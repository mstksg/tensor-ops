{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module TensorOps.Model.NeuralNet.FeedForward where

import           Control.DeepSeq
import           Control.Monad.Primitive
import           Data.Kind
import           Data.Nested
import           Data.Singletons
import           Data.Singletons.Prelude hiding ((%:++))
import           Data.Type.Conjunction
import           Data.Type.Index
import           Data.Type.Length
import           Data.Type.Product              as TCP
import           Data.Type.Product.Util         as TCP
import           Data.Type.Sing
import           Data.Type.Uniform
import           Statistics.Distribution.Normal
import           System.Random.MWC
import           TensorOps.Gradient
import           TensorOps.NatKind
import           TensorOps.Run
import           TensorOps.TOp                  as TO
import           TensorOps.Tensor               as TT
import           TensorOps.Types
import           Type.Class.Higher
import           Type.Class.Witness
import           Type.Family.List
import           Type.Family.List.Util

data Network :: ([k] -> Type) -> k -> k -> Type where
    N :: { _nsOs    :: !(Sing os)
         , _nOp     :: !(TensorOp ('[i] ': os) '[ '[o] ])
         , _nParams :: !(Prod t os)
         } -> Network t i o

instance Nesting1 Proxy NFData t => NFData (Network t i o) where
    rnf = \case
      N (s :: Sing os) _ p
        -> p `deepseq` ()
             \\ (nesting1Every (Proxy @t) (map1 (\_ -> Proxy) (singProd s))
                    :: Wit (Every NFData (t <$> os))
                )

(~*~)
    :: (SingI a, SingI b)
    => Network t a b
    -> Network t b c
    -> Network t a c
N sOs1 o1 p1 ~*~ N sOs2 o2 p2 =
    N (sOs1 %:++ sOs2)
      (pappend (sing `SCons` sOs1) sing sOs2 o1 o2)
      (p1 `TCP.append'` p2)
infixr 4 ~*~

(~*) :: (SingI a, SingI b)
     => TensorOp '[ '[a] ] '[ '[b] ]
     -> Network t b c
     -> Network t a c
f ~* N sO o p = N sO (pappend sing sing sO f o) p
infixr 4 ~*

(*~) :: (SingI a, SingI b)
     => Network t a b
     -> TensorOp '[ '[b] ] '[ '[c] ]
     -> Network t a c
N sO o p *~ f = N sO (pappend (sing `SCons` sO) sing SNil o f) p
                  \\ appendNil (singLength sO)
infixl 5 *~

nmap
     :: (SingI o, SingI i)
     => (forall a. Floating a => a -> a)
     -> Network t i o
     -> Network t i o
nmap f n = n *~ pipe (TO.map f)

runNetwork
    :: (Floating (ElemT t), Tensor t)
    => Network t i o
    -> t '[i]
    -> t '[o]
runNetwork (N _ o p) = head' . runTensorOp o . (:< p)

trainNetwork
    :: forall i o t. (SingI i, SingI o, Tensor t, Floating (ElemT t))
    => ElemT t
    -> t '[i]
    -> t '[o]
    -> Network t i o
    -> Network t i o
trainNetwork r x y = \case
    N (s :: Sing os) (o :: TensorOp ('[i] ': os) '[ '[o]]) (p :: Prod t os) ->
      ( let o'   :: TensorOp ('[i] ': os >: '[o]) '[ '[]]
            o' = pappend (sing `SCons` s) sing sing o squaredError
            inp  :: Prod t ('[i] ': os >: '[o])
            inp = x :< p >: y
            grad :: Prod t os
            grad = takeProd (singLength s) (LS LZ :: Length '[ '[o]])
                 . tail'
                 $ gradTensorOp o' inp
            p'   :: Prod t os
            p' = map1 (\(s1 :&: o1 :&: g1) -> withSingI s1 $ TT.zip2 stepFunc o1 g1)
               $ zipProd3 (singProd s) p grad
        in  N s o p'
      ) \\ appendSnoc (singLength s) (Proxy @('[o]))
  where
    stepFunc :: ElemT t -> ElemT t -> ElemT t
    stepFunc o' g' = o' - r * g'

squaredError
    :: forall o. SingI o
    => TensorOp '[ '[o], '[o]] '[ '[] ]
squaredError = (LS (LS LZ), LZ   , TO.zip2      (-)         )
            ~. (LS LZ     , LZ   , TO.replicate (US (US UØ)))
            ~. (LS (LS LZ), LZ   , TO.dot                   )
            ~. OPØ

ffLayer
    :: forall i o m t. (SingI i, SingI o, PrimMonad m, Tensor t)
    => Gen (PrimState m)
    -> m (Network t i o)
ffLayer g = (\w b -> N sing ffLayer' (w :< b :< Ø))
        <$> genRand (normalDistr 0 0.5) g
        <*> genRand (normalDistr 0 0.5) g
  where
    ffLayer'
        :: TensorOp '[ '[i], '[o,i], '[o]] '[ '[o] ]
    ffLayer' = (LS (LS LZ), LS LZ, TO.swap                   )
            ~. (LS (LS LZ), LS LZ, GMul    (LS LZ) (LS LZ) LZ)
            ~. (LS (LS LZ), LZ   , TO.zip2 (+)               )
            ~. OPØ

genNet
    :: forall k o i m (t :: [k] -> Type). (SingI o, SingI i, PrimMonad m, Tensor t)
    => (forall a. Floating a => a -> a)
    -> [Integer]
    -> Gen (PrimState m)
    -> m (Network t i o)
genNet f xs0 g = go sing xs0
  where
    go  :: forall (j :: k). ()
        => Sing j
        -> [Integer]
        -> m (Network t j o)
    go sj = \case
      []   -> ffLayer g       \\ sj
      x:xs -> withNatKind x $ \sl -> do
        n <- go sl xs
        l <- ffLayer g  \\ sl \\ sj
        return $ l ~*~ pipe (TO.map f) ~* n  \\ sl \\ sj
