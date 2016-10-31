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

module TensorOps.Learn.NeuralNet.FeedForward
  ( Network(..)
  , buildNet
  , runNetwork
  , trainNetwork
  , induceNetwork
  , nmap
  , (~*)
  , (*~)
  , liftNet
  , netParams
  , networkGradient
  , genNet
  , ffLayer
  ) where

import           Control.Category
import           Control.DeepSeq
import           Control.Monad.Primitive
import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude        (Sing(..))
import           Data.Type.Conjunction
import           Data.Type.Length
import           Data.Type.Product              as TCP
import           Data.Type.Product.Util         as TCP
import           Data.Type.Sing
import           Prelude hiding                 ((.), id)
import           Statistics.Distribution.Normal
import           System.Random.MWC
import           TensorOps.Learn.NeuralNet
import           TensorOps.NatKind
import           TensorOps.TOp                  as TO
import           TensorOps.Tensor               as TT
import           TensorOps.Types
import           Type.Class.Higher
import           Type.Class.Higher.Util
import           Type.Class.Known
import           Type.Class.Witness
import           Type.Family.List
import           Type.Family.List.Util

data Network :: ([k] -> Type) -> k -> k -> Type where
    N :: { _nsPs    :: !(Sing ps)
         , _nOp     :: !(TOp ('[i] ': ps) '[ '[o] ])
         , _nParams :: !(Prod t ps)
         } -> Network t i o

instance NFData1 t => NFData (Network t i o) where
    rnf = \case
      N _ o p -> o `seq` p `deepseq1` ()
    {-# INLINE rnf #-}

buildNet
    :: SingI ps
    => TOp ('[i] ': ps) '[ '[o] ]
    -> Prod t ps
    -> Network t i o
buildNet = N sing

netParams
    :: Network t i o
    -> (forall ps. SingI ps => Prod t ps -> r)
    -> r
netParams n f = case n of
    N o _ p -> f p \\ o

(~*~)
    :: Network t a b
    -> Network t b c
    -> Network t a c
N sPs1 o1 p1 ~*~ N sPs2 o2 p2 =
    N (sPs1 %:++ sPs2) (o1 *>> o2) (p1 `TCP.append'` p2)
        \\ singLength sPs1
infixr 4 ~*~
{-# INLINE (~*~) #-}

instance Category (Network t) where
    id = N SNil idOp Ø
    (.) = flip (~*~)

(~*) :: TOp '[ '[a] ] '[ '[b] ]
     -> Network t b c
     -> Network t a c
f ~* N sO o p = N sO (f *>> o) p
infixr 4 ~*
{-# INLINE (~*) #-}

(*~) :: Network t a b
     -> TOp '[ '[b] ] '[ '[c] ]
     -> Network t a c
N sO o p *~ f = N sO (o >>> f) p
infixl 5 *~
{-# INLINE (*~) #-}

liftNet
     :: TOp '[ '[i] ] '[ '[o] ]
     -> Network t i o
liftNet o = buildNet o Ø

nmap
     :: SingI o
     => (forall a. RealFloat a => a -> a)
     -> Network t i o
     -> Network t i o
nmap f n = n *~ TO.map f
{-# INLINE nmap #-}

runNetwork
    :: (RealFloat (ElemT t), Tensor t)
    => Network t i o
    -> t '[i]
    -> t '[o]
runNetwork (N _ o p) = head' . runTOp o . (:< p)
{-# INLINE runNetwork #-}

trainNetwork
    :: forall i o t. (Tensor t, RealFloat (ElemT t))
    => TOp '[ '[o], '[o] ] '[ '[] ]
    -> ElemT t
    -> t '[i]
    -> t '[o]
    -> Network t i o
    -> Network t i o
trainNetwork loss r x y = \case
    N s o p ->
      let p' = map1 (\(s1 :&: o1 :&: g1) -> TT.zip stepFunc o1 g1 \\ s1)
             $ zipProd3 (singProd s) p (tail' $ netGrad loss x y s o p)
      in  N s o p'
  where
    stepFunc :: ElemT t -> ElemT t -> ElemT t
    stepFunc o' g' = o' - r * g'
    {-# INLINE stepFunc #-}
{-# INLINE trainNetwork #-}

induceNetwork
    :: forall i o t. (Tensor t, RealFloat (ElemT t), SingI i)
    => TOp '[ '[o], '[o] ] '[ '[] ]
    -> ElemT t
    -> t '[o]
    -> Network t i o
    -> t '[i]
    -> t '[i]
induceNetwork loss r y = \case
    N s o p -> \x -> TT.zip stepFunc x (head' $ netGrad loss x y s o p)
  where
    stepFunc :: ElemT t -> ElemT t -> ElemT t
    stepFunc o' g' = o' - r * g'
    {-# INLINE stepFunc #-}
{-# INLINE induceNetwork #-}

networkGradient
    :: forall i o t r. (Tensor t, RealFloat (ElemT t))
    => TOp '[ '[o], '[o] ] '[ '[] ]
    -> t '[i]
    -> t '[o]
    -> Network t i o
    -> (forall ps. SingI ps => Prod t ps -> r)
    -> r
networkGradient loss x y = \case
    N s o p -> \f -> f (tail' $ netGrad loss x y s o p) \\ s
{-# INLINE networkGradient #-}

netGrad
    :: forall i o ps t. (Tensor t, RealFloat (ElemT t))
    => TOp '[ '[o], '[o] ] '[ '[] ]
    -> t '[i]
    -> t '[o]
    -> Sing ps
    -> TOp ('[i] ': ps) '[ '[o] ]
    -> Prod t ps
    -> Prod t ('[i] ': ps)
netGrad loss x y s o p = (\\ appendSnoc lO (Proxy @'[o])) $
                         (\\ lO                         ) $
                         takeProd @'[ '[o] ] (LS lO)
                       $ gradTOp o' inp
  where
    lO  :: Length ps
    lO = singLength s
    o'  :: ((ps ++ '[ '[o] ]) ~ (ps >: '[o]), Known Length ps)
        => TOp ('[i] ': ps >: '[o]) '[ '[]]
    o' = o *>> loss
    inp  :: Prod t ('[i] ': ps >: '[o])
    inp = x :< p >: y
{-# INLINE netGrad #-}

ffLayer
    :: forall i o m t. (SingI i, SingI o, PrimMonad m, Tensor t)
    => Gen (PrimState m)
    -> m (Network t i o)
ffLayer g = (\w b -> buildNet ffLayer' (w :< b :< Ø))
          <$> genRand (normalDistr 0 0.5) g
          <*> genRand (normalDistr 0 0.5) g
  where
    ffLayer'
        :: TOp '[ '[i], '[o,i], '[o]] '[ '[o] ]
    ffLayer' = firstOp (TO.swap >>> TO.matVec)
           >>> TO.add
    {-# INLINE ffLayer' #-}
{-# INLINE ffLayer #-}

genNet
    :: forall k o i m (t :: [k] -> Type). (SingI o, SingI i, PrimMonad m, Tensor t)
    => [(Integer, Activation k)]
    -> Activation k
    -> Gen (PrimState m)
    -> m (Network t i o)
genNet xs0 f g = go sing xs0
  where
    go  :: forall (j :: k). ()
        => Sing j
        -> [(Integer, Activation k)]
        -> m (Network t j o)
    go sj = (\\ sj) $ \case
      []        -> (*~ getAct f) <$> ffLayer g
      (x,f'):xs -> withNatKind x $ \sl -> (\\ sl) $ do
        n <- go sl xs
        l <- ffLayer g
        return $ l *~ getAct f' ~*~ n
    {-# INLINE go #-}
{-# INLINE genNet #-}

