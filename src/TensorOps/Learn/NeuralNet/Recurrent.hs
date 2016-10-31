{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module TensorOps.Learn.NeuralNet.Recurrent
  ( Network
  , buildNet
  , netParams
  , runNetwork
  , runNetworkSt
  , genNet
  , fullyConnected
  , ffLayer
  , stateless
  , (~*~)
  , (*~)
  , (~*)
  , nmap
  , trainNetwork
  , trainNetwork'
  , networkGradient
  ) where

import           Control.Category
import           Control.DeepSeq
import           Control.Monad.Primitive
import           Control.Monad.State
import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude               (Sing(..))
import           Data.Type.Combinator
import           Data.Type.Conjunction
import           Data.Type.Length                      as TCL
import           Data.Type.Length.Util                 as TCL
import           Data.Type.Nat
import           Data.Type.Product                     as TCP
import           Data.Type.Product.Util                as TCP
import           Data.Type.Sing
import           Data.Type.Uniform
import           Data.Type.Vector                      as TCV
import           Data.Type.Vector.Util                 as TCV
import           Prelude hiding                        ((.), id)
import           Statistics.Distribution.Normal
import           System.Random.MWC
import           TensorOps.Learn.NeuralNet
import           TensorOps.NatKind
import           TensorOps.TOp                         as TO
import           TensorOps.Tensor                      as TT
import           TensorOps.Types
import           Type.Class.Higher
import           Type.Class.Higher.Util
import           Type.Class.Known
import           Type.Class.Witness
import           Type.Family.List
import           Type.Family.List.Util
import           Type.Family.Nat
import           Unsafe.Coerce
import qualified TensorOps.Learn.NeuralNet.FeedForward as FF

data Network :: ([k] -> Type) -> k -> k -> Type where
    N :: { _nsSs    :: !(Sing ss)
         , _nsPs    :: !(Sing ps)
         , _nOp     :: !(TOp ('[i] ': ss ++ ps) ('[o] ': ss))
         , _nState  :: !(Prod t ss)
         , _nParams :: !(Prod t ps)
         } -> Network t i o

instance NFData1 t => NFData (Network t i o) where
    rnf = \case
      N _ _ o p s -> o `seq` p `deepseq1` s `deepseq1` ()
    {-# INLINE rnf #-}

netParams
    :: Network t i o
    -> (forall ss ps. (SingI ss, SingI ps) => Prod t ss -> Prod t ps -> r)
    -> r
netParams = \case
    N sS sP _ s p -> \f -> f s p \\ sS \\ sP

buildNet
    :: forall ss ps i o t. (SingI ss, SingI ps)
    => TOp ('[i] ': ss ++ ps) ('[o] ': ss)  -- ^ Tensor operation for network
    -> Prod t ss        -- ^ Initial states
    -> Prod t ps        -- ^ Network parameters
    -> Network t i o
buildNet = N sing sing

fullyConnected
    :: forall k (i :: k) (o :: k) (m :: Type -> Type) (t :: [k] -> Type).
     ( SingI i
     , SingI o
     , PrimMonad m
     , Tensor t
     )
    => Activation k         -- ^ Activation function for internal state
    -> Gen (PrimState m)
    -> m (Network t i o)
fullyConnected a g = (\s w w' b -> buildNet @'[ '[o] ] @'[ '[o,o], '[o,i], '[o] ]
                                     fc (s :< Ø) (w' :< w :< b :< Ø)
                     )
          <$> genRand (normalDistr 0 0.5) g
          <*> genRand (normalDistr 0 0.5) g
          <*> genRand (normalDistr 0 0.5) g
          <*> genRand (normalDistr 0 0.5) g
  where
    fc  :: TOp '[ '[i], '[o], [o,o], '[o,i], '[o]] '[ '[o], '[o] ]
    fc = secondOp @'[ '[i] ] (
           firstOp @'[ '[o,i], '[o] ] (TO.swap >>> TO.matVec)
       >>> firstOp @'[ '[o] ]         TO.swap
         )
     >>> firstOp @'[ '[o], '[o] ] (TO.swap >>> TO.matVec)
     >>> TO.add3
     >>> TO.duplicate
     >>> secondOp @'[ '[o] ] (getAct a)
    {-# INLINE fc #-}
{-# INLINE fullyConnected #-}

-- | Convert a neural network from "TensorOps.Learn.NeuralNet.FeedForward"
-- to a stateless 'Network'.
--
-- Can be thought a functor from the category of stateless neural networks
-- to the category of stateful (recurrent) ones.
stateless
    :: FF.Network t i o
    -> Network t i o
stateless = \case
    FF.N sP o p -> N SNil sP o Ø p
{-# INLINE stateless #-}

ffLayer
    :: forall i o m t. (SingI i, SingI o, PrimMonad m, Tensor t)
    => Gen (PrimState m)
    -> m (Network t i o)
ffLayer g = stateless <$> FF.ffLayer g
{-# INLINE ffLayer #-}

genNet
    :: forall k o i m (t :: [k] -> Type). (SingI o, SingI i, PrimMonad m, Tensor t)
    => [(Integer, (Activation k, Maybe (Activation k)))]
    -> Activation k
    -> Maybe (Activation k)
    -> Gen (PrimState m)
    -> m (Network t i o)
genNet xs0 f fS g = go sing xs0
  where
    go  :: forall (j :: k). ()
        => Sing j
        -> [(Integer, (Activation k, Maybe (Activation k)))]
        -> m (Network t j o)
    go sj = (\\ sj) $ \case
      []        -> fmap (*~ getAct f) $ case fS of
        Just fS' -> fullyConnected fS' g
        Nothing  -> ffLayer g
      (x,(f', fS')):xs -> withNatKind x $ \sl -> (\\ sl) $ do
        n <- go sl xs
        l <- case fS' of
          Nothing   -> ffLayer g
          Just fS'' -> fullyConnected fS'' g
        return $ l *~ getAct f' ~*~ n
    {-# INLINE go #-}
{-# INLINE genNet #-}

instance Category (Network t) where
    id  = N SNil SNil idOp Ø Ø
    (.) = flip (~*~)

(~*~)
    :: forall k (t :: [k] -> Type) a b c. ()
    => Network t a b
    -> Network t b c
    -> Network t a c
(~*~) = \case
  N (sSs1 :: Sing ss1)
    (sPs1 :: Sing ps1)
    (o1   :: TOp ('[a] ': ss1 ++ ps1) ('[b] ': ss1))
    (s1   :: Prod t ss1)
    (p1   :: Prod t ps1) -> \case
    N (sSs2 :: Sing ss2)
      (sPs2 :: Sing ps2)
      (o2   :: TOp ('[b] ': ss2 ++ ps2) ('[c] ': ss2))
      (s2   :: Prod t ss2)
      (p2   :: Prod t ps2) ->
      let lSs1 :: Length ss1
          lSs1 = singLength sSs1
          lSs2 :: Length ss2
          lSs2 = singLength sSs2
          lPs1 :: Length ps1
          lPs1 = singLength sPs1
          lPs2 :: Length ps2
          lPs2 = singLength sPs2
          o :: TOp ('[a] ': (ss2 ++ ss1) ++ (ps1 ++ ps2)) ('[c] ': ss2 ++ ss1)
                    -- all these proofs lol
          o     = (\\ (unsafeCoerce Refl :: ((ss2 ++ ss1) ++ ps1) ++ ps2 :~: (ss2 ++ ss1) ++ (ps1 ++ ps2))) $
                  (\\ (unsafeCoerce Refl :: ((ss1 ++ ps1) ++ ss2) ++ ps2 :~: (ss1 ++ ps1) ++ (ss2 ++ ps2))) $
                  (\\ appendAssoc lSs1 lSs2 lPs2                  ) $
                  (\\ appendAssoc lSs2 lSs1 lPs1                  ) $
                  (\\ (lSs2 `TCL.append'` lSs1) `TCL.append'` lPs1) $
                  (\\ (lSs1 `TCL.append'` lPs1) `TCL.append'` lSs2) $
                  (\\ lSs1                                        ) $
                  (\\ lSs2                                        ) $
                  (\\ lSs1 `TCL.append'` lPs1                     ) $
                  (\\ lSs2 `TCL.append'` lPs2                     ) $
                    secondOp @'[ '[a] ]
                      (firstOp @ps2 (TO.swap' lSs2 (lSs1 `TCL.append'` lPs1))
                      )
                >>> firstOp @(ss2 ++ ps2) o1
                >>> secondOp @'[ '[b] ] (TO.swap' lSs1 (lSs2 `TCL.append'` lPs2))
                >>> firstOp @ss1 o2
      in  N (sSs2 %:++ sSs1)
            (sPs1 %:++ sPs2)
            o
            (s2 `TCP.append'` s1)
            (p1 `TCP.append'` p2)
infixr 4 ~*~
{-# INLINE (~*~) #-}

runNetwork
    :: (RealFloat (ElemT t), Tensor t)
    => Network t i o
    -> t '[i]
    -> (t '[o], Network t i o)
runNetwork (N sS sO o s p) x =
        (\case y :< s' -> (y, N sS sO o s' p))
      . runTOp o
      $ x :< (s `TCP.append'` p)
{-# INLINE runNetwork #-}

runNetworkSt
    :: (RealFloat (ElemT t), Tensor t, MonadState (Network t i o) m)
    => t '[i]
    -> m (t '[o])
runNetworkSt x = state $ flip runNetwork x

(~*) :: TOp '[ '[a] ] '[ '[b] ]
     -> Network t b c
     -> Network t a c
f ~* N sS sO o s p = N sS sO (f *>> o) s p
infixr 4 ~*
{-# INLINE (~*) #-}

(*~) :: Network t a b
     -> TOp '[ '[b] ] '[ '[c] ]
     -> Network t a c
N sS sO o s p *~ f = N sS sO (o >>> firstOp f) s p
infixl 5 *~
{-# INLINE (*~) #-}

nmap
     :: SingI o
     => (forall a. RealFloat a => a -> a)
     -> Network t i o
     -> Network t i o
nmap f n = n *~ TO.map f
{-# INLINE nmap #-}

netGrad
    :: forall k n (t :: [k] -> Type) (i :: k) (o :: k) ss ps.
     ( Tensor t
     , RealFloat (ElemT t)
     , SingI i
     , SingI o
     )
    => TOp '[ '[o], '[o] ] '[ '[] ]
    -> Vec n (t '[i])
    -> Vec n (t '[o])
    -> Sing ss
    -> Sing ps
    -> TOp ('[i] ': ss ++ ps) ('[o] ': ss)
    -> Prod t ss
    -> Prod t ps
    -> (Vec n (t '[i]), (Prod t ss, Prod t ps))
netGrad loss xs ys sS sP o s p =
      (prodToVec' I n grI, splitProd @ps lS grSP)
  where
    n :: Nat n
    n = known   \\ xs
    lS :: Length ss
    lS = singLength sS
    lP :: Length ps
    lP = singLength sP
    sO :: Sing (Replicate n '[o])
    sO = replicateSing (sing :: Sing '[o]) n
    lI :: Length (Replicate n '[i])
    lI = replicateLength @'[i] n
    lO :: Length (Replicate n '[o])
    lO = replicateLength @'[o] n
    unrolled
        :: TOp (Replicate n '[i] ++ ss ++ ps) (Replicate n '[o])
    unrolled = (\\ sS %:++ sO) $
               (\\ sS %:++ sP) $
                 unroll sS sP o n
             >>> TO.drop @(Replicate n '[o]) lS
    o'  :: TOp (Replicate n '[i] ++ ss ++ ps ++ Replicate n '[o]) '[ '[] ]
    o' = (\\ appendAssoc lI (lS `TCL.append'` lP) lO) $
         (\\ appendAssoc lS lP lO) $
         (\\ lI `TCL.append'` lS `TCL.append'` lP) $
         (\\ lO) $
            firstOp @(Replicate n '[o]) unrolled
        >>> rollup @k lS lP loss n
    xs' :: Prod t (Replicate n '[i] ++ ss ++ ps ++ Replicate n '[o])
    xs' = vecToProd' getI (TCV.reverse' xs) `TCP.append'` (s
            `TCP.append'` (
              p `TCP.append'` vecToProd' getI ys
            )
          )
    grad :: Prod t (Replicate n '[i] ++ ss ++ ps)
    grad = (\\ (unsafeCoerce Refl :: Replicate n '[i] ++ ss ++ ps ++ Replicate n '[o]
                                 :~: (Replicate n '[i] ++ ss ++ ps) ++ Replicate n '[o]
               )
           ) $
      takeProd @(Replicate n '[o]) (lI `TCL.append'` lS `TCL.append'` lP) $ gradTOp o' xs'
    grI   :: Prod t (Replicate n '[i])
    grSP  :: Prod t (ss ++ ps)
    (grI, grSP) = splitProd @(ss ++ ps) lI grad
{-# INLINE netGrad #-}

trainNetwork'
    :: forall k n (t :: [k] -> Type) (i :: k) (o :: k).
     ( Tensor t
     , RealFloat (ElemT t)
     , SingI i
     , SingI o
     )
    => TOp '[ '[o], '[o] ] '[ '[] ]     -- ^ loss function (input, target)
    -> ElemT t          -- ^ train rate for initial state
    -> ElemT t          -- ^ train rate for network parameters
    -> Vec n (t '[i])   -- ^ inputs
    -> Vec n (t '[o])   -- ^ targets
    -> Network t i o
    -> Network t i o
trainNetwork' loss rS rP xs ys = \case
    N sS sP o s p ->
      let (gS, gP) = snd $ netGrad loss xs ys sS sP o s p
          s' = map1 (f rS) $ zipProd3 (singProd sS) s gS
          p' = map1 (f rP) $ zipProd3 (singProd sP) p gP
      in  N sS sP o s' p'
  where
    f   :: forall ns. ()
        => ElemT t
        -> (Sing :&: t :&: t) ns
        -> t ns
    f r (s1 :&: p1 :&: g1) =
      TT.zip (\p2 g2 -> p2 - r * g2) p1 g1 \\ s1
    {-# INLINE f #-}
{-# INLINE trainNetwork #-}

trainNetwork
    :: forall k (t :: [k] -> Type) (i :: k) (o :: k).
     ( Tensor t
     , RealFloat (ElemT t)
     , SingI i
     , SingI o
     )
    => TOp '[ '[o], '[o] ] '[ '[] ]     -- ^ loss function (input, target)
    -> ElemT t          -- ^ train rate for initial state
    -> ElemT t          -- ^ train rate for network parameters
    -> [(t '[i], t '[o])]   -- ^ inputs and targets
    -> Network t i o
    -> Network t i o
trainNetwork loss rS rP xsys n = withV xsys $ \v ->
    let (xs, ys) = TCV.unzip' v
    in  trainNetwork' loss rS rP xs ys n

networkGradient
    :: forall k n (t :: [k] -> Type) (i :: k) (o :: k) r.
     ( Tensor t
     , RealFloat (ElemT t)
     , SingI i
     , SingI o
     )
    => TOp '[ '[o], '[o] ] '[ '[] ]     -- ^ loss function (output, target)
    -> Vec n (t '[i])       -- ^ inputs
    -> Vec n (t '[o])       -- ^ targets
    -> Network t i o
    -> (forall ss ps. (SingI ss, SingI ps) => Vec n (t '[i]) -> Prod t ss -> Prod t ps -> r)
    -> r
networkGradient loss xs ys = \case
    N sS sP o s p -> \f -> case netGrad loss xs ys sS sP o s p of
      (gI, (gS, gP)) -> f gI gS gP \\ sS \\ sP
{-# INLINE networkGradient #-}


unroll
    :: forall ss ps i o n. (SingI (ss ++ ps), SingI i)
    => Sing ss
    -> Sing ps
    -> TOp ('[i] ': ss ++ ps) ('[o] ': ss)
    -> Nat n
    -> TOp (Replicate n '[i] ++ ss ++ ps) (ss ++ Replicate n '[o])
unroll sS sP o = \case
    Z_              -> TO.take lS lP    \\ appendNil lS
    S_ (m :: Nat m) -> (\\ (unsafeCoerce Refl :: Replicate m '[i] ++ '[i] ': ss ++ ps
                                             :~: '[i] ': Replicate m '[i] ++ ss ++ ps
                           )
                       ) $
                       (\\ (unsafeCoerce Refl :: (Replicate m '[i] ++ ss ++ ps) ++ '[ '[o] ]
                                             :~: Replicate m '[i] ++ ss ++ (ps >: '[o])
                           )
                       ) $
                       (\\ (unsafeCoerce Refl :: (ss ++ Replicate m '[o]) ++ '[ '[o] ]
                                             :~: ss ++ '[o] ': Replicate m '[o]
                           )
                       ) $
                       (\\ appendAssoc lS lP (LS LZ :: Length '[ '[o] ])) $
                       (\\ appendSnoc lP (Proxy @'[o])) $
                       (\\ replicateLength @'[i] m `TCL.append'` lS `TCL.append'` lP) $
                       (\\ lS `TCL.append'` replicateLength @'[o] m) $
                       (\\ replicateLength @'[i] m) $
                       (\\ lS) $
          secondOp @(Replicate m '[i]) @('[i] ': ss ++ ps) @(ss ++ ps >: '[o]) (
                (o &&& TO.drop @ps @('[i] ': ss) (LS lS))
            >>> TO.swap' (LS LZ) (lS `TCL.append'` lP)
          )
      >>> firstOp @'[ '[o] ] @(Replicate m '[i] ++ ss ++ ps) @(ss ++ Replicate m '[o]) (
            unroll sS sP o m
          )
  where
    lS :: Length ss
    lS = singLength sS
    lP :: Length ps
    lP = singLength sP
{-# INLINE unroll #-}


rollup
    :: forall k (ss :: [[k]]) (ps :: [[k]]) (o :: k) (n :: N). ()
    => Length ss
    -> Length ps
    -> TOp '[ '[o], '[o] ] '[ '[] ]
    -> Nat n
    -> TOp (Replicate n '[o] ++ Replicate n '[o]) '[ '[] ]
rollup lS lP loss = \case
    Z_                     -> TO.konst (US UØ) 0
    S_ Z_                  -> loss
    S_ (m@(S_ _) :: Nat m) ->
      let lO :: Length (Replicate m '[o])
          lO = replicateLength @'[o] m
      in  (\\ (unsafeCoerce Refl :: Replicate m '[o] ++ '[o] ': '[o] ': Replicate m '[o]
                                :~: '[o] ': Replicate m '[o] ++ '[o] ': Replicate m '[o]
              )
            ) $
            (\\ appendSnoc lO (Proxy @'[])) $
            (\\ lO) $
            (\\ lO `TCL.append'` lO) $
            (\\ appendAssoc lO lO (LS LZ :: Length '[ '[] ])) $
              secondOp @(Replicate m '[o]) @('[o] ': '[o] ': Replicate m '[o]) @(Replicate m '[o] >: '[]) (
                  firstOp @(Replicate m '[o]) @('[ '[o], '[o] ]) @('[ '[] ]) loss
                >>> TO.swap' @'[ '[] ] @(Replicate m '[o]) (LS LZ) lO
              )
            >>> firstOp @'[ '[] ] @(Replicate m '[o] ++ Replicate m '[o]) @'[ '[] ] (
                  rollup lS lP loss m
                )
            >>> TO.add
{-# INLINE rollup #-}
