{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE IncoherentInstances        #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeInType                 #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ViewPatterns               #-}

module TensorOps.Backend.LTensor
  ( LTensor
  ) where

-- import           Control.Monad.Trans.Maybe
-- import           Control.Monad.Trans.State.Strict
-- import           Data.List hiding                 ((\\))
-- import           Data.Singletons.Prelude.List     (sHead,Sing(..))
-- import           Type.Class.Higher
-- import qualified TensorOps.Tensor                 as Tensor
import           Control.Applicative
import           Control.Monad.Primitive
import           Data.Kind
import           Data.Singletons
import           Data.Type.Combinator
import           Data.Type.Fin
import           Data.Type.Index
import           Data.Type.Length
import           Data.Type.Length.Util               as TCL
import           Data.Type.Nat
import           Data.Type.Product                   as TCP
import           Data.Type.Product.Util              as TCP
import           Data.Type.Sing
import           Data.Type.Uniform
import           Data.Type.Vector                    as TCV
import           Data.Type.Vector.Util
import           Statistics.Distribution
import           System.Random.MWC
import           TensorOps.Types
import           Type.Class.Known
import           Type.Class.Witness
import           Type.Family.List
import           Type.Family.List.Util
import           Type.Family.Nat

data NestedVec :: [N] -> Type -> Type where
    NVZ :: !a -> NestedVec '[]  a
    NVS :: !(VecT n (NestedVec ns) a) -> NestedVec (n ': ns) a

deriving instance Show a => Show (NestedVec ns a)
deriving instance Functor (NestedVec ns)
deriving instance Foldable (NestedVec ns)
deriving instance Traversable (NestedVec ns)
instance Known (Prod Nat) ns => Applicative (NestedVec ns) where
    pure x = case known :: Length ns of
               LZ   -> NVZ x
               LS _ -> NVS $ vgen_ (\_ -> pure x)
    (<*>) = \case
      NVZ f -> \case
        NVZ x -> NVZ (f x)
      NVS fs -> \case
        NVS xs -> NVS $ vap (<*>) fs xs

instance (Num a, Applicative (NestedVec ns)) => Num (NestedVec ns a) where
    (+)         = liftA2 (+)
    (-)         = liftA2 (-)
    (*)         = liftA2 (*)
    negate      = fmap negate
    abs         = fmap abs
    signum      = fmap signum
    fromInteger = pure . fromInteger

instance (Fractional a, Applicative (NestedVec ns)) => Fractional (NestedVec ns a) where
    (/)          = liftA2 (/)
    recip        = fmap recip
    fromRational = pure . fromRational

nvHead
    :: NestedVec ('S m ': ms) a
    -> NestedVec ms a
nvHead = \case
    NVS xs -> TCV.head' xs

nvTail
    :: NestedVec ('S m ': ms) a
    -> NestedVec (m ': ms) a
nvTail = \case
    NVS xs -> NVS $ TCV.tail' xs

nvToMatrix
    :: NestedVec ns a
    -> Matrix ns a
nvToMatrix = \case
    NVZ x  -> I x
    NVS xs -> nvToMatrix `vmap` xs

matrixToNV
    :: Length ns
    -> Matrix ns a
    -> NestedVec ns a
matrixToNV = \case
    LZ   -> \case
      I x -> NVZ x
    LS l -> \case
      xs  -> NVS $ matrixToNV l `vmap` xs

sumNVec
    :: (Num a, Known (Prod Nat) ns)
    => NestedVec (n ': ns) a
    -> NestedVec ns a
sumNVec = \case
    NVS xs -> sum $ vmap I xs

mapNVecSlices
    :: (NestedVec ms a -> b)
    -> Length ns
    -> NestedVec (ns ++ ms) a
    -> NestedVec ns b
mapNVecSlices f = \case
    LZ -> NVZ . f
    LS l -> \case
      NVS xs -> NVS $ mapNVecSlices f l `vmap` xs

frontSlices
    :: Applicative f
    => (NestedVec ns a -> f b)
    -> Length ns
    -> NestedVec (ns ++ ms) a
    -> f (NestedVec ms b)
frontSlices f = \case
    LZ -> \case
      NVZ x  -> NVZ <$> f (NVZ x)
      NVS xs -> NVS . vmap getI <$> sequenceA (vmap (I . frontSlices f LZ) xs)
    LS _ -> error "wait why"

imapNestedVec
    :: (Prod Fin ns -> a -> b)
    -> NestedVec ns a
    -> NestedVec ns b
imapNestedVec f = \case
    NVZ x  -> NVZ (f Ø x)
    NVS xs -> NVS $ TCV.imap (\i -> imapNestedVec (\is -> f (i :< is))) xs

itraverseNestedVec
    :: Applicative f
    => (Prod Fin ns -> a -> f b)
    -> NestedVec ns a
    -> f (NestedVec ns b)
itraverseNestedVec f = \case
    NVZ x  -> NVZ <$> f Ø x
    NVS xs -> NVS <$> TCV.itraverse (\i -> itraverseNestedVec (\is -> f (i :< is))) xs


joinNestedVec
    :: NestedVec ns (NestedVec ms a)
    -> NestedVec (ns ++ ms) a
joinNestedVec = \case
    NVZ x  -> x
    NVS xs -> NVS $ vmap joinNestedVec xs

-- unjoinNestedVec
--     :: Length ns
--     -> NestedVec (ns ++ ms) a
--     -> NestedVec

imapNVecSlices
    :: (Prod Fin ns -> NestedVec ms a -> b)
    -> Length ns
    -> NestedVec (ns ++ ms) a
    -> NestedVec ns b
imapNVecSlices f = \case
    LZ -> NVZ . f Ø
    LS l -> \case
      NVS xs -> NVS $ TCV.imap (\i -> imapNVecSlices (\is -> f (i :< is)) l) xs

genNestedVec
    :: Prod Nat ns
    -> (Prod Fin ns -> a)
    -> NestedVec ns a
genNestedVec = \case
    Ø       -> \f -> NVZ (f Ø)
    n :< ns -> \f -> NVS . vgen n $ \i -> genNestedVec ns (f . (i :<))

genNestedVecA
    :: Applicative f
    => Prod Nat ns
    -> (Prod Fin ns -> f a)
    -> f (NestedVec ns a)
genNestedVecA = \case
    Ø       -> \f -> NVZ <$> f Ø
    n :< ns -> \f -> NVS <$> vgenA n (\i -> genNestedVecA ns (f . (i :<)))

indexNestedVec
    :: Prod Fin ns
    -> NestedVec ns a
    -> a
indexNestedVec = \case
    Ø -> \case
      NVZ x  -> x
    i :< is -> \case
      NVS xs -> indexNestedVec is (TCV.index i xs)

innerNV
    :: forall ns o ms a. (Num a, Known (Prod Nat) ms)
    => Length ns
    -> Length ms
    -> NestedVec (ns >: o) a
    -> NestedVec (o ': ms) a
    -> NestedVec (ns ++ ms) a
innerNV lN lM x y = joinNestedVec $ innerNV' lN lM x y

innerNV'
    :: forall ns o ms a. (Num a, Known (Prod Nat) ms)
    => Length ns
    -> Length ms
    -> NestedVec (ns >: o) a
    -> NestedVec (o ': ms) a
    -> NestedVec ns (NestedVec ms a)
innerNV' lN _ x y = mapNVecSlices rowMat lN x
                       \\ appendSnoc lN (Proxy :: Proxy o)
  where
    rowMat :: NestedVec '[o] a -> NestedVec ms a
    rowMat x' = case y of
      NVS y' -> sum $ vap (\(I z) zs -> I (fmap (z *) zs))
                          (nvToMatrix x')
                           y'

reduceTrace
    :: forall ns ms a. (Num a, Known (Prod Nat) (Reverse ns ++ ms))
    => Length ns
    -> Length ms
    -> NestedVec ns (NestedVec (Reverse ns ++ ms) a)
    -> NestedVec ms a
reduceTrace lN lM x =
    case viewR lN of
      RNil -> case x of
        NVZ y -> y
      RSnoc (p :: Proxy o) lN' ->
        reduceTrace lN' lM (mapNVecSlices (f p lN') lN' x)
          \\ appendSnoc lN' p
          \\ snocReverse lN' p
          \\ TCL.reverse' lN' `TCL.append'` lM
  where
    f   :: forall o os. (Known (Prod Nat) (Reverse os ++ ms))
        => Proxy o
        -> Length os
        -> NestedVec '[o] (NestedVec ((o ': Reverse os) ++ ms) a)
        -> NestedVec (Reverse os ++ ms) a
    f _ _ = (\case NVS xs -> sum (vmap I xs)) . diagNV' . joinNestedVec

-- mulMatMat
--     :: Num a
--     => Length ns
--     -> Length ms
--     -> NestedVec ns a
--     -> NestedVec (Reverse ns ++ ms) a
--     -> NestedVec ms a
-- mulMatMat lN lM x y = undefined

-- zipTransp
--     :: (a -> b -> c)
--     -> NestedVec ns a
--     -> NestedVec (Reverse ns) b
--     -> NestedVec ns c
-- zipTransp f = \case
--     NVZ x -> \case
--       NVZ y -> NVZ $ f x y
--     NVS xs -> \case
--       NVS ys -> NVS $ _



diagNV'
    :: NestedVec (n ': n ': ns) a
    -> NestedVec (n ': ns) a
diagNV' = \case
    NVS xs ->
      case xs of
        y :* ys -> case diagNV' $ NVS (vmap nvTail ys) of
          NVS zs -> NVS $ nvHead y :* zs
        ØV      -> NVS ØV

diagNV
    :: Uniform n ms
    -> NestedVec (n ': n ': ms) a
    -> NestedVec '[n] a
diagNV = \case
    UØ   -> diagNV'
    US u -> diagNV u . diagNV'

newtype LTensor :: [N] -> Type where
    LTensor :: { getNVec :: NestedVec ns Double
               } -> LTensor ns

deriving instance Show (LTensor ns)
deriving instance Known (Prod Nat) ns => Num (LTensor ns)
deriving instance Known (Prod Nat) ns => Fractional (LTensor ns)

ltNVec
    :: Functor f
    => (NestedVec ns Double -> f (NestedVec ms Double))
    -> LTensor ns
    -> f (LTensor ms)
ltNVec f = fmap LTensor . f . getNVec

overNVec
    :: (NestedVec ns Double -> NestedVec ms Double)
    -> LTensor ns
    -> LTensor ms
overNVec f = getI . ltNVec (I . f)

overNVec2
    :: (NestedVec ns Double -> NestedVec ms Double -> NestedVec os Double)
    -> LTensor ns
    -> LTensor ms
    -> LTensor os
overNVec2 f x y = LTensor $ f (getNVec x) (getNVec y)

genLTensor
    :: Prod Nat ns
    -> (Prod Fin ns -> Double)
    -> LTensor ns
genLTensor l f = LTensor $ genNestedVec l f

genLTensorA
    :: Applicative f
    => Prod Nat ns
    -> (Prod Fin ns -> f Double)
    -> f (LTensor ns)
genLTensorA l f = LTensor <$> genNestedVecA l f

indexLTensor
    :: Prod Fin ns
    -> LTensor ns
    -> Double
indexLTensor i = indexNestedVec i . getNVec

liftLT
    :: (Known Length o, Known Nat m, Every (Known Nat) o)
    => (Vec n Double -> Vec m Double)
    -> Vec n (NestedVec o Double)
    -> Vec m (NestedVec o Double)
liftLT f xs = fmap (\g -> liftVec g xs) (vecFunc f)

outer
    :: forall ns ms. ()
    => LTensor ns
    -> LTensor ms
    -> LTensor (ns ++ ms)
outer (LTensor x) (LTensor y) = LTensor (joinNestedVec z)
  where
    z :: NestedVec ns (NestedVec ms Double)
    z = fmap (\x' -> (x' *) <$> y) x

instance Tensor LTensor where
    type ElemT  LTensor = Double
    type IndexT LTensor = Prod Fin

    liftT
        :: forall (n :: N) (m :: N) (o :: [N]). (SingI o, Known Nat m)
        => (Vec n Double -> Vec m Double)
        -> Vec n (LTensor o)
        -> Vec m (LTensor o)
    liftT f = fmap LTensor . liftLT f . fmap getNVec
                \\ singLength (sing :: Sing o)
                \\ (entailEvery entailNat :: SingI o :- Every (Known Nat) o)

    -- TODO: ugh this is literally the worst implementation
    transp
        :: forall ns. (SingI ns, SingI (Reverse ns))
        => LTensor ns
        -> LTensor (Reverse ns)
    transp t = genLTensor known ((flip indexLTensor t) . TCP.reverse')
                 \\ lNs
                 \\ singLength (sing :: Sing (Reverse ns))
                 \\ (entailEvery entailNat :: SingI ns :- Every (Known Nat) ns)
                 \\ (entailEvery entailNat :: SingI (Reverse ns) :- Every (Known Nat) (Reverse ns))
                 \\ reverseReverse lNs
      where
        lNs :: Length ns
        lNs = singLength sing

    -- TODO: Decently inefficient because it multiplies everything and then
    -- sums only the diagonal.
    gmul
        :: forall ms os ns. SingI (Reverse os ++ ns)
        => Length ms
        -> Length os
        -> Length ns
        -> LTensor (ms         ++ os)
        -> LTensor (Reverse os ++ ns)
        -> LTensor (ms         ++ ns)
    gmul lM lO lN = overNVec2 $ \x y ->
                      joinNestedVec $ mapNVecSlices (f y) lM x
      where
        f   :: NestedVec (Reverse os ++ ns) Double
            -> NestedVec os Double
            -> NestedVec ns Double
        f y x = (reduceTrace lO lN $ fmap (\x' -> fmap (x' *) y) x)
                  \\ (TCL.reverse' lO `TCL.append'` lN)
                  \\ (entailEvery entailNat :: SingI (Reverse os ++ ns)
                                            :- Every (Known Nat) (Reverse os ++ ns)
                     )

    diag
        :: forall n ns. SingI ns
        => Uniform n ns
        -> LTensor '[n]
        -> LTensor ns
    diag u d
        = genLTensor known (\i -> case uniformVec (prodToVec I u i) of
                                    Nothing     -> 0
                                    Just (I i') -> indexLTensor (i' :< Ø) d
                           )
            \\ uniformLength u
            \\ (entailEvery entailNat :: SingI ns :- Every (Known Nat) ns)

    getDiag
        :: forall n ns. ()
        => Uniform n ns
        -> LTensor (n ': n ': ns)
        -> LTensor '[n]
    getDiag u = overNVec (diagNV u)

    genRand
        :: forall m d (ns :: [N]). (ContGen d, PrimMonad m, SingI ns)
        => d
        -> Gen (PrimState m)
        -> m (LTensor ns)
    genRand d g = generateA (\_ -> genContVar d g)

    generateA
        :: forall f ns. (Applicative f, SingI ns)
        => (Prod Fin ns -> f Double)
        -> f (LTensor ns)
    generateA = genLTensorA known \\ singLength (sing :: Sing ns)
                                  \\ (entailEvery entailNat :: SingI ns :- Every (Known Nat) ns)

    ixElems
        :: Applicative f
        => ((Prod Fin ns, Double) -> f Double)
        -> LTensor ns
        -> f (LTensor ns)
    ixElems f = ltNVec (itraverseNestedVec (curry f))

    (!) = flip indexLTensor


