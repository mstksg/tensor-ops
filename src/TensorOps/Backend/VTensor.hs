{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeInType                 #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module TensorOps.Backend.VTensor
  ( VTensor
  ) where

-- import           Data.Type.Fin
-- import qualified Data.Vector                      as V
import           Control.Applicative
import           Control.Monad.Primitive
import           Data.Finite
import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude.List hiding (Reverse, Length, (%:++))
import           Data.Singletons.TypeLits
import           Data.Type.Combinator
import           Data.Type.Length
import           Data.Type.Length.Util               as TCL
import           Data.Type.Product                   as TCP
import           Data.Type.Product.Util              as TCP
import           Data.Type.Sing
import           Data.Type.SnocProd
import           Data.Type.Uniform
import           Data.Type.Vector
import           Data.Type.Vector.Util
import           GHC.TypeLits
import           Statistics.Distribution
import           System.Random.MWC
import           TensorOps.Types
import           Type.Class.Known
import           Type.Class.Witness
import           Type.Family.List
import           Type.Family.List.Util
import qualified Data.Type.Nat                       as TCN
import qualified Data.Type.Vector                    as TCV
import qualified Data.Type.Vector.Util               as TCV
import qualified Data.Vector.Sized                   as VS
import qualified Type.Family.Nat                     as TCN

data NestedVec :: [Nat] -> Type -> Type where
    NVZ :: !a                               -> NestedVec '[]       a
    NVS :: !(VS.VectorT n (NestedVec ns) a) -> NestedVec (n ': ns) a

deriving instance Show a => Show (NestedVec ns a)
deriving instance Functor (NestedVec ns)
deriving instance Foldable (NestedVec ns)
deriving instance Traversable (NestedVec ns)

instance SingI ns => Applicative (NestedVec ns) where
    pure :: forall a. a -> NestedVec ns a
    pure x = go sing
      where
        go  :: forall ms. ()
            => Sing ms
            -> NestedVec ms a
        go = \case
          SNil            -> NVZ x
          SNat `SCons` ss -> NVS $ VS.generate (\_ -> go ss)
    (<*>)
        :: forall a b. ()
        => NestedVec ns (a -> b)
        -> NestedVec ns a
        -> NestedVec ns b
    (<*>) = go
      where
        go  :: forall ms. ()
            => NestedVec ms (a -> b)
            -> NestedVec ms a
            -> NestedVec ms b
        go = \case
          NVZ f -> \case
            NVZ x -> NVZ (f x)
          NVS fs -> \case
            NVS xs -> NVS $ VS.vap go fs xs

instance (Num a, SingI ns) => Num (NestedVec ns a) where
    (+)    = liftA2 (+)
    (-)    = liftA2 (-)
    (*)    = liftA2 (*)
    negate = fmap negate
    abs    = fmap abs
    signum = fmap signum
    fromInteger = pure . fromInteger

nvHead
    :: NestedVec ((m + 1) ': ms) a
    -> NestedVec ms a
nvHead = \case
    NVS xs -> VS.head xs

nvTail
    :: NestedVec ((m + 1) ': ms) a
    -> NestedVec (m ': ms) a
nvTail = \case
    NVS xs -> NVS $ VS.tail xs

genNestedVec
    :: Sing ns
    -> (Prod Finite ns -> a)
    -> NestedVec ns a
genNestedVec = \case
    SNil            -> \f -> NVZ (f Ø)
    SNat `SCons` ss -> \f -> NVS $ VS.generate (\i -> genNestedVec ss (f . (i :<)))

genNestedVecA
    :: Applicative f
    => Sing ns
    -> (Prod Finite ns -> f a)
    -> f (NestedVec ns a)
genNestedVecA = \case
    SNil            -> \f -> NVZ <$> f Ø
    SNat `SCons` ss -> \f -> NVS <$> VS.generateA (\i -> genNestedVecA ss (f . (i :<)))


indexNestedVec
    :: Prod Finite ns
    -> NestedVec ns a
    -> a
indexNestedVec = \case
    Ø -> \case
      NVZ x  -> x
    i :< is -> \case
      NVS xs -> indexNestedVec is (xs VS.! i)

joinNestedVec
    :: NestedVec ns (NestedVec ms a)
    -> NestedVec (ns ++ ms) a
joinNestedVec = \case
    NVZ x  -> x
    NVS xs -> NVS $ VS.vmap joinNestedVec xs

mapNVecSlices
    :: (NestedVec ms a -> b)
    -> Length ns
    -> NestedVec (ns ++ ms) a
    -> NestedVec ns b
mapNVecSlices f = \case
    LZ -> NVZ . f
    LS l -> \case
      NVS xs -> NVS $ mapNVecSlices f l `VS.vmap` xs

reduceTrace
    :: forall ns ms a. (Num a, SingI (Reverse ns ++ ms))
    => Length ns
    -> Length ms
    -> NestedVec ns (NestedVec (Reverse ns ++ ms) a)
    -> NestedVec ms a
reduceTrace lN _ = reduceTraceHelp (reverseSnocProd sN) (prodSing sM)
                     \\ reverseReverse lN
  where
    slN :: SnocLength ns
    slN = snocLength lN
    sN :: Prod Sing (Reverse ns)
    sM :: Prod Sing ms
    (sN, sM) = splitProd (snocLengthReverse slN) (singProd sing)

reduceTraceHelp
    :: forall ns ms a. Num a
    => SnocProd Sing ns
    -> Sing ms
    -> NestedVec ns (NestedVec (Reverse ns ++ ms) a)
    -> NestedVec ms a
reduceTraceHelp = \case
    ØS -> \_ -> \case
      NVZ y -> y
    sNs' :& (sN :: Sing n) -> \sMs x ->
      let lNs' = snocProdLength sNs'
      in  reduceTraceHelp sNs' sMs (mapNVecSlices (f sMs sNs' sN) lNs' x)
            \\ appendSnoc lNs' sN
            \\ snocReverse lNs' sN
  where
    f   :: forall o os. ()
        => Sing ms
        -> SnocProd Sing os
        -> Sing o
        -> NestedVec '[o] (NestedVec ((o ': Reverse os) ++ ms) a)
        -> NestedVec (Reverse os ++ ms) a
    f sm sp so = (\case NVS xs -> sum (VS.vmap I xs)) . diagNV' . joinNestedVec
                    \\ prodSing (snocProdReverse sp) %:++ sm
                    \\ so


diagNV'
    :: forall n ns a. SingI n
    => NestedVec (n ': n ': ns) a
    -> NestedVec (n ': ns) a
diagNV' = withKnownNat (sing :: Sing n) $ \case
    NVS xs ->
      case VS.uncons xs of
        VS.VNil       -> NVS VS.empty
        VS.VCons y ys -> case diagNV' $ NVS (VS.vmap nvTail ys) of
          NVS zs -> NVS $ nvHead y `VS.cons` zs

diagNV
    :: SingI n
    => Uniform n ms
    -> NestedVec (n ': n ': ms) a
    -> NestedVec '[n] a
diagNV = \case
    UØ   -> diagNV'
    US u -> diagNV u . diagNV'

itraverseNestedVec
    :: Applicative f
    => (Prod Finite ns -> a -> f b)
    -> NestedVec ns a
    -> f (NestedVec ns b)
itraverseNestedVec f = \case
    NVZ x  -> NVZ <$> f Ø x
    NVS xs -> NVS <$> VS.itraverse (\i -> itraverseNestedVec (\is -> f (i :< is))) xs


newtype VTensor :: [Nat] -> Type where
    VTensor :: { getNVec :: NestedVec ns Double
               } -> VTensor ns

deriving instance Show (VTensor ns)
deriving instance SingI ns => Num (VTensor ns)
-- deriving instance SingI ns => Fractional (VTensor ns)

liftLT
    :: (Applicative (NestedVec o), Known TCN.Nat m)
    -- => (TCV.Vec n Double -> TCV.Vec m Double)
    => (TCV.Vec m (TCV.Vec n Double -> Double))
    -> TCV.Vec n (NestedVec o Double)
    -> TCV.Vec m (NestedVec o Double)
liftLT f xs = fmap (\g -> TCV.liftVec g xs) f

genVTensor
    :: Sing ns
    -> (Prod Finite ns -> Double)
    -> VTensor ns
genVTensor s f = VTensor $ genNestedVec s f

genVTensorA
    :: Applicative f
    => Sing ns
    -> (Prod Finite ns -> f Double)
    -> f (VTensor ns)
genVTensorA s f = VTensor <$> genNestedVecA s f

indexVTensor
    :: Prod Finite ns
    -> VTensor ns
    -> Double
indexVTensor i = indexNestedVec i . getNVec

ltNVec
    :: Functor f
    => (NestedVec ns Double -> f (NestedVec ms Double))
    -> VTensor ns
    -> f (VTensor ms)
ltNVec f = fmap VTensor . f . getNVec

overNVec
    :: (NestedVec ns Double -> NestedVec ms Double)
    -> VTensor ns
    -> VTensor ms
overNVec f = getI . ltNVec (I . f)
{-# INLINE overNVec #-}

overNVec2
    :: (NestedVec ns Double -> NestedVec ms Double -> NestedVec os Double)
    -> VTensor ns
    -> VTensor ms
    -> VTensor os
overNVec2 f x y = VTensor $ f (getNVec x) (getNVec y)
{-# INLINE overNVec2 #-}



instance Tensor VTensor where
    type ElemT  VTensor = Double
    type IndexT VTensor = Prod Finite


    liftT
        :: forall (n :: TCN.N) (m :: TCN.N) (o :: [Nat]). (SingI o, Known TCN.Nat m)
        -- => (TCV.Vec n Double -> Vec m Double)
        => (Vec m (Vec n Double -> Double))
        -> TCV.Vec n (VTensor o)
        -> TCV.Vec m (VTensor o)
    liftT f = fmap VTensor . liftLT f . fmap getNVec

    -- TODO: this is an awful implementation
    transp
        :: forall ns. (SingI ns, SingI (Reverse ns))
        => VTensor ns
        -> VTensor (Reverse ns)
    transp t = genVTensor sing ((flip indexVTensor t) . TCP.reverse')
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
        -> VTensor (ms         ++ os)
        -> VTensor (Reverse os ++ ns)
        -> VTensor (ms         ++ ns)
    gmul lM lO lN = overNVec2 $ \x y ->
                      joinNestedVec $ mapNVecSlices (f y) lM x
      where
        f   :: NestedVec (Reverse os ++ ns) Double
            -> NestedVec os Double
            -> NestedVec ns Double
        f y x = (reduceTrace lO lN $ fmap (\x' -> fmap (x' *) y) x)

    diag
        :: forall n ns. SingI ns
        => Uniform n ns
        -> VTensor '[n]
        -> VTensor ns
    diag u d
        = genVTensor sing (\i -> case uniformVec (prodToVec I u i) of
                                   Nothing     -> 0
                                   Just (I i') -> indexVTensor (i' :< Ø) d
                          )
            \\ witSings (sing :: Sing ns)

    getDiag
        :: forall n ns. SingI '[n]
        => Uniform n ns
        -> VTensor (n ': n ': ns)
        -> VTensor '[n]
    getDiag u = overNVec (diagNV u)
                  \\ sHead (sing :: Sing '[n])

    genRand
        :: forall m d (ns :: [Nat]). (ContGen d, PrimMonad m, SingI ns)
        => d
        -> Gen (PrimState m)
        -> m (VTensor ns)
    genRand d g = generateA (\_ -> genContVar d g)

    generateA
        :: forall f ns. (Applicative f, SingI ns)
        => (Prod Finite ns -> f Double)
        -> f (VTensor ns)
    generateA = genVTensorA sing

    ixElems
        :: Applicative f
        => ((Prod Finite ns, Double) -> f Double)
        -> VTensor ns
        -> f (VTensor ns)
    ixElems f = ltNVec (itraverseNestedVec (curry f))

    (!) = flip indexVTensor


