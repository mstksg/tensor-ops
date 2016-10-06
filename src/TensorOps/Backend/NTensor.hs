{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeInType                 #-}
{-# LANGUAGE TypeOperators              #-}

module TensorOps.Backend.NTensor
  ( NTensor
  , LTensor
  , VTensor
  )
  where

import           Control.Monad.Primitive
import           Data.Kind
import           Data.Nested
import           Data.Proxy
import           Data.Singletons
import           Data.Singletons.Prelude.List hiding (Length, Reverse)
import           Data.Type.Combinator
import           Data.Type.Combinator.Util
import           Data.Type.Length                    as TCL
import           Data.Type.Length.Util               as TCL
import           Data.Type.Product                   as TCP
import           Data.Type.Product.Util              as TCP
import           Data.Type.Sing
import           Data.Type.Uniform
import           Statistics.Distribution
import           System.Random.MWC
import           TensorOps.Types
import           Type.Class.Higher
import           Type.Class.Higher.Util
import           Type.Class.Known
import           Type.Class.Witness
import           Type.Family.List
import           Type.Family.List.Util
import           Type.NatKind
import qualified Data.Type.Nat                       as TCN
import qualified Data.Type.Vector                    as TCV
import qualified Data.Type.Vector.Util               as TCV
import qualified Data.Vector.Sized                   as VS
import qualified Type.Family.Nat                     as TCN
import qualified Type.Family.Nat.Util                as TCN

newtype NTensor :: (k -> Type -> Type) -> Type -> [k] -> Type where
    NTensor
        :: { getNVec :: Nested v js a }
        -> NTensor v a js

liftLT
    :: (Applicative (Nested v o), Known TCN.Nat m)
    => (TCV.Vec m (TCV.Vec n a -> a))
    -> TCV.Vec n (Nested v o a)
    -> TCV.Vec m (Nested v o a)
liftLT f xs = fmap (\g -> TCV.liftVec g xs) f
{-# INLINE liftLT #-}

genNTensor
    :: forall k (v :: k -> Type -> Type) (ns :: [k]) (a :: Type). Vec v
    => Sing ns
    -> (Prod (IndexN k) ns -> a)
    -> NTensor v a ns
genNTensor s f = NTensor $ genNestedVec s f
{-# INLINE genNTensor #-}

genNTensorA
    :: forall k (v :: k -> Type -> Type) (ns :: [k]) (a :: Type) f. (Applicative f, Vec v)
    => Sing ns
    -> (Prod (IndexN k) ns -> f a)
    -> f (NTensor v a ns)
genNTensorA s f = NTensor <$> genNestedVecA s f
{-# INLINE genNTensorA #-}

indexNTensor
    :: forall k (v :: k -> Type -> Type) (ns :: [k]) (a :: Type). Vec v
    => Prod (IndexN k) ns
    -> NTensor v a ns
    -> a
indexNTensor i = indexNestedVec i . getNVec
{-# INLINE indexNTensor #-}

overNVec2
    :: (Nested v ns a -> Nested v ms a -> Nested v os a)
    -> NTensor v a ns
    -> NTensor v a ms
    -> NTensor v a os
overNVec2 f x y = NTensor $ f (getNVec x) (getNVec y)
{-# INLINE overNVec2 #-}

ltNVec
    :: Functor f
    => (Nested v ns a -> f (Nested v ms a))
    -> NTensor v a ns
    -> f (NTensor v a ms)
ltNVec f = fmap NTensor . f . getNVec
{-# INLINE ltNVec #-}

overNVec
    :: (Nested v ns a -> Nested v ms a)
    -> NTensor v a ns
    -> NTensor v a ms
overNVec f = getI . ltNVec (I . f)
{-# INLINE overNVec #-}


instance
      ( Vec (v :: k -> Type -> Type)
      , a ~ Double
      , Nesting1 Proxy Functor v
      , Nesting1 Sing Applicative v
      , Nesting1 Proxy Foldable v
      , Nesting1 Proxy Traversable v
      , Eq1 (IndexN k)
      ) => Tensor (NTensor v a) where
    type ElemT  (NTensor v a) = a
    type IndexT (NTensor (v :: k -> Type -> Type) a) = Prod (IndexN k)

    liftT
        :: forall (n :: TCN.N) (m :: TCN.N) (o :: [k]). (SingI o, Known TCN.Nat m)
        => (TCV.Vec m (TCV.Vec n a -> a))
        -> TCV.Vec n (NTensor v a o)
        -> TCV.Vec m (NTensor v a o)
    liftT f = fmap NTensor . liftLT f . fmap getNVec
    {-# INLINE liftT #-}

    -- TODO: this is an awful implementation
    transp
        :: forall ns. (SingI ns, SingI (Reverse ns))
        => NTensor v a ns
        -> NTensor v a (Reverse ns)
    transp = overNVec (transpose sing)
    {-# INLINE transp #-}

    -- TODO: Decently inefficient because it multiplies everything and then
    -- sums only the diagonal.
    gmul
        :: forall ms os ns.
         ( SingI (ms ++ os)
         , SingI (Reverse os ++ ns)
         , SingI (ms ++ ns)
         )
        => Length ms
        -> Length os
        -> Length ns
        -> NTensor v a (ms         ++ os)
        -> NTensor v a (Reverse os ++ ns)
        -> NTensor v a (ms         ++ ns)
    gmul lM lO lN = overNVec2 (gmul' lM lO lN)
                      \\ sOr
                      \\ sN
      where
        lO' = TCL.reverse' lO
        sOr :: Sing (Reverse os)
        sN  :: Sing ns
        (sOr, sN) = splitSing (TCL.reverse' lO)
                              (sing :: Sing (Reverse os ++ ns))

    diag
        :: forall n ns. SingI ns
        => Uniform n ns
        -> NTensor v a '[n]
        -> NTensor v a ns
    diag u d
        = genNTensor sing (\i -> case TCV.uniformVec (prodToVec I u i) of
                                   Nothing     -> 0
                                   Just (I i') -> indexNTensor (i' :< Ø) d
                          )
            \\ witSings (sing :: Sing ns)
            \\ (produceEq1 :: Eq1 (IndexN k) :- Eq (IndexN k n))
    -- {-# INLINE diag #-}

    getDiag
        :: forall n ns. SingI '[n]
        => Uniform n ns
        -> NTensor v a (n ': n ': ns)
        -> NTensor v a '[n]
    getDiag u = overNVec (diagNV sing u)
                  \\ sHead (sing :: Sing '[n])
    -- {-# INLINE getDiag #-}

    genRand
        :: forall m d (ns :: [k]). (ContGen d, PrimMonad m, SingI ns)
        => d
        -> Gen (PrimState m)
        -> m (NTensor v a ns)
    genRand d g = generateA (\_ -> genContVar d g)
    -- {-# INLINE genRand #-}

    generateA
        :: forall f ns. (Applicative f, SingI ns)
        => (Prod (IndexN k) ns -> f a)
        -> f (NTensor v a ns)
    generateA = genNTensorA sing
    {-# INLINE generateA #-}

    ixElems
        :: Applicative f
        => ((Prod (IndexN k) ns, a) -> f a)
        -> NTensor v a ns
        -> f (NTensor v a ns)
    ixElems f = ltNVec (itraverseNestedVec (curry f))
    {-# INLINE ixElems #-}

    (!) = flip indexNTensor
    {-# INLINE (!) #-}

-- newtype LTensor ns = LTensor { lTensor :: NTensor (Flip2 TCV.VecT   I) Double ns }
-- newtype VTensor ns = VTensor { vTensor :: NTensor (Flip2 VS.VectorT I) Double ns }

type LTensor = NTensor (Flip2 TCV.VecT I) Double
type VTensor = NTensor (Flip2 VS.VectorT I) Double
