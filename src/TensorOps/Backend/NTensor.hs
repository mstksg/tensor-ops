{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeInType                 #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module TensorOps.Backend.NTensor
  ( NTensor
  , NTensorL
  , NTensorV
  )
  where

import           Control.DeepSeq
import           Control.Monad.Primitive
import           Data.Distributive
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
import           GHC.Generics
import           Statistics.Distribution
import           System.Random.MWC
import           TensorOps.NatKind
import           TensorOps.Types
import           Type.Class.Higher
import           Type.Class.Higher.Util
import           Type.Class.Witness
import           Type.Family.List
import qualified Data.Type.Vector                    as TCV
import qualified Data.Type.Vector.Util               as TCV
import qualified Data.Vector.Sized                   as VS
import qualified Type.Family.Nat                     as TCN

newtype NTensor :: (k -> Type -> Type) -> Type -> [k] -> Type where
    NTensor
        :: { getNVec :: Nested v js a }
        -> NTensor v a js

deriving instance Generic (NTensor v a ns)
deriving instance (NFData a, Nesting Proxy NFData v) => NFData (NTensor v a ns)
instance (NFData a, Nesting Proxy NFData v) => Nesting1 w NFData (NTensor v a) where
    nesting1 _ = Wit

genNTensor
    :: forall k (v :: k -> Type -> Type) (ns :: [k]) (a :: Type). Vec v
    => Sing ns
    -> (Prod (IndexN k) ns -> a)
    -> NTensor v a ns
genNTensor s f = NTensor $ genNested s f
{-# INLINE genNTensor #-}

genNTensorA
    :: forall k (v :: k -> Type -> Type) (ns :: [k]) (a :: Type) f. (Applicative f, Vec v)
    => Sing ns
    -> (Prod (IndexN k) ns -> f a)
    -> f (NTensor v a ns)
genNTensorA s f = NTensor <$> genNestedA s f
{-# INLINE genNTensorA #-}

indexNTensor
    :: forall k (v :: k -> Type -> Type) (ns :: [k]) (a :: Type). Vec v
    => Prod (IndexN k) ns
    -> NTensor v a ns
    -> a
indexNTensor i = indexNested i . getNVec
{-# INLINE indexNTensor #-}

overNVec2
    :: (Nested v ns a -> Nested w ms b -> Nested u os c)
    -> NTensor v a ns
    -> NTensor w b ms
    -> NTensor u c os
overNVec2 f x y = NTensor $ f (getNVec x) (getNVec y)
{-# INLINE overNVec2 #-}

ntNVec
    :: Functor f
    => (Nested v ns a -> f (Nested w ms b))
    -> NTensor v a ns
    -> f (NTensor w b ms)
ntNVec f = fmap NTensor . f . getNVec
{-# INLINE ntNVec #-}

nvecNT
    :: Functor f
    => (NTensor v a ns -> f (NTensor w b ms))
    -> Nested v ns a
    -> f (Nested w ms b)
nvecNT f = fmap getNVec . f . NTensor
{-# INLINE nvecNT #-}

overNVec
    :: (Nested v ns a -> Nested v ms a)
    -> NTensor v a ns
    -> NTensor v a ms
overNVec f = getI . ntNVec (I . f)
{-# INLINE overNVec #-}

underNVec
    :: (NTensor v a ns -> NTensor v a ms)
    -> Nested v ns a
    -> Nested v ms a
underNVec f = getNVec . f . NTensor


instance
      ( Vec (v :: k -> Type -> Type)
      , Floating a
      , Nesting1 Proxy Functor      v
      , Nesting1 Sing  Applicative  v
      , Nesting1 Proxy Foldable     v
      , Nesting1 Proxy Traversable  v
      , Nesting1 Sing  Distributive v
      , Eq1 (IndexN k)
      ) => Tensor (NTensor v a) where
    type ElemT  (NTensor v a) = a

    liftT
        :: forall (n :: TCN.N) (m :: TCN.N) (o :: [k]). SingI o
        => (TCV.Vec m (TCV.Vec n a -> a))
        -> TCV.Vec n (NTensor v a o)
        -> TCV.Vec m (NTensor v a o)
    liftT f = fmap NTensor . liftNested f . fmap getNVec
    {-# INLINE liftT #-}

    transp
        :: forall ns. (SingI ns, SingI (Reverse ns))
        => NTensor v a ns
        -> NTensor v a (Reverse ns)
    -- transp = overNVec (transpose sing)
    transp = overNVec (transpose' (singLength sing) sing)
    {-# INLINE transp #-}

    gmul
        :: forall ms os ns. SingI (Reverse os ++ ns)
        => Length ms
        -> Length os
        -> Length ns
        -> NTensor v a (ms         ++ os)
        -> NTensor v a (Reverse os ++ ns)
        -> NTensor v a (ms         ++ ns)
    gmul lM lO lN = overNVec2 (gmul' lM lO lN)
                      \\ sO'
                      \\ sN
      where
        sO' :: Sing (Reverse os)
        sN  :: Sing ns
        (sO', sN) = splitSing (TCL.reverse' lO)
                              (sing :: Sing (Reverse os ++ ns))
    {-# INLINE gmul #-}

    -- TODO: this is a dumb implementation
    diag
        :: forall n ns. SingI (n ': ns)
        => Uniform n ns
        -> NTensor v a '[n]
        -> NTensor v a (n ': ns)
    diag u d
        = genNTensor sing (\i -> case TCV.uniformVec (prodToVec I (US u) i) of
                                   Nothing     -> 0
                                   Just (I i') -> indexNTensor (i' :< Ø) d
                          )
            \\ (produceEq1 :: Eq1 (IndexN k) :- Eq (IndexN k n))
    {-# INLINE diag #-}

    -- TODO: this can be just done using genNTensor
    getDiag
        :: forall n ns. SingI '[n]
        => Uniform n ns
        -> NTensor v a (n ': n ': ns)
        -> NTensor v a '[n]
    getDiag u = overNVec (diagNV sing u)
                  \\ sHead (sing :: Sing '[n])
    {-# INLINE getDiag #-}

    genRand
        :: forall m d (ns :: [k]). (ContGen d, PrimMonad m, SingI ns)
        => d
        -> Gen (PrimState m)
        -> m (NTensor v a ns)
    genRand d g = generateA (\_ -> realToFrac <$> genContVar d g)
    {-# INLINE genRand #-}

    generateA
        :: forall f ns. (Applicative f, SingI ns)
        => (Prod (IndexN k) ns -> f a)
        -> f (NTensor v a ns)
    generateA = genNTensorA sing
    {-# INLINE generateA #-}

    (!) = flip indexNTensor
    {-# INLINE (!) #-}

    ixRows
        :: Applicative f
        => Length ms
        -> Length os
        -> (Prod (IndexN k) ms -> NTensor v a ns -> f (NTensor v a os))
        -> NTensor v a (ms ++ ns)
        -> f (NTensor v a (ms ++ os))
    ixRows l _ f = ntNVec $ fmap joinNested . nIxRows l (\i -> nvecNT (f i))
    {-# INLINE ixRows #-}

    sumRows
        :: forall n ns. SingI ns
        => NTensor v a (n ': ns)
        -> NTensor v a ns
    sumRows = overNVec sumRowsNested
                \\ (nesting1 Proxy :: Wit (Foldable (v n)))
    {-# INLINE sumRows #-}

    mapRows
        :: Length ns
        -> (NTensor v a ms -> NTensor v a ms)
        -> NTensor v a (ns ++ ms)
        -> NTensor v a (ns ++ ms)
    mapRows l f = overNVec $ joinNested . mapNVecSlices (underNVec f) l
    {-# INLINE mapRows #-}

type NTensorL = NTensor (Flip2 TCV.VecT   I) Double
type NTensorV = NTensor (Flip2 VS.VectorT I) Double
