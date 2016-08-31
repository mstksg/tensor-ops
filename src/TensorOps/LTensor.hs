{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE IncoherentInstances  #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns         #-}

module TensorOps.LTensor where

import           Control.Applicative
import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude.List (sHead)
import           Data.Type.Combinator
import           Data.Type.Fin
import           Data.Type.Index
import           Data.Type.Length
import           Data.Type.Nat
import           Data.Type.Product            as TCP
import           Data.Type.Product.Util       as TCP
import           Data.Type.Sing
import           Data.Type.Uniform
import           Data.Type.Vector             as TCV
import           Data.Type.Vector.Util
import           TensorOps.Tensor
import           TensorOps.Types
import           Type.Class.Higher
import           Type.Class.Known
import           Type.Class.Witness
import           Type.Family.List
import           Type.Family.Nat

data NestedVec :: [N] -> Type -> Type where
    NVZ :: !a -> NestedVec '[]  a
    NVS :: VecT n (NestedVec ns) a -> NestedVec (n ': ns) a

-- data NestedFin :: [N] -> Type where
--     NFZ :: NestedFin '[]
--     NFS :: Fin n -> NestedFin ns -> NestedFin (n ': ns)

deriving instance Functor (NestedVec ns)
instance Known (Prod Nat) ns => Applicative (NestedVec ns) where
    pure x = case known :: Length ns of
               LZ   -> NVZ x
               LS l -> NVS $ vgen_ (\_ -> pure x)
    (<*>) = \case
      NVZ f -> \case
        NVZ x -> NVZ (f x)
      NVS fs -> \case
        NVS xs -> NVS $ vap (<*>) fs xs

nestedVec0
    :: NestedVec '[] a
    -> a
nestedVec0 = \case
    NVZ x -> x

genNestedVec
    :: Prod Nat ns
    -> (Prod Fin ns -> a)
    -> NestedVec ns a
genNestedVec = \case
    Ø       -> \f -> NVZ (f Ø)
    n :< ns -> \f -> NVS . vgen n $ \i -> genNestedVec ns (f . (i :<))

indexNestedVec
    :: Prod Fin ns
    -> NestedVec ns a
    -> a
indexNestedVec = \case
    Ø -> \case
      NVZ x  -> x
    i :< is -> \case
      NVS xs -> indexNestedVec is (TCV.index i xs)

newtype LTensor :: [N] -> Type where
    LTensor :: { getNVec :: NestedVec ns Double
               } -> LTensor ns

genLTensor
    :: Prod Nat ns
    -> (Prod Fin ns -> Double)
    -> LTensor ns
genLTensor l f = LTensor $ genNestedVec l f

indexLTensor
    :: Prod Fin ns
    -> LTensor ns
    -> Double
indexLTensor i = indexNestedVec i . getNVec

onDiagonal
    :: Vec m (Fin n)
    -> Maybe (Fin n)
onDiagonal = \case
    ØV        -> Nothing
    I x :* xs | all (== x) xs -> Just x
              | otherwise     -> Nothing

liftLT
    :: (Known Length o, Known Nat m, Every (Known Nat) o)
    => (Vec n Double -> Vec m Double)
    -> Vec n (NestedVec o Double)
    -> Vec m (NestedVec o Double)
liftLT f xs = fmap (\g -> liftVec g xs) (vecFunc f)

instance Tensor LTensor where
    type ElemT LTensor = Double

    liftT
        :: forall (n :: N) (m :: N) (o :: [N]). (SingI o, Known Nat m)
        => (Vec n Double -> Vec m Double)
        -> Vec n (LTensor o)
        -> Vec m (LTensor o)
    liftT f = fmap LTensor . liftLT f . fmap getNVec
                \\ singLength (sing :: Sing o)
                \\ (entailEvery entailNat :: SingI o :- Every (Known Nat) o)

    diag
        :: forall n ns. SingI ns
        => Uniform n ns
        -> LTensor '[n]
        -> LTensor ns
    diag u d
        = genLTensor known (\i -> case onDiagonal (prodToVec I u i) of
                                    Nothing -> 0
                                    Just i' -> indexLTensor (i' :< Ø) d
                           )
            \\ uniformLength u
            \\ (entailEvery entailNat :: SingI ns :- Every (Known Nat) ns)

    getDiag
        :: forall n ns. SingI '[n]
        => Uniform n ns
        -> LTensor ns
        -> LTensor '[n]
    getDiag u m = genLTensor known (\i -> indexLTensor (vecToProd (TCP.head' . getI) u (vrep (I i))) m)
                    \\ uniformLength u
                    \\ getNat (sHead (sing :: Sing '[n]))
