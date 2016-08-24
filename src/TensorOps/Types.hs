{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes     #-}
{-# LANGUAGE TypeInType     #-}
{-# LANGUAGE TypeOperators  #-}

module TensorOps.Types where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude.List
import           Data.Type.Uniform
import           Data.Type.Vector
import           GHC.TypeLits
import           Type.Family.Nat
import qualified Control.Foldl                as F

type Dim = [Nat]

class Tensor (t :: Dim -> Type) where

data MatMatChain :: Nat -> [Dim] -> Nat -> Type where
    MMØ :: MatMatChain n '[] m
    MMS :: Sing n
        -> MatMatChain m ms o
        -> MatMatChain n ('[n,m] ': ms) o
    -- MMS :: MatMatChain n ('[m,o] ': ds) p -> MatMatChain n (m ': ms) o

data TensorOp :: [Dim] -> [Dim] -> Type where
    -- | Lift any `R^N -> R^M` function over every element in a n-tensor list,
    -- producing a m-tensor list.
    Lift    :: Uniform n ns
            -> Uniform m ms
            -> (forall a. Floating a => Vec (Len ns) a -> Vec (Len ms) a)
            -> TensorOp ns ms
    -- | Multiply a chain of matrices
    MatMat  :: MatMatChain n ns m
            -> TensorOp ns '[ '[m] ]
    -- | Fold along the principle direction
    Fold    :: (forall a. Floating a => F.Fold a a)
            -> TensorOp (n ': ns) ns
    -- | Tensor/outer product on a chain of vectors
    Outer   :: TensorOp ns '[Concat ns]

data Chain :: (k -> k -> Type) -> k -> k -> Type where
    CØ   :: Chain f a a
    (:.) :: SingI b => f a b -> Chain f b c -> Chain f a c
