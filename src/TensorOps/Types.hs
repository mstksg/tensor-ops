{-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE DataKinds               #-}
{-# LANGUAGE FlexibleContexts        #-}
{-# LANGUAGE GADTs                   #-}
{-# LANGUAGE KindSignatures          #-}
{-# LANGUAGE LambdaCase              #-}
{-# LANGUAGE RankNTypes              #-}
{-# LANGUAGE ScopedTypeVariables     #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE TypeInType              #-}
{-# LANGUAGE TypeOperators           #-}

module TensorOps.Types where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude.List hiding (Length)
import           Data.Type.Equality
import           Data.Type.Length
import           Data.Type.Product
import           Data.Type.Subset
import           Data.Type.Uniform
import           Data.Type.Vector
import           GHC.TypeLits
import           Prelude hiding                      ((.), id)
import           Type.Class.Known
import           Type.Family.Nat
import qualified Control.Foldl                       as F

type Dim = [Nat]

class Tensor (t :: Dim -> Type) where
    type ElemT t :: Type
    liftT   :: Floating (ElemT t)
            => Uniform n ns
            -> Uniform m ms
            -> (Vec (Len ns) (ElemT t) -> Vec (Len ms) (ElemT t))
            -> Prod t ns
            -> Prod t ms
    mulMM   :: t '[m, n]
            -> t '[n, o]
            -> t '[m, o]
    mulMV   :: t (m ': ms)
            -> t ms
            -> t '[m]
    foldT   :: Floating (ElemT t)
            => F.Fold (ElemT t) (ElemT t)
            -> t (n ': ns)
            -> t ns
    eye     :: Uniform n ns
            -> t ns
    transp  :: Len ns :~: Len ms
            -> Subset ns ms
            -> t ns
            -> t ms
    outer   :: t ns
            -> t ms
            -> t (ns :++ ms)

data MatMatChain :: Nat -> [Dim] -> Nat -> Type where
    MMØ :: MatMatChain n '[] n
    MMS :: MatMatChain m ms o
        -> MatMatChain n ('[n,m] ': ms) o

type TensorOp = OpPipe TOp

data TOp :: [Dim] -> [Dim] -> Type where
    -- | Lift any `R^N -> R^M` function over every element in a n-tensor list,
    -- producing a m-tensor list.
    Lift    :: Uniform n ns
            -> Uniform m ms
            -> (forall a. Floating a => Vec (Len ns) a -> Vec (Len ms) a)
            -> TOp ns ms
    -- | Multiply a chain of matrices
    MatMat  :: MatMatChain n ns m
            -> TOp ns '[ '[n, m] ]
    -- | Matrix-vector multiplication
    MatVec  :: TOp '[ (m ': ms), ms ] '[ '[m] ]
    -- -- | Tensor/outer product on a chain of vectors
    -- Outer   :: Sing ns
    --         -> Sing (Concat ns)
    --         -> TOp ns '[Concat ns]
    -- | Outer (tensor) product
    Outer   :: TOp '[ns,ms] '[ns :++ ms]
    -- | Transpose based on indices
    Transp  :: Len ns :~: Len ms
            -> Subset ns ms
            -> TOp '[ns] '[ms]
    -- | Fold along the principle direction
    Fold    :: (forall a. Floating a => F.Fold a a)
            -> TOp '[n ': ns] '[ns]

data OpPipe :: ([k] -> [k] -> Type) -> [k] -> [k] -> Type where
    OPØ   :: OpPipe f a a
    OP1   :: f a b
          -> OpPipe f a b
    (:.)  :: SingI b
          => OpPipe f a b -> OpPipe f b c -> OpPipe f a c
    (:*)  :: Known Length a
          => OpPipe f a b -> OpPipe f c d -> OpPipe f (a :++ c) (b :++ d)
    (:&)  :: (SingI a, SingI b, SingI c)
          => OpPipe f a b -> OpPipe f a c -> OpPipe f a (b :++ c)
    -- First :: Length as
    --       => Length cs
    --       -> OpPipe f as bs
    --       -> OpPipe f (as :++ cs) (bs :++ cs)

infixr 9 :.
infixr 5 :*
infixr 5 :&
