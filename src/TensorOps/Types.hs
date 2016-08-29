{-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE ConstraintKinds         #-}
{-# LANGUAGE DataKinds               #-}
{-# LANGUAGE FlexibleContexts        #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE GADTs                   #-}
{-# LANGUAGE KindSignatures          #-}
{-# LANGUAGE LambdaCase              #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE PolyKinds               #-}
{-# LANGUAGE RankNTypes              #-}
{-# LANGUAGE ScopedTypeVariables     #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE TypeFamilyDependencies  #-}
{-# LANGUAGE TypeInType              #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE UndecidableInstances    #-}

module TensorOps.Types where

-- import           Data.Singletons.Prelude.List hiding (Length)
-- import           Data.Type.Equality
-- import           Data.Type.Subset
-- import           GHC.TypeLits
-- import           Unsafe.Coerce
-- import qualified Control.Foldl                       as F
import           Data.Kind
import           Data.Singletons
import           Data.Type.Length
import           Data.Type.Product
import           Data.Type.Uniform
import           Data.Type.Vector
import           Prelude hiding                         ((.), id)
import           Type.Class.Known
import           Type.Family.List
import           Type.Family.List.Util
import           Type.Family.Nat

class LenUnder (t :: N) (n :: [k])
instance LenUnder n '[]
instance LenUnder n as => LenUnder ('S n) (a ': as)

-- type TensorRank t n = (LenUnder (MaxRank t) n, ListC (DimConstr t <$> n))

class Tensor (t :: [k] -> Type) where
    type ElemT t      :: Type
    -- type RankConstr t :: [k] -> Constraint

    liftT   :: (SingI ns, SingI ms, Floating (ElemT t))
            => Uniform o ns
            -> Uniform o ms
            -> (Vec (Len ns) (ElemT t) -> Vec (Len ms) (ElemT t))
            -> Prod t ns
            -> Prod t ms
    gmul    :: (SingI (ms ++ os), SingI (Reverse os ++ ns), SingI (ms ++ ns))
            => Length ms
            -> Length os
            -> Length ns
            -> t (ms         ++ os)
            -> t (Reverse os ++ ns)
            -> t (ms         ++ ns)
    transp  :: (SingI ns, SingI (Reverse ns))
            => t ns
            -> t (Reverse ns)
    -- foldT   :: (RankConstr t (n ': ns), RankConstr t ns)
    --         => F.Fold (ElemT t) (ElemT t)
    --         -> t (n ': ns)
    --         -> t ns
    -- foldTGrad :: RankConstr t (n ': ns)
    --           => (forall a. Floating a => F.Fold a a)
    --           -> t (n ': ns)
    --           -> t (n ': ns)
    diag    :: (SingI n, SingI ns)
            => Uniform n ns
            -> t '[n]
            -> t ns

type TensorOp = OpPipe TOp

data TOp :: [[k]] -> [[k]] -> Type where
    -- | Lift any `R^N -> R^M` function over every element in a n-tensor list,
    -- producing a m-tensor list.
    Lift    :: Uniform o ns
            -> Uniform o ms
            -> (forall a. Floating a => Vec (Len ns) a -> Vec (Len ms) a)
            -> TOp ns ms
    -- | Generalized tensor product
    GMul    :: Length ms
            -> Length os
            -> Length ns
            -> TOp '[ (ms ++ os), (Reverse os ++ ns) ] '[ ms ++ ns ]
    -- | Transpose (reverse indices)
    Transp  :: Length ns
            -> TOp '[ns] '[Reverse ns]
    -- -- | Fold along the principle direction
    -- Fold    :: Length ns
    --         -> (forall a. Floating a => F.Fold a a)
    --         -> TOp '[n ': ns] '[ns]

data OpPipe :: ([k] -> [k] -> Type) -> [k] -> [k] -> Type where
    OPØ   :: OpPipe f a a
    Pop   :: (SingI (b ++ d), SingI (a ++ d), SingI a, SingI b)
          => Length a
          -> Length d
          -> f a b
          -> OpPipe f (b ++ d) c
          -> OpPipe f (a ++ d) c

-- (~.)
--     :: SingI a
--     => (Sing d, f a b)
--     -> OpPipe f (b ++ d) c
--     -> OpPipe f (a ++ d) c
-- (l,x) ~. y = Pop sing l x y

