{-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE DataKinds               #-}
{-# LANGUAGE FlexibleContexts        #-}
{-# LANGUAGE GADTs                   #-}
{-# LANGUAGE KindSignatures          #-}
{-# LANGUAGE LambdaCase              #-}
{-# LANGUAGE PolyKinds               #-}
{-# LANGUAGE RankNTypes              #-}
{-# LANGUAGE ScopedTypeVariables     #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE TypeFamilyDependencies  #-}
{-# LANGUAGE TypeInType              #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE UndecidableInstances    #-}

module TensorOps.Types where

-- import           Data.Singletons
-- import           Data.Singletons.Prelude.List hiding (Length)
-- import           Data.Type.Equality
-- import           Data.Type.Subset
-- import           Unsafe.Coerce
import           Data.Kind
import           Data.Type.Length
import           Data.Type.Product
import           Data.Type.Uniform
import           Data.Type.Vector
import           GHC.TypeLits
import           Prelude hiding                         ((.), id)
import           Type.Class.Known
import           Type.Family.List
import           Type.Family.Nat
import qualified Control.Foldl                          as F

type Dim = [Nat]

-- type family Rev (asbs :: ([k], [k])) = (cs :: [k]) | cs -> asbs where
--     Rev '( '[]    , bs) = bs
--     Rev '( a ': as, bs) = Rev '(as, a ': bs)

class Tensor (t :: Dim -> Type) where
    type ElemT t :: Type
    liftT   :: Floating (ElemT t)
            => Uniform o ns
            -> Uniform o ms
            -> (Vec (Len ns) (ElemT t) -> Vec (Len ms) (ElemT t))
            -> Prod t ns
            -> Prod t ms
    gmul    :: Length ms
            -> Length os
            -> Length ns
            -> t (ms         ++ os)
            -> t (Reverse os ++ ns)
            -> t (ms         ++ ns)
    -- mulMM   :: t '[m, n]
    --         -> t '[n, o]
    --         -> t '[m, o]
    -- mulMV   :: t (m ': ms)
    --         -> t ms
    --         -> t '[m]
    foldT   :: (forall a. Floating a => F.Fold a a)
            -> t (n ': ns)
            -> t ns
    eye     :: Uniform n ns
            -> t ns
    transp  :: t ns
            -> t (Reverse ns)
    -- uncons  :: t (n ': ns)
    --         -> VecT (Len ns) t '[n]
    -- outer   :: t ns
    --         -> t ms
    --         -> t (ns ++ ms)

data MatMatChain :: Nat -> [Dim] -> Nat -> Type where
    MMØ :: MatMatChain n '[] n
    MMS :: MatMatChain m ms o
        -> MatMatChain n ('[n,m] ': ms) o

type TensorOp = OpPipe TOp

data TOp :: [Dim] -> [Dim] -> Type where
    -- | Lift any `R^N -> R^M` function over every element in a n-tensor list,
    -- producing a m-tensor list.
    Lift    :: Uniform o ns
            -> Uniform o ms
            -> (forall a. Floating a => Vec (Len ns) a -> Vec (Len ms) a)
            -> TOp ns ms
    GMul    :: Length ms
            -> Length os
            -> Length ns
            -> TOp '[ (ms ++ os), (Reverse os ++ ns) ] '[ ms ++ ns ]
    -- -- | Matrix product
    -- MatMat  :: TOp [ '[m,n], '[n,o] ] '[ '[m,o] ]
    -- -- | Matrix-vector multiplication
    -- MatVec  :: TOp '[ (m ': ms), ms ] '[ '[m] ]
    -- -- | Outer (tensor) product
    -- Outer   :: TOp '[ns,ms] '[ns ++ ms]
    -- | Transpose (reverse indices)
    Transp  :: Length ns
            -> TOp '[ns] '[Reverse ns]
    -- | Fold along the principle direction
    Fold    :: (forall a. Floating a => F.Fold a a)
            -> TOp '[n ': ns] '[ns]

data OpPipe :: ([k] -> [k] -> Type) -> [k] -> [k] -> Type where
    OPØ   :: OpPipe f a a
    Pop   :: Length a
          -> Length d
          -> f a b
          -> OpPipe f (b ++ d) c
          -> OpPipe f (a ++ d) c
    -- (:~)  :: (Known Length d)
    --       => OpPipe f a b -> OpPipe f (b ++ d) c -> OpPipe f (a ++ d) c
    -- OP1   :: f a b
    --       -> OpPipe f a b
    -- (:.)  :: SingI b
    --       => OpPipe f a b -> OpPipe f b c -> OpPipe f a c
    -- (:*)  :: Known Length a
    --       => OpPipe f a b -> OpPipe f c d -> OpPipe f (a ++ c) (b ++ d)
    -- (:&)  :: (SingI a, SingI b, SingI c)
    --       => OpPipe f a b -> OpPipe f a c -> OpPipe f a (b ++ c)
    -- First :: Length as
    --       => Length cs
    --       -> OpPipe f as bs
    --       -> OpPipe f (as ++ cs) (bs ++ cs)

(~.)
    :: Known Length a
    => (Length d, f a b)
    -> OpPipe f (b ++ d) c
    -> OpPipe f (a ++ d) c
(l,x) ~. y = Pop known l x y


-- infixr 9 :.
-- infixr 5 :*
-- infixr 5 :&
-- infixr 5 :~

data RevLength :: [Nat] -> [Nat] -> Type where
    RLZ :: RevLength '[] '[]
    RLS :: RevLength as  bs  -> RevLength (c ': as) (bs >: c)

-- mkRev
--     :: (c ': as) :~: Reverse (as >: c)
-- mkRev = unsafeCoerce Refl

-- unRev
--     :: RevLength ns ms
--     -> (ns :~: Reverse ms)
-- unRev = \case
--     RLZ    -> Refl
--     RLS rl -> case unRev rl of
--                 r@Refl -> case hey (rlSecond rl) r of
--                             Refl -> undefined

-- rlSecond
--     :: RevLength as bs
--     -> Length bs
-- rlSecond = \case
--     RLZ    -> LZ
--     RLS rl -> _ $ rlSecond rl

-- hey :: Length bs
--     -> (as :~: Reverse bs)
--     -> ((c ': as) :~: Reverse (bs >: c))
-- hey _ Refl = unsafeCoerce Refl
