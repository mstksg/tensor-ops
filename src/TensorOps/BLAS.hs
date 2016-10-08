{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module TensorOps.BLAS where

import           Data.Finite
import           Data.Kind
import           Data.Nested
import           Data.Singletons
import           Data.Singletons.Prelude hiding (Reverse, (++))
import           Data.Singletons.TH
import           Data.Type.Length
import           Data.Type.Product
import           GHC.TypeLits
import           TensorOps.NatKind
import           TensorOps.Types hiding         (transp)
import           Type.Family.List

$(singletons [d|
  data BShape a = BV !a | BM !a !a
    deriving (Show, Eq, Ord, Functor)

  bShapeDims :: BShape a -> [a]
  bShapeDims (BV x  ) = [x]
  bShapeDims (BM x y) = [x,y]
  |])

class NatKind k => BLAS (b :: BShape k -> Type) where
    type ElemB b :: Type
    axpy
        :: ElemB b          -- ^ α
        -> b ('BV n)        -- ^ x
        -> Maybe (b ('BV n))  -- ^ y
        -> b ('BV n)        -- ^ α x + y
    dot :: b ('BV n)        -- ^ x
        -> b ('BV n)        -- ^ y
        -> ElemB b          -- ^ x' y
    norm
        :: b ('BV n)        -- ^ x
        -> ElemB b          -- ^ ||x||
    ger :: b ('BV n)        -- ^ x
        -> b ('BV m)        -- ^ y
        -> b ('BM n m)      -- ^ x y'
    gemv
        :: ElemB b          -- ^ α
        -> b ('BM n m)      -- ^ A
        -> b ('BV m)        -- ^ x
        -> Maybe (ElemB b, b ('BV n))        -- ^ β, y
        -> b ('BV n)        -- ^ α A x + β y
    gemm
        :: ElemB b          -- ^ α
        -> b ('BM n o)      -- ^ A
        -> b ('BM o m)      -- ^ B
        -> Maybe (ElemB b, b ('BM n m))      -- ^ β, C
        -> b ('BM n m)      -- ^ α A B + β C
    indexB
        :: Prod (IndexN k) (BShapeDims s)
        -> b s
        -> ElemB b
    transp
        :: b ('BM n m)
        -> b ('BM m n)

data BTensor :: (k -> Type -> Type) -> (BShape k -> Type) -> [k] -> Type where
    BTS :: !(ElemB b)     -> BTensor v b '[]
    BTV :: !(b ('BV n))   -> BTensor v b '[n]
    BTM :: !(b ('BM n m)) -> BTensor v b '[n,m]
    BTN :: !(v n (BTensor v b (o ': m ': ns)))
        -> BTensor v b (n ': o ': m ': ns)

data ArbiProd :: (k -> Type) -> f k -> Type where
    AP :: ArbiProd f as

-- dispatchBLAS
--     :: forall b ms os ns v. (Floating (ElemB b), BLAS b)
--     => Length ms
--     -> Length os
--     -> Length ns
--     -> BTensor v b (ms         ++ os)
--     -> BTensor v b (Reverse os ++ ns)
--     -> BTensor v b (ms         ++ ns)
-- dispatchBLAS = \case
--     LZ -> \case
--       LZ -> \case
--         LZ -> \case
--           -- scalar-scalar
--           BTS x -> \case
--             BTS y -> BTS $ x * y
--         LS LZ -> \case
--           -- scalar-vector
--           BTS x -> \case
--             BTV y -> BTV $ axpy x y Nothing
--         LS _  -> error "not in scope?"

-- dispatchBLAS lM lO lN = case (lM, lO, lN) of
--     -- dot product
--     (LZ   , LS LZ, LZ   ) -> \case
--       BTV x -> \case
--         BTV y -> BTS $ x `dot` y
--     -- matrix vector
--     (LS LZ, LS LZ, LZ   ) -> \case
--       BTM (x :: b ('BM n m)) -> \case
--         BTV (y :: b ('BV m)) -> BTV $ gemv 1 x y Nothing
--     -- vector matrix
--     (LZ   , LS LZ, LS LZ) -> \case
--       BTV (x :: b ('BV n)) -> \case
--         BTM (y :: b ('BM n m)) -> BTV $ gemv 1 (transp y) x Nothing
--     -- matrix matrix
--     (LS LZ, LS LZ, LS LZ) -> \case
--       BTM (x :: b ('BM n o)) -> \case
--         BTM (y :: b ('BM o m)) -> BTM $ gemm 1 x y Nothing
--     -- outer product
--     (LS LZ, LZ   , LS LZ) -> \case
--       BTV (x :: b ('BV n)) -> \case
--         BTV (y :: b ('BV m)) -> BTM $ ger x y
--     -- scalar scalar
--     (LZ   , LZ  , LZ    ) -> \case


instance forall k (v :: k -> Type -> Type) (b :: BShape k -> Type).
      (Vec v, BLAS b, NatKind k)
      => Tensor (BTensor v b) where
    type ElemT (BTensor v b) = ElemB b


    -- -- general strategy:
    -- --   * if the ranks match, use the primitives
    -- --   * if not ... um we'll figure that out next
    -- gmul    :: SingI (Reverse os ++ ns)
    --         => Length ms
    --         -> Length os
    --         -> Length ns
    --         -> BTensor v b (ms         ++ os)
    --         -> BTensor v b (Reverse os ++ ns)
    --         -> BTensor v b (ms         ++ ns)
    -- gmul lM lO lN = case (lM, lO, lN) of
    --     -- dot product
    --     (LZ, LS LZ, LZ) -> \case
    --       BTV x -> \case
    --         BTV y -> BTS $ x `dot` y


