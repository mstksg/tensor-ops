{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module TensorOps.BLAS where

import           Data.Finite
import           Data.Kind
import           Data.Nested
import           Data.Singletons
import           Data.Singletons.Prelude hiding (Reverse, (++))
import           Data.Singletons.TH
import           Data.Type.Length
import           Data.Type.Length.Util
import           Data.Type.Product
import           GHC.TypeLits
import           TensorOps.NatKind
import           TensorOps.Types hiding         (transp)
import           Type.Family.List
import           Type.Family.Nat

$(singletons [d|
  data BShape a = BV !a | BM !a !a
    deriving (Show, Eq, Ord, Functor)
  |])

type family BShapeDims (s :: BShape k) = (ks :: [k]) | ks -> s where
    BShapeDims ('BV x  ) = '[x]
    BShapeDims ('BM x y) = '[x,y]

genDefunSymbols [''BShapeDims]

-- bShapeDims :: BShape a -> [a]
-- bShapeDims (BV x  ) = [x]
-- bShapeDims (BM x y) = [x,y]

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

-- | TODO: add RULES pragmas so that this can be done without checking
-- lengths at runtime in the common case that the lengths are known at
-- compile-time.
dispatchBLAS
    :: forall b ms os ns v. (Floating (ElemB b), BLAS b)
    => MaxLength N1 ms
    -> MaxLength N1 os
    -> MaxLength N1 ns
    -> BTensor v b (ms         ++ os)
    -> BTensor v b (Reverse os ++ ns)
    -> BTensor v b (ms         ++ ns)
dispatchBLAS lM lO lN v r = case (lM, lO, lN) of
    (MLZ    , MLZ    , MLZ    ) -> case (v, r) of
      -- scalar-scalar
      (BTS x, BTS y) -> BTS $ x * y
    (MLZ    , MLZ    , MLS MLZ) -> case (v, r) of
      -- scalar-vector
      (BTS x, BTV y) -> BTV $ axpy x y Nothing
    (MLZ    , MLS MLZ, MLZ    ) -> case (v, r) of
      -- dot
      (BTV x, BTV y) -> BTS $ x `dot` y
    (MLZ    , MLS MLZ, MLS MLZ) -> case (v, r) of
      -- vector-matrix
      (BTV x, BTM y) -> BTV $ gemv 1 (transp y) x Nothing
    (MLS MLZ, MLZ    , MLZ    ) -> case (v, r) of
      -- vector-scalar
      (BTV x, BTS y) -> BTV $ axpy y x Nothing
    (MLS MLZ, MLZ    , MLS MLZ) -> case (v, r) of
      -- vector-scalar
      (BTV x, BTV y) -> BTM $ ger x y
    (MLS MLZ, MLS MLZ, MLZ    ) -> case (v, r) of
      -- matrx-vector
      (BTM x, BTV y) -> BTV $ gemv 1 x y Nothing
    (MLS MLZ, MLS MLZ, MLS MLZ) -> case (v, r) of
      -- matrix-matrix
      (BTM x, BTM y) -> BTM $ gemm 1 x y Nothing


gmulBLAS
    :: forall b ms os ns v. (Floating (ElemB b), BLAS b)
    => Length ms
    -> MaxLength N1 os
    -> MaxLength N1 ns
    -> BTensor v b (ms         ++ os)
    -> BTensor v b (Reverse os ++ ns)
    -> BTensor v b (ms         ++ ns)
gmulBLAS lM lO lN v r = undefined

-- | General strategy:
--
-- *   We can only outsource to BLAS (using 'dispatchBLAS') in the case
--     that @os@ and @ns@ have length 0 or 1.  Anything else, fall back to
--     the basic reverse-indexing method in "Data.Nested".
-- *   If @ms@ is length 2 or higher, "traverse down" to the length 0 or
--     1 tail...and then sum them up.
gmulB
    :: (SingI (Reverse os ++ ns))
    => Length ms
    -> Length os
    -> Length ns
    -> BTensor v b (ms         ++ os)
    -> BTensor v b (Reverse os ++ ns)
    -> BTensor v b (ms         ++ ns)
gmulB = undefined

instance forall k (v :: k -> Type -> Type) (b :: BShape k -> Type).
      (Vec v, BLAS b, NatKind k)
      => Tensor (BTensor v b) where
    type ElemT (BTensor v b) = ElemB b


    gmul = gmulB
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


