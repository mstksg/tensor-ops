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
{-# LANGUAGE TypeApplications       #-}
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
import           Data.Singletons.Prelude hiding (Reverse, (++), Head)
import           Data.Singletons.TH
import           Data.Type.Combinator
import           Data.Type.Length               as TCL
import           Data.Type.Length.Util          as TCL
import           Data.Type.Nat
import           Data.Type.Product              as TCP
import           Data.Type.Product.Util         as TCP
import           GHC.TypeLits
import           TensorOps.NatKind
import           TensorOps.Types hiding         (transp)
import           Type.Class.Witness
import           Type.Family.List
import           Type.Family.List.Util
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
    iRowsB
        :: Applicative f
        => (IndexN k n -> b ('BV m) -> f (b ('BV o)))
        -> b ('BM n m)
        -> f (b ('BM n o))
    iElemsB
        :: Applicative f
        => (Prod (IndexN k) (BShapeDims s) -> ElemB b -> f (ElemB b))
        -> b s
        -> f (b s)
    bgenA
        :: Applicative f
        => (Prod (IndexN k) (BShapeDims s) -> f (ElemB b))
        -> f (b s)
    eye :: b ('BM n n)

elemsB
    :: (Applicative f, BLAS b)
    => (ElemB b -> f (ElemB b))
    -> b s
    -> f (b s)
elemsB f = iElemsB (\_ x -> f x)


data BTensor :: (k -> Type -> Type) -> (BShape k -> Type) -> [k] -> Type where
    BTS :: !(ElemB b)     -> BTensor v b '[]
    BTV :: !(b ('BV n))   -> BTensor v b '[n]
    BTM :: !(b ('BM n m)) -> BTensor v b '[n,m]
    BTN :: !(v n (BTensor v b (o ': m ': ns)))
        -> BTensor v b (n ': o ': m ': ns)

-- | TODO: add RULES pragmas so that this can be done without checking
-- lengths at runtime in the common case that the lengths are known at
-- compile-time.
--
-- Also, totally forgot about matrix-scalar multiplication here, but there
-- isn't really any way of making it work without a lot of empty cases.
-- should probably handle one level up.
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
    :: forall b ms os ns v. (Floating (ElemB b), BLAS b, Vec v)
    => Length ms
    -> MaxLength N1 os
    -> MaxLength N1 ns
    -> BTensor v b (ms         ++ os)
    -> BTensor v b (Reverse os ++ ns)
    -> BTensor v b (ms         ++ ns)
gmulBLAS lM mlO mlN v r = case mlO of
    MLZ -> case splittingEnd (S_ (S_ Z_)) (lengthProd lM) of
      FewerEnd MLZ             _ -> dispatchBLAS MLZ       mlO  mlN v r
      FewerEnd (MLS MLZ)       _ -> dispatchBLAS (MLS MLZ) mlO mlN v r
      FewerEnd (MLS (MLS MLZ)) _ -> case v of
        BTM xs -> case mlN of
          MLZ     -> case r of
            BTS y  -> BTM $ gemm y xs eye Nothing
          MLS MLZ -> case r of
            BTV ys -> undefined
      SplitEnd (ELS (ELS ELZ)) lM0 lM1@(Proxy :< Proxy :< Ø) -> case mlN of
        MLZ -> case r of
          BTS y -> mapBase (prodLength lM0) (prodLength lM1) (\xs -> BTM $ gemm y xs eye Nothing) v
                     \\ appendNil lM
        MLS MLZ -> case r of
          BTV ys -> undefined
    MLS MLZ -> case splittingEnd (S_ Z_) (lengthProd lM) of
      FewerEnd mlM _ -> dispatchBLAS mlM mlO mlN v r
      SplitEnd (ELS ELZ) plM0 plM1 -> case mlN of
        MLZ -> case r of
          BTV ys -> let lM0 = prodLength plM0
                        lM1 = prodLength plM1
                    in  mapBase lM0 lM1 (\xs -> BTV $ gemv 1 xs ys Nothing) v
                          \\ appendNil lM
                          \\ appendAssoc (TCL.tail' lM0)
                                         lM1
                                         (LS LZ :: Length os)

bTensorElems
    :: forall k (v :: k -> Type -> Type) ns n m ms os b f. (Applicative f, Vec v, BLAS b)
    => (ElemB b -> f (ElemB b))
    -> BTensor v b ns
    -> f (BTensor v b ns)
bTensorElems f = \case
    BTS x  -> BTS <$> f x
    BTV xs -> BTV <$> elemsB f xs
    BTM xs -> BTM <$> elemsB f xs
    BTN xs -> BTN <$> vITraverse (\_ x -> bTensorElems f x) xs

mapBase
    :: forall k (v :: k -> Type -> Type) ns n m ms os b. Vec v
    => Length ns
    -> Length ms
    -> (b (BM n m) -> BTensor v b ms)
    -> BTensor v b (ns ++ [n,m])
    -> BTensor v b (ns ++ ms)
mapBase lN lM f = getI . traverseBase lN lM (I . f)

traverseBase
    :: forall k (v :: k -> Type -> Type) ns n m ms os b f. (Applicative f, Vec v)
    => Length ns
    -> Length ms
    -> (b (BM n m) -> f (BTensor v b ms))
    -> BTensor v b (ns ++ [n,m])
    -> f (BTensor v b (ns ++ ms))
traverseBase = \case
    LZ -> \lM f -> \case
      BTM x  -> f x
    LS l -> \lM f -> \case
      BTV xs -> undefined
      BTM xs -> undefined
      BTN xs -> fmap (btn (l `TCL.append'` lM))
              . vITraverse (\_ -> traverseBase l lM f)
              $ xs

imapBase
    :: forall k (v :: k -> Type -> Type) ns n m ms os b. Vec v
    => Length ns
    -> Length ms
    -> (Prod (IndexN k) ns -> b (BM n m) -> BTensor v b ms)
    -> BTensor v b (ns ++ [n,m])
    -> BTensor v b (ns ++ ms)
imapBase lN lM f = getI . itraverseBase lN lM (\i -> I . f i)

itraverseBase
    :: forall k (v :: k -> Type -> Type) ns n m ms os b f. (Applicative f, Vec v)
    => Length ns
    -> Length ms
    -> (Prod (IndexN k) ns -> b (BM n m) -> f (BTensor v b ms))
    -> BTensor v b (ns ++ [n,m])
    -> f (BTensor v b (ns ++ ms))
itraverseBase = \case
    LZ -> \lM f -> \case
      BTM x  -> f Ø x
    LS l -> \lM f -> \case
      -- BTN xs -> fmap BTN . vITraverse (\i -> itraverseBase l (\is ys -> f (i :< is) ys)) $ xs
      BTV xs -> undefined
      BTM xs -> undefined
      BTN xs -> fmap (btn (l `TCL.append'` lM))
              . vITraverse (\i -> itraverseBase l lM (\is ys -> f (i :< is) ys))
              $ xs

btn :: Length ns
    -> v n (BTensor v b ns)
    -> BTensor v b (n ': ns)
btn = \case
    LZ        -> \x -> BTV undefined
    LS LZ     -> \x -> BTM undefined
    LS (LS l) -> BTN


-- nIxRows = \case
--     LZ   -> \f -> fmap NØ . f Ø
--     LS l -> \f -> \case
--       NS (xs :: v j (Nested v js a)) ->
--         fmap NS . vITraverse (\i -> nIxRows l (\is ys -> f (i :< is) ys)) $ xs


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


