{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module TensorOps.BLAS where

import           Control.Applicative
import           Data.Finite
import           Data.Kind
import           Data.Monoid
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
import qualified Data.Type.Vector               as TCV

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
    -- liftB
    --     :: (TCV.Vec n (ElemB b) -> ElemB b)
    --     -> TCV.Vec n (b s)
    --     -> b s
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
    zero :: b s
    zipB
        :: (ElemB b -> ElemB b -> ElemB b)
        -> b s
        -> b s
        -> b s
    -- konstB :: ElemB b -> b s
    traceB
        :: b ('BM n n)
        -> ElemB b

elemsB
    :: (Applicative f, BLAS b)
    => (ElemB b -> f (ElemB b))
    -> b s
    -> f (b s)
elemsB f = iElemsB (\_ x -> f x)

bgen
    :: forall k (b :: BShape k -> Type) (s :: BShape k). BLAS b
    => (Prod (IndexN k) (BShapeDims s) -> ElemB b)
    -> b s
bgen f = getI $ bgenA (I . f)

-- mapB
--     :: BLAS b
--     => (ElemB b -> ElemB b)
--     -> b s
--     -> b s
-- mapB f = liftB (f . getI . TCV.head') . (TCV.:* TCV.ØV) . I

data BTensor :: (k -> Type -> Type) -> (BShape k -> Type) -> [k] -> Type where
    BTS :: !(ElemB b)     -> BTensor v b '[]
    BTV :: !(b ('BV n))   -> BTensor v b '[n]
    BTM :: !(b ('BM n m)) -> BTensor v b '[n,m]
    BTN :: !(v n (BTensor v b (o ': m ': ns)))
        -> BTensor v b (n ': o ': m ': ns)

instance (BLAS b, Vec v, Nesting1 Proxy Functor v, Nesting1 Sing Applicative v, SingI ns, Num (ElemB b))
        => Num (BTensor v b ns) where
    (+) = zipBase sing (+) (\xs ys -> axpy 1 xs (Just ys)) (\xs ys -> gemm 1 xs eye (Just (1, ys)))
    (-) = zipBase sing (-) (\xs ys -> axpy (-1) ys (Just xs)) (\xs ys -> gemm 1 xs eye (Just (-1, ys)))
    (*) = zipBTensorElems sing (*)
    negate = mapBase negate (\xs -> axpy (-1) xs Nothing) (\xs -> gemm 1 xs eye Nothing)
    abs    = mapBTensorElems abs
    signum = mapBTensorElems signum
    fromInteger i = genBTensor sing $ \_ -> fromInteger i

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
    :: forall k (b :: BShape k -> Type) ms os ns v.
     ( Floating (ElemB b)
     , BLAS b
     , Vec v
     , Nesting1 Proxy Functor     v
     , Nesting1 Sing  Applicative v
     )
    => Length ms
    -> Length os
    -> MaxLength N1 ns
    -> BTensor v b (ms         ++ os)
    -> BTensor v b (Reverse os ++ ns)
    -> BTensor v b (ms         ++ ns)
gmulBLAS lM lO mlN v r = case splittingEnd (S_ (S_ Z_)) (lengthProd lO) of
    FewerEnd MLZ             _ -> gmulBLAS' lM MLZ       mlN v r
    FewerEnd (MLS MLZ)       _ -> gmulBLAS' lM (MLS MLZ) mlN v r
    FewerEnd (MLS (MLS MLZ)) _ -> case mlN of
      MLZ -> case r of
        BTM ys -> mapBTM lM LZ (\xs -> BTS $ traceB (gemm 1 xs ys Nothing)) v
      MLS MLZ -> case r of
        BTN ys -> undefined
    SplitEnd (ELS (ELS ELZ) :: ExactLength N2 os1) plO0 plO1 -> case mlN of
      MLZ -> let f  :: (os1 ~ BShapeDims s)
                    => Prod (IndexN k) qs
                    -> b s
                    -> BTensor v b '[]
                 f is = undefined
             in  mapRows lM LZ (getSum . ifoldMapBTM (prodLength plO0) (\i -> Sum . f i)) v

-- imapBTM
--     :: forall k (v :: k -> Type -> Type) ns n m ms os b. Vec v
--     => Length ns
--     -> Length ms
--     -> (Prod (IndexN k) ns -> b (BM n m) -> BTensor v b ms)
--     -> BTensor v b (ns ++ [n,m])
--     -> BTensor v b (ns ++ ms)
-- imapBTM lN lM f = getI . itraverseBTM lN lM (\i -> I . f i)


    -- :: forall k (v :: k -> Type -> Type) ns n m ms os b. Vec v
    -- => Length ns
    -- -> Length ms
    -- -> (b (BM n m) -> BTensor v b ms)
    -- -> BTensor v b (ns ++ [n,m])
    -- -> BTensor v b (ns ++ ms)
    -- SplitEnd (ELS ELZ) plO0 plO1 -> case splittingEnd (S_ (S_ Z_)) (lengthProd lM) of
    --   FewerEnd mlM _ -> undefined

-- gmulBLAS lM lO mlN v r = case lO of
--     MLZ -> case splittingEnd (S_ (S_ Z_)) (lengthProd lM) of
--       FewerEnd MLZ             _ -> dispatchBLAS MLZ       mlO  mlN v r
--       FewerEnd (MLS MLZ)       _ -> dispatchBLAS (MLS MLZ) mlO mlN v r
--       FewerEnd (MLS (MLS MLZ)) _ -> case v of
--         BTM xs -> case mlN of
--           MLZ     -> case r of
--             BTS y  -> BTM $ gemm y xs eye Nothing
--           MLS MLZ -> case r of
--             BTV ys -> undefined
--       SplitEnd (ELS (ELS ELZ)) lM0 lM1@(Proxy :< Proxy :< Ø) -> case mlN of
--         MLZ -> case r of
--           BTS y -> mapBTM (prodLength lM0) (prodLength lM1) (\xs -> BTM $ gemm y xs eye Nothing) v
--                      \\ appendNil lM
--         MLS MLZ -> case r of
--           BTV ys -> undefined
--     MLS MLZ -> case splittingEnd (S_ Z_) (lengthProd lM) of
--       FewerEnd mlM _ -> dispatchBLAS mlM mlO mlN v r
--       SplitEnd (ELS ELZ) plM0 plM1 -> case mlN of
--         MLZ -> case r of
--           BTV ys -> let lM0 = prodLength plM0
--                         lM1 = prodLength plM1
--                     in  mapBTM lM0 lM1 (\xs -> BTV $ gemv 1 xs ys Nothing) v
--                           \\ appendNil lM
--                           \\ appendAssoc (TCL.tail' lM0)
--                                          lM1
--                                          (LS LZ :: Length os)


gmulBLAS'
    :: forall b ms os ns v. (Floating (ElemB b), BLAS b, Vec v)
    => Length ms
    -> MaxLength N1 os
    -> MaxLength N1 ns
    -> BTensor v b (ms         ++ os)
    -> BTensor v b (Reverse os ++ ns)
    -> BTensor v b (ms         ++ ns)
gmulBLAS' lM mlO mlN v r = case mlO of
    MLZ -> case splittingEnd (S_ (S_ Z_)) (lengthProd lM) of
      FewerEnd MLZ             _ -> dispatchBLAS MLZ       mlO  mlN v r
      FewerEnd (MLS MLZ)       _ -> dispatchBLAS (MLS MLZ) mlO mlN v r
      FewerEnd (MLS (MLS MLZ)) _ -> case v of
        BTM xs -> case mlN of
          MLZ     -> case r of
            BTS y  -> BTM $ gemm y xs eye Nothing
          MLS MLZ -> case r of
            BTV ys -> undefined
      SplitEnd (ELS (ELS ELZ)) plM0 plM1 -> case mlN of
        MLZ -> case r of
          BTS y -> mapBTM (prodLength plM0)
                           (prodLength plM1)
                           (\xs -> BTM $ gemm y xs eye Nothing)
                           v
                     \\ appendNil lM
        MLS MLZ -> case r of
          BTV ys -> undefined
    MLS MLZ -> case splittingEnd (S_ Z_) (lengthProd lM) of
      FewerEnd mlM       _         -> dispatchBLAS mlM mlO mlN v r
      SplitEnd (ELS ELZ) plM0 plM1 -> case mlN of
        MLZ -> case r of
          BTV ys -> let lM0 = prodLength plM0
                        lM1 = prodLength plM1
                    in  mapBTM lM0 lM1 (\xs -> BTV $ gemv 1 xs ys Nothing) v
                          \\ appendNil lM
                          \\ appendAssoc (TCL.tail' lM0)
                                         lM1
                                         (LS LZ :: Length os)

mapRows
    :: forall k (v :: k -> Type -> Type) ns ms os a b. Vec v
    => Length ns
    -> Length os
    -> (BTensor v b ms -> BTensor v b os)
    -> BTensor v b (ns ++ ms)
    -> BTensor v b (ns ++ os)
mapRows lN lO f = getI . bRows lN lO (I . f)


bRows
    :: forall k (v :: k -> Type -> Type) ns ms os a b f. (Applicative f, Vec v)
    => Length ns
    -> Length os
    -> (BTensor v b ms -> f (BTensor v b os))
    -> BTensor v b (ns ++ ms)
    -> f (BTensor v b (ns ++ os))
bRows lN lO f = bIxRows lN lO (\_ -> f)

mapIxRows
    :: forall k (v :: k -> Type -> Type) ns ms os a b. Vec v
    => Length ns
    -> Length os
    -> (Prod (IndexN k) ns -> BTensor v b ms -> BTensor v b os)
    -> BTensor v b (ns ++ ms)
    -> BTensor v b (ns ++ os)
mapIxRows lN lO f = getI . bIxRows lN lO (\i -> I . f i)

foldMapIxRows
    :: forall k (v :: k -> Type -> Type) ns ms m os a b. (Vec v, Monoid m)
    => Length ns
    -> (Prod (IndexN k) ns -> BTensor v b ms -> m)
    -> BTensor v b (ns ++ ms)
    -> m
foldMapIxRows l f = getConst . bIxRows l LZ (\i -> Const . f i)

bIxRows
    :: forall k (v :: k -> Type -> Type) ns ms os a b f. (Applicative f, Vec v)
    => Length ns
    -> Length os
    -> (Prod (IndexN k) ns -> BTensor v b ms -> f (BTensor v b os))
    -> BTensor v b (ns ++ ms)
    -> f (BTensor v b (ns ++ os))
bIxRows = \case
    LZ   -> \_  f -> f Ø
    LS l -> \lO f -> \case
      BTV xs -> undefined
      BTM xs -> undefined
      BTN xs -> fmap (btn (l `TCL.append'` lO))
              . vITraverse (\i -> bIxRows l lO (\is -> f (i :< is)))
              $ xs

mapBTensorElems
    :: (Vec v, BLAS b)
    => (ElemB b -> ElemB b)
    -> BTensor v b ns
    -> BTensor v b ns
mapBTensorElems f = getI . bTensorElems (I . f)

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

zipBTensorElems
    :: forall v b ns. (BLAS b, Nesting1 Sing Applicative v)
    => Sing ns
    -> (ElemB b -> ElemB b -> ElemB b)
    -> BTensor v b ns
    -> BTensor v b ns
    -> BTensor v b ns
zipBTensorElems = \case
    SNil -> \f -> \case
      BTS x -> \case
        BTS y -> BTS (f x y)
    _ `SCons` SNil -> \f -> \case
      BTV xs -> \case
        BTV ys -> BTV (zipB f xs ys)
    _ `SCons` (_ `SCons` SNil) -> \f -> \case
      BTM xs -> \case
        BTM ys -> BTM (zipB f xs ys)
    (s :: Sing k) `SCons` ss@(_ `SCons` (_ `SCons` _)) -> \f -> \case
      BTN xs -> \case
        BTN ys -> BTN (zipBTensorElems ss f <$> xs <*> ys)
                    \\ (nesting1 s :: Wit (Applicative (v k)))

mapBTM
    :: forall k (v :: k -> Type -> Type) ns n m ms os b. Vec v
    => Length ns
    -> Length ms
    -> (b ('BM n m) -> BTensor v b ms)
    -> BTensor v b (ns ++ [n,m])
    -> BTensor v b (ns ++ ms)
mapBTM lN lM f = getI . traverseBTM lN lM (I . f)

foldMapBTM
    :: (Monoid a, Vec v)
    => Length ns
    -> (b ('BM n m) -> a)
    -> BTensor v b (ns ++ [n,m])
    -> a
foldMapBTM l f = ifoldMapBTM l (\_ -> f)

traverseBTM
    :: forall k (v :: k -> Type -> Type) ns n m ms os b f. (Applicative f, Vec v)
    => Length ns
    -> Length ms
    -> (b ('BM n m) -> f (BTensor v b ms))
    -> BTensor v b (ns ++ [n,m])
    -> f (BTensor v b (ns ++ ms))
traverseBTM = \case
    LZ -> \lM f -> \case
      BTM x  -> f x
    LS l -> \lM f -> \case
      BTV xs -> undefined
      BTM xs -> undefined
      BTN xs -> fmap (btn (l `TCL.append'` lM))
              . vITraverse (\_ -> traverseBTM l lM f)
              $ xs

imapBTM
    :: forall k (v :: k -> Type -> Type) ns n m ms os b. Vec v
    => Length ns
    -> Length ms
    -> (Prod (IndexN k) ns -> b ('BM n m) -> BTensor v b ms)
    -> BTensor v b (ns ++ [n,m])
    -> BTensor v b (ns ++ ms)
imapBTM lN lM f = getI . itraverseBTM lN lM (\i -> I . f i)

ifoldMapBTM
    :: (Vec v, Monoid a)
    => Length ns
    -> (Prod (IndexN k) ns -> b (BM n m) -> a)
    -> BTensor v b (ns ++ [n,m])
    -> a
ifoldMapBTM = \case
    LZ -> \f -> \case
      BTM xs -> f Ø xs
    LS l -> \f -> \case
      BTN xs -> vIFoldMap (\i -> ifoldMapBTM l (\is -> f (i :< is))) xs

itraverseBTM
    :: forall k (v :: k -> Type -> Type) ns n m ms os b f. (Applicative f, Vec v)
    => Length ns
    -> Length ms
    -> (Prod (IndexN k) ns -> b (BM n m) -> f (BTensor v b ms))
    -> BTensor v b (ns ++ [n,m])
    -> f (BTensor v b (ns ++ ms))
itraverseBTM = \case
    LZ -> \lM f -> \case
      BTM x  -> f Ø x
    LS l -> \lM f -> \case
      BTV xs -> undefined
      BTM xs -> undefined
      BTN xs -> fmap (btn (l `TCL.append'` lM))
              . vITraverse (\i -> itraverseBTM l lM (\is ys -> f (i :< is) ys))
              $ xs

mapBase
    :: forall v b ns. (Nesting1 Proxy Functor v)
    => (ElemB b -> ElemB b)
    -> (forall n. b ('BV n) -> b ('BV n))
    -> (forall n m. b ('BM n m) -> b ('BM n m))
    -> BTensor v b ns
    -> BTensor v b ns
mapBase f g h = \case
    BTS x  -> BTS (f x)
    BTV xs -> BTV (g xs)
    BTM xs -> BTM (h xs)
    BTN (xs :: v k (BTensor v b (n ': m ': os))) -> BTN (mapBase f g h <$> xs)
                \\ (nesting1 Proxy :: Wit (Functor (v k)))

zipBase
    :: forall v b ns. (Nesting1 Sing Applicative v)
    => Sing ns
    -> (ElemB b -> ElemB b -> ElemB b)
    -> (forall n. b ('BV n) -> b ('BV n) -> b ('BV n))
    -> (forall n m. b ('BM n m) -> b ('BM n m) -> b ('BM n m))
    -> BTensor v b ns
    -> BTensor v b ns
    -> BTensor v b ns
zipBase = \case
    SNil -> \f _ _ -> \case
      BTS x -> \case
        BTS y -> BTS (f x y)
    _ `SCons` SNil -> \_ g _ -> \case
      BTV xs -> \case
        BTV ys -> BTV (g xs ys)
    _ `SCons` (_ `SCons` SNil) -> \_ _ h -> \case
      BTM xs -> \case
        BTM ys -> BTM (h xs ys)
    (s :: Sing k) `SCons` ss@(_ `SCons` (_ `SCons` _)) -> \f g h -> \case
      BTN xs -> \case
        BTN ys -> BTN $ zipBase ss f g h <$> xs <*> ys
                    \\ (nesting1 s :: Wit (Applicative (v k)))

genBTensorA
    :: forall k (b :: BShape k -> Type) v (ns :: [k]) f. (Applicative f, BLAS b, Vec v)
    => Sing ns
    -> (Prod (IndexN k) ns -> f (ElemB b))
    -> f (BTensor v b ns)
genBTensorA = \case
    SNil                                   -> \f ->
        BTS <$> f Ø
    _ `SCons` SNil                         -> \f ->
        BTV <$> bgenA f
    _ `SCons` (_ `SCons` SNil)             -> \f ->
        BTM <$> bgenA f
    s `SCons` ss@(_ `SCons` (_ `SCons` _)) -> \f ->
        BTN <$> vGenA s (\i -> genBTensorA ss (\is -> f (i :< is)))

genBTensor
    :: forall k (b :: BShape k -> Type) v (ns :: [k]). (BLAS b, Vec v)
    => Sing ns
    -> (Prod (IndexN k) ns -> ElemB b)
    -> BTensor v b ns
genBTensor s f = getI $ genBTensorA s (I . f)

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


