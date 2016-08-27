{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

module TensorOps.Tensor where

-- import           Data.Singletons.Prelude.List hiding (Length)
-- import           Data.Type.Index
-- import           Data.Type.Length
-- import           Data.Type.Product.Util
import           Control.Applicative
import           Data.Type.Combinator
import           Data.Type.Product                      as TCP
import           Data.Type.Uniform
import           Data.Type.Vector
import           Data.Type.Vector.Util
import           Numeric.AD
import           TensorOps.Types
import           Type.Class.Known
import           Type.Class.Witness
import           Type.Family.Nat
import           Type.Family.Nat.Util

-- mulChain
--     :: Tensor t
--     => MatMatChain n ns m
--     -> Prod t ns
--     -> t '[n,m]
-- mulChain = \case
--     MMØ -> \case
--       Ø -> eye (US (US UØ))
--     MMS mm -> \case
--       x :< xs -> x `mulMM` mulChain mm xs

konst
    :: (Tensor t, Floating (ElemT t))
    => ElemT t
    -> t n
konst = TCP.head' . konstN (US UØ)

konstN
    :: forall n ns t. (Tensor t, Floating (ElemT t))
    => Uniform n ns
    -> ElemT t
    -> Prod t ns
konstN u x = liftT UØ u (\ØV -> vrep (I x) \\ uniformLength u) Ø

-- transpose
--     :: Tensor t
--     => t '[m,n]
--     -> t '[n,m]
-- transpose = transp Refl (IS IZ :< IZ :< Ø)

gradLift
    :: forall o ms ns t. (Tensor t, Floating (ElemT t))
    => Uniform o ns
    -> Uniform o ms
    -- TODO: make less polymorphic, maybe only require Reverse?
    -> (forall a. Floating a => Vec (Len ns) a -> Vec (Len ms) a)
    -> Prod t ns    -- ^ inputs
    -> Prod t ms    -- ^ d target / d outputs
    -> Prod t ns    -- ^ d target / d inputs
gradLift uN uM f xs dtdys =
    liftT (uN `appendUniform` uM) uN
          (uncurry go . splitVec (known \\ lN))
          (xs `append'` dtdys)
      \\ (lN `appendLengths` uniformLength uM)
  where
    lN = uniformLength uN
    go  :: Vec (Len ns) (ElemT t)
        -> Vec (Len ms) (ElemT t)
        -> Vec (Len ns) (ElemT t)
    go x dtdy = sum ((vap . liftA2) (\e -> fmap (e*)) dtdy (jacobian f x)) \\ lN


-- outerChain
--     :: forall t ns. Tensor t
--     => Sing ns
--     -> Prod t ns
--     -> t (Concat ns)
-- outerChain = \case
--     SNil -> \case
--       Ø -> eye UØ
--     sN `SCons` sNs -> \case
--       -- x :< xs -> _ (outer sN x (outerChain sNs xs))
--       x :< xs -> _ x (outerChain sNs xs)
--       -- x :< xs -> outer sN x (outerChain sNs xs)
--       -- x :< xs -> case sConcat sNs of
--       --              (sMs :: Sing ms) -> case outerChain sNs xs of
--       --                (y :: t ms) -> undefined
--       -- case outerChain sNs xs of
--       --              (y :: t ms) -> outer sN

-- outer sN (sConcat sNs) (sN %:++ sConcat sNs) x (outerChain sNs xs)
      -- case outerChain sNs xs of
      --              (y :: t ms) -> outer sN
        -- sM `SCons` sMs -> outer sN _ _ x (outerChain sNs xs)
    -- case sConcat sNs of
      -- SNil -> \case
      --   x :< xs -> outer sN x (outerChain SNil xs)
      -- x :< xs -> case sConcat sNs of
      --   SNil -> undefined

    -- sN `SCons` sNs -> \case
    --   x :< xs -> outer sN x (outerChain sNs xs)

      -- x :< xs -> x `outer` (outerChain sNs xs)

    -- (sN :: Sing n) `SCons` (sNs :: Sing ns') -> \case
    --   (x :: t n) :< (xs :: Prod t ns') ->
    --     let sNsc :: Sing (Concat ns')
    --         sNsc = sConcat sNs
    --         y    :: t (Concat ns')
    --         y    = outerChain sNs xs
    --     in  (undefined :: t n -> t (Concat ns') -> t (n :++ Concat ns')) x y
      -- outer sN (sConcat sNs) x (outerChain sNs xs)
      -- x :< xs -> outer sN (sConcat sNs) x (outerChain sNs xs)

    -- • Could not deduce: (a1 :++ Data.Singletons.Prelude.Base.Let1628040677Go (:++$) '[] as as)
    --                     ~
    --                     (a1 :++ Data.Singletons.Prelude.Base.Let1628040677Go (:++$) '[] (a1 : as) as)

    -- • Found hole:
    --     _ :: t (a1 :++ Data.Singletons.Prelude.Base.Let1628040677Go (:++$) '[] as as)
    --       -> t (a1 :++ Data.Singletons.Prelude.Base.Let1628040677Go (:++$) '[] (a1 : as) as)

