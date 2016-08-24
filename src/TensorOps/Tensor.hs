{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

module TensorOps.Tensor where

import           Data.Singletons.Prelude.List
import           Data.Type.Product
import           Data.Type.Uniform
import           TensorOps.Types

mulChain
    :: Tensor t
    => MatMatChain n ns m
    -> Prod t ns
    -> t '[n,m]
mulChain = \case
    MMØ -> \case
      Ø -> eye (US (US UØ))
    MMS mm -> \case
      x :< xs -> x `mulMM` mulChain mm xs

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

