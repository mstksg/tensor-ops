{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

module TensorOps.Tensor where

-- import           Data.Singletons.Prelude.List
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
--       x :< xs -> x `outer` (outerChain sNs xs)

    -- (sN :: Sing n) `SCons` (sNs :: Sing ns') -> \case
    --   (x :: t n) :< (xs :: Prod t ns') ->
    --     let sNsc :: Sing (Concat ns')
    --         sNsc = sConcat sNs
    --         y    :: t (Concat ns')
    --         y    = outerChain sNs xs
    --     in  (undefined :: t n -> t (Concat ns') -> t (n :++ Concat ns')) x y
      -- outer sN (sConcat sNs) x (outerChain sNs xs)
      -- x :< xs -> outer sN (sConcat sNs) x (outerChain sNs xs)
