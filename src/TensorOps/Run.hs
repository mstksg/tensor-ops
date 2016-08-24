{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeOperators       #-}

module TensorOps.Run where

import           Control.Arrow                       ((&&&))
import           Data.Bifunctor
import           Data.Functor.Identity
import           Data.Singletons
import           Data.Singletons.Prelude.List hiding (Length)
import           Data.Type.Length
import           Data.Type.Product hiding            (append')
import           Data.Type.Uniform
import           TensorOps.Tensor
import           TensorOps.Types

runTOp
    :: (Tensor t, Floating (ElemT t))
    => TOp ns ms
    -> Prod t ns
    -> Prod t ms
runTOp = \case
    Lift uNs uMs lO f -> overProdInit (uniformLength uNs) lO (liftT uNs uMs f)
    MatMat c ->
    MatMat  :: MatMatChain n ns m
            -> TOp (ns :++ ms) ( '[n,m] ': ms )
    -- MatMat c          -> only . mulChain c
    -- MatVec            -> \case
    --   x :< y :< Ø     -> only (x `mulMV` y)
    -- Outer             -> \case
    --   x :< y :< Ø     -> only (x `outer` y)
    -- Transp r is       -> only . transp r is . head'
    -- Fold f            -> only . foldT f     . head'

-- runTensorOp
--     :: forall t ns ms. (Tensor t, Floating (ElemT t))
--     => TensorOp ns ms
--     -> Prod t ns
--     -> Prod t ms
-- runTensorOp = \case
--     OPØ      -> id
--     OP1 o    -> runTOp o
--     oL :. oR -> runTensorOp oR . runTensorOp oL
--     oL :* oR -> uncurry append'
--               . bimap (runTensorOp oL) (runTensorOp oR)
--               . splitProd sing
--     oL :& oR -> uncurry append'
--               . (runTensorOp oL &&& runTensorOp oR)

splitProd
    :: Sing ns
    -> Prod f (ns :++ ms)
    -> (Prod f ns, Prod f ms)
splitProd = \case
    SNil         -> \p -> (Ø, p)
    _ `SCons` sNs -> \case
      x :< xs -> case splitProd sNs xs of
                   (xs', ys) -> (x :< xs', ys)

append'
    :: Prod f as
    -> Prod f bs
    -> Prod f (as :++ bs)
append' = \case
    Ø       -> id
    x :< xs -> (x :<) . append' xs

overProdInit
    :: Length ns
    -> Length os
    -> (Prod g ns -> Prod g ms)
    -> Prod g (ns :++ os)
    -> Prod g (ms :++ os)
overProdInit lN lO f = runIdentity . prodInit lN lO (Identity . f)

prodInit
    :: Applicative f
    => Length ns
    -> Length os
    -> (Prod g ns -> f (Prod g ms))
    -> Prod g (ns :++ os)
    -> f (Prod g (ms :++ os))
prodInit lN lO f = case lN of
    LZ     -> \xs -> (`append'` xs) <$> f Ø
    LS lN' -> \case
      x :< xs -> prodInit lN' lO (\xs' -> f (x :< xs')) xs

    -- Ø -> case lM of
    --   LZ -> case lO of
    --     LZ -> pure Ø
    -- x :< xs -> prodInit lM lO (\ys -> _) xs


-- prodSplit
--     :: forall f g ns ms. (Applicative f, SingI ns)
--     => (Prod g ns -> f (Prod g ns))
--     -> (Prod g ms -> f (Prod g ms))
--     -> Prod g (ns :++ ms)
--     -> f (Prod g (ns :++ ms))
-- prodSplit fL fR = case sing :: Sing ns of
--     SNil -> fR
--     _ `SCons` sNs -> \case
--       x :< xs -> prodSplit fL fR
