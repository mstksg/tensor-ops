{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeOperators       #-}

module TensorOps.Run where

import           Control.Arrow                ((&&&))
import           Data.Bifunctor
import           Data.Singletons
import           Data.Singletons.Prelude.List
import           Data.Type.Product hiding     (append')
import           TensorOps.Tensor
import           TensorOps.Types

runTOp
    :: (Tensor t, Floating (ElemT t))
    => TOp ns ms
    -> Prod t ns
    -> Prod t ms
runTOp = \case
    Lift uNs uMs f -> liftT uNs uMs f
    MatMat c       -> only . mulChain c
    MatVec         -> \case
      x :< y :< Ø  -> only (x `mulMV` y)
    Outer          -> \case
      x :< y :< Ø  -> only (x `outer` y)
    Transp r is    -> only . transp r is . head'
    Fold f         -> only . foldT f     . head'

runTensorOp
    :: forall t ns ms. (Tensor t, Floating (ElemT t))
    => TensorOp ns ms
    -> Prod t ns
    -> Prod t ms
runTensorOp = \case
    OPØ      -> id
    OP1 o    -> runTOp o
    oL :. oR -> runTensorOp oR . runTensorOp oL
    oL :* oR -> uncurry append'
              . bimap (runTensorOp oL) (runTensorOp oR)
              . splitProd sing
    oL :& oR -> uncurry append'
              . (runTensorOp oL &&& runTensorOp oR)

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
