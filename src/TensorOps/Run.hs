{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeOperators       #-}

module TensorOps.Run where

-- import           Data.Bifunctor
-- import           Data.Functor.Identity
-- import           Data.Singletons
-- import           Data.Singletons.Prelude.List hiding (Length)
-- import           Data.Type.Length
-- import           Data.Type.Uniform
-- import           Type.Class.Known
import           Control.Arrow                          ((&&&))
import           Data.Type.Product hiding               (append')
import           Data.Type.Product.Util
import           TensorOps.Tensor
import           TensorOps.Types

runTOp
    :: (Tensor t, Floating (ElemT t))
    => TOp ns ms
    -> Prod t ns
    -> Prod t ms
runTOp = \case
    Lift uNs uMs f -> liftT uNs uMs f
    GMul lM lO lN  -> \case
      x :< y :< Ø  -> only (gmul lM lO lN x y)
    -- MatMat         -> \case
    --   x :< y :< Ø  -> only (x `mulMM` y)
    -- MatVec         -> \case
    --   x :< y :< Ø  -> only (x `mulMV` y)
    -- Outer          -> \case
    --   x :< y :< Ø  -> only (x `outer` y)
    Transp         -> only . transp . head'
    -- Transp r is    -> only . transp r is . head'
    Fold f         -> only . foldT f     . head'

runTensorOp
    :: forall t ns ms. (Tensor t, Floating (ElemT t))
    => TensorOp ns ms
    -> Prod t ns
    -> Prod t ms
runTensorOp = \case
    OPØ            -> id
    Pop lA lD o os -> runTensorOp os . overProdInit lA lD (runTOp o)

    -- OP1 o    -> runTOp o
    -- oL :. oR -> runTensorOp oR . runTensorOp oL
    -- oL :* oR -> overProdSplit known (runTensorOp oL) (runTensorOp oR)
    -- oL :& oR -> uncurry append' . (runTensorOp oL &&& runTensorOp oR)
