{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeOperators       #-}

module TensorOps.Run where

import           Data.Singletons
import           Data.Type.Combinator
import           Data.Type.Product hiding (append')
import           Data.Type.Product.Util
import           Data.Type.Sing
import           Data.Type.Uniform
import           TensorOps.Types
import           Type.Class.Witness

runTOp
    :: forall (ns :: [[k]]) (ms :: [[k]]) (t :: [k] -> *).
     ( Tensor t
     , Floating (ElemT t)
     )
    => Sing ns
    -> Sing ms
    -> TOp ns ms
    -> Prod t ns
    -> Prod t ms
runTOp sNs sMs = (\\ witSings sNs) $
                 (\\ witSings sMs) $ \case
    Lift uNs f -> _ . liftT f . prodToVec I uNs
    -- case uMs of
    --                 UØ   -> \_ -> Ø
    --                 US _ -> vecToProd getI uMs . liftT (getVF <$> f) . prodToVec I uNs
    --                           \\ uniformLength uMs
    GMul lM lO lN  -> \case
      x :< y :< Ø -> only (gmul lM lO lN x y)
    Transp _       -> only . transp . head'
    Shuffle i      -> select i
    -- Fold _ f       -> only . foldT f     . head'

runTensorOp
    :: forall t ns ms. (Tensor t, Floating (ElemT t))
    => TensorOp ns ms
    -> Prod t ns
    -> Prod t ms
runTensorOp = \case
    OPØ                 -> id
    Pop sA sB sD o os -> runTensorOp os
                       . overProdInit (singLength sA)
                                      (singLength sD)
                                      (runTOp sA sB o)

    -- OP1 o    -> runTOp o
    -- oL :. oR -> runTensorOp oR . runTensorOp oL
    -- oL :* oR -> overProdSplit known (runTensorOp oL) (runTensorOp oR)
    -- oL :& oR -> uncurry append' . (runTensorOp oL &&& runTensorOp oR)
