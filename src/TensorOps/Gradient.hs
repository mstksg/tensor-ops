module TensorOps.Gradient where

import           TensorOps.Types
import           TensorOps.Run

-- gradTOp
--     :: (Tensor t, Floating (ElemT t))
--     => TOp ns ms
--     -> Prod t ns    -- ^ inputs
--     -> Prod t ms    -- ^ d target / d output
--     -> Prod t ns    -- ^ d target / d input
-- gradTOp = \case
--     Lift uNs uMs f -> liftT uNs uMs f
--     MatMat c       -> only . mulChain c
--     MatVec         -> \case
--       x :< y :< Ø  -> only (x `mulMV` y)
--     Outer          -> \case
--       x :< y :< Ø  -> only (x `outer` y)
--     Transp r is    -> only . transp r is . head'
--     Fold f         -> only . foldT f     . head'
