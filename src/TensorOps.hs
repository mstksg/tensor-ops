{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

module TensorOps where

-- import           Data.List hiding              ((\\))
-- import           Data.Singletons
-- import           Data.Type.Combinator
-- import           Data.Type.Conjunction
-- import           Data.Type.Index
-- import           Data.Type.Length.Util         as TCL
-- import           Data.Type.Uniform
-- import           TensorOps.Run
-- import           TensorOps.Types
-- import           Type.Class.Higher
-- import           Type.Class.Witness
-- import           Type.Family.List.Util
import           Data.Singletons.Prelude.List     (Sing(..))
import           Data.Type.Length
import           Data.Type.Product  as TCP hiding (select, toList)
import           Data.Type.Product.Util           as TCP
import           Data.Type.Sing
import           TensorOps.Types
import           Type.Family.List
import qualified TensorOps.Tensor                 as TT


runTensorOp
    :: forall t ns ms. (Tensor t, RealFloat (ElemT t))
    => TensorOp ns ms
    -> Prod t ns
    -> Prod t ms
runTensorOp = \case
    OPØ                 -> id
    Pop sA sB sD o os -> runTensorOp os
                       . overProdInit (singLength sA)
                                      (singLength sD)
                                      (runTOp o)

gradTensorOp
    :: forall ns t. (Tensor t, RealFloat (ElemT t))
    => TensorOp ns '[ '[] ]
    -> Prod t ns    -- ^ inputs
    -> Prod t ns    -- ^ d target / d inputs
gradTensorOp = \case
    OPØ            -> \_ -> only $ TT.konst 1
    -- ns ~ a ++ d
    Pop (sA :: Sing a)
        (sB :: Sing b)
        (sD :: Sing d)
        (o  :: TOp a b)
        (os :: OpPipe TOp (b ++ d) '[ '[] ])
                   -> \x -> let lA   :: Length a
                                lA   = singLength sA
                                lB   :: Length b
                                lB   = singLength sB
                                lD   :: Length d
                                lD   = singLength sD
                                y    :: Prod t (b ++ d)
                                y    = overProdInit lA lD
                                                    (runTOp o)
                                                    x
                                dtdy :: Prod t (b ++ d)
                                dtdy = gradTensorOp os y
                                res  :: Prod t (a ++ d)
                                res  = overProdInit lB lD
                                                    (gradTOp o (takeProd lA lD x))
                                                    dtdy
                            in  res
