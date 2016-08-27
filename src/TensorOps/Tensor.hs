{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module TensorOps.Tensor where

-- import           Data.Singletons.Prelude.List hiding (Length)
-- import           Data.Type.Index
-- import           Data.Type.Product.Util
import           Control.Applicative
import           Data.Proxy
import           Data.Type.Combinator
import           Data.Type.Length
import           Data.Type.Product                      as TCP
import           Data.Type.Uniform
import           Data.Type.Vector
import           Data.Type.Vector.Util
import           Numeric.AD
import           TensorOps.Types
import           Type.Class.Known
import           Type.Class.Witness hiding              (inner, outer)
import           Type.Family.List
import           Type.Family.List.Util
import           Type.Family.Nat
import           Type.Family.Nat.Util

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

inner
    :: forall t ms ns o. Tensor t
    => Length ms
    -> Length ns
    -> t (ms >: o)
    -> t (o ': ns)
    -> t (ms ++ ns)
inner lM lN x = gmul lM (LS LZ) lN x
                    \\ appendSnoc lM (Proxy @o)

outer
    :: Tensor t
    => Length ms
    -> Length ns
    -> t ms
    -> t ns
    -> t (ms ++ ns)
outer lM lN x = gmul lM LZ lN x
                    \\ appendNil lM

outerV
    :: Tensor t
    => t '[m]
    -> t '[n]
    -> t '[m,n]
outerV = outer (LS LZ) (LS LZ)

dot
    :: Tensor t
    => t '[m]
    -> t '[m]
    -> t '[]
dot = inner LZ LZ

matVec
    :: Tensor t
    => t '[m, n]
    -> t '[n]
    -> t '[m]
matVec = inner (LS LZ) LZ

vecMat
    :: Tensor t
    => t '[m]
    -> t '[m,n]
    -> t '[n]
vecMat = inner LZ (LS LZ)

matMat
    :: Tensor t
    => t '[m,n]
    -> t '[n,o]
    -> t '[m,o]
matMat = inner (LS LZ) (LS LZ)

