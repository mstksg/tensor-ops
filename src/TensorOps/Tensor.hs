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
-- import           Data.Type.Product                   as TCP
-- import           Data.Type.Product.Util
-- import           Data.Type.Sing
-- import           Data.Type.Uniform
-- import           Type.Family.Nat
import           Control.Applicative
import           Data.Proxy
import           Data.Singletons
import           Data.Type.Combinator
import           Data.Type.Length
import           Data.Type.Nat
import           Data.Type.Vector                       as TCV
import           Data.Type.Vector.Util                  as TCV
import           Numeric.AD
import           TensorOps.Types
import           Type.Class.Known
import           Type.Class.Witness hiding              (inner, outer)
import           Type.Family.List
import           Type.Family.List.Util
import           Type.Family.Nat.Util

konst
    :: (Tensor t, Floating (ElemT t), SingI n)
    => ElemT t
    -> t n
konst = getI . TCV.head' . konstN (S_ Z_)

konstN
    :: forall n o t. (Tensor t, Floating (ElemT t), SingI o)
    => Nat n
    -> ElemT t
    -> Vec n (t o)
konstN n x = liftT (\ØV -> vrep (I x) \\ n) ØV

-- problem: shouldn't need Sing o if n or m is zero
gradLift
    :: forall o n m t. (Tensor t, Floating (ElemT t), SingI o)
       -- TODO: make less polymorphic, maybe only require Reverse?
    => (forall a. Floating a => Vec n a -> Vec m a)
    -> Vec n (t o)    -- ^ inputs
    -> Vec m (t o)    -- ^ d target / d outputs
    -> Vec n (t o)    -- ^ d target / d inputs
gradLift f xs dtdys =
    liftT (uncurry go . splitVec (known \\ xs))
          (xs `TCV.append'` dtdys)
  where
    go  :: Vec n (ElemT t)
        -> Vec m (ElemT t)
        -> Vec n (ElemT t)
    go x dtdy = sum ((vap . liftA2) (\e -> fmap (e*)) dtdy (jacobian f x)) \\ x

inner
    :: forall t ms ns o. (Tensor t, SingI (ms >: o), SingI (o ': ns), SingI (ms ++ ns))
    => Length ms
    -> Length ns
    -> t (ms >: o)
    -> t (o ': ns)
    -> t (ms ++ ns)
inner lM lN x = gmul lM (LS LZ) lN x
                    \\ appendSnoc lM (Proxy @o)

outer
    :: (Tensor t, SingI ms, SingI ns, SingI (ms ++ ns))
    => Length ms
    -> Length ns
    -> t ms
    -> t ns
    -> t (ms ++ ns)
outer lM lN x = gmul lM LZ lN x
                    \\ appendNil lM

outerV
    :: (Tensor t, SingI '[n], SingI '[m], SingI '[m,n])
    => t '[m]
    -> t '[n]
    -> t '[m,n]
outerV = outer (LS LZ) (LS LZ)

dot
    :: forall (t :: [k] -> *) (m :: k). (Tensor t, SingI '[m], SingI ('[] :: [k]))
    => t '[m]
    -> t '[m]
    -> t '[]
dot = inner LZ LZ

matVec
    :: (Tensor t, SingI '[m,n], SingI '[n], SingI '[m])
    => t '[m, n]
    -> t '[n]
    -> t '[m]
matVec = inner (LS LZ) LZ

vecMat
    :: (Tensor t, SingI '[m], SingI '[m,n], SingI '[n])
    => t '[m]
    -> t '[m,n]
    -> t '[n]
vecMat = inner LZ (LS LZ)

matMat
    :: (Tensor t, SingI '[m,n], SingI '[n,o], SingI '[m,o])
    => t '[m,n]
    -> t '[n,o]
    -> t '[m,o]
matMat = inner (LS LZ) (LS LZ)

