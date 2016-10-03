{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}

module TensorOps.Tensor where

-- import           Data.Singletons.Prelude.List hiding (Length)
-- import           Data.Type.Index
-- import           Data.Type.Product as TCP hiding     (toList)
-- import           Data.Type.Product.Util
-- import           Data.Type.Sing
-- import           Data.Type.Uniform
-- import           Type.Family.Nat.Util
import           Control.Applicative
import           Control.Monad.Trans.State.Strict
import           Control.Monad.Trans.Writer.Strict
import           Data.Functor
import           Data.Kind
import           Data.List hiding                       ((\\), zip)
import           Data.Monoid
import           Data.Proxy
import           Data.Reflection
import           Data.Singletons
import           Data.Type.Combinator
import           Data.Type.Fin
import           Data.Type.Length
import           Data.Type.Nat
import           Data.Type.Vector                       as TCV
import           Data.Type.Vector.Util                  as TCV
import           Numeric.AD
import           Prelude hiding                         (zip)
import           TensorOps.Types
import           Type.Class.Known
import           Type.Class.Witness hiding              (inner, outer)
import           Type.Family.List
import           Type.Family.List.Util
import           Type.Family.Nat
import qualified Numeric.AD.Internal.Reverse            as AD

konst
    :: (Tensor t, Floating (ElemT t), SingI n)
    => ElemT t
    -> t n
konst = getI . TCV.head' . konstN @('S 'Z)
{-# INLINE konst #-}

konstN
    :: forall n o t. (Tensor t, Floating (ElemT t), SingI o, Known Nat n)
    => ElemT t
    -> Vec n (t o)
konstN x = liftT (vrep (I (\ØV -> x))) ØV
{-# INLINE konstN #-}

map
    :: forall k (o :: [k]) (t :: [k] -> Type). (Floating (ElemT t), SingI o, Tensor t)
    => (ElemT t -> ElemT t)
    -> t o
    -> t o
map f = getI . TCV.head' . liftT ((f . getI . TCV.head') :+ ØV) . (:+ ØV)
{-# INLINE map #-}

zip
    :: (Floating (ElemT t), SingI o, Tensor t)
    => (Vec n (ElemT t) -> ElemT t)
    -> Vec n (t o)
    -> t o
zip f = getI . TCV.head' . liftT (f :+ ØV)
{-# INLINE zip #-}

zip2
    :: (Floating (ElemT t), SingI o, Tensor t)
    => (ElemT t -> ElemT t -> ElemT t)
    -> t o
    -> t o
    -> t o
zip2 f x y = zip (\case I x' :* I y' :* ØV -> f x' y') (x :+ y :+ ØV)
{-# INLINE zip2 #-}

zip3
    :: (Floating (ElemT t), SingI o, Tensor t)
    => (ElemT t -> ElemT t -> ElemT t -> ElemT t)
    -> t o
    -> t o
    -> t o
    -> t o
zip3 f x y z = zip (\case I x' :* I y' :* I z' :* ØV -> f x' y' z') (x :+ y :+ z :+ ØV)
{-# INLINE zip3 #-}

-- replicate
--     :: (Tensor t, Floating (ElemT t), SingI o, Known Nat n)
--     => t o
--     -> Vec n (t o)
-- replicate = vrep
-- -- replicate x = liftT (\(x' :* ØV) -> vrep x') (x :+ ØV)

newtype VFunc n a = VF { getVF :: forall s. Reifies s AD.Tape => Vec n (AD.Reverse s a) -> AD.Reverse s a }

-- TODO: this implementation is pretty awful, but I hope there is a better
-- way.
wrapVF
    :: forall m n a. Floating a
    => (forall b. Floating b => Vec m (Vec n b -> b))
    -> Vec m (VFunc n a)
wrapVF fs = flip imap fs $ \i _ -> I (VF (index' i fs))
{-# INLINE wrapVF #-}

-- problem: shouldn't need Sing o if n or m is zero
gradLift
    :: forall o n m t. (Tensor t, Floating (ElemT t), SingI o)
    => (forall a. Floating a => Vec m (Vec n a -> a))
    -> Vec n (t o)    -- ^ inputs
    -> Vec m (t o)    -- ^ d target / d outputs
    -> Vec n (t o)    -- ^ d target / d inputs
gradLift (wrapVF->fs) xs dtdys =
    liftT (vgen_ (\i -> I (uncurry (go i) . splitVec known)))
          (xs `TCV.append'` dtdys)
      \\ xs
  where
    go  :: Fin n
        -> Vec n (ElemT t)
        -> Vec m (ElemT t)
        -> ElemT t
    go i x dtdy = sum $ (vap . liftA2) (\d (VF f) -> d * index' i (grad f x)) dtdy fs

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
    :: forall (t :: [k] -> Type) (m :: k). (Tensor t, SingI '[m], SingI ('[] :: [k]))
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

fromList
    :: (Tensor t, SingI ns)
    => [ElemT t]
    -> Maybe (t ns)
fromList = evalStateT . generateA $ \_ -> StateT uncons

generate
    :: (Tensor t, SingI ns)
    => (IndexT t ns -> ElemT t)
    -> t ns
generate = getI . generateA . fmap I

itoList
    :: Tensor t
    => t ns
    -> [(IndexT t ns, ElemT t)]
itoList = ($ [])
        . appEndo
        . execWriter
        . ixElems (\ix@(_,x) -> tell (Endo (ix:)) $> x)

elems
    :: (Applicative f, Tensor t)
    => (ElemT t -> f (ElemT t))
    -> t ns
    -> f (t ns)
elems f = ixElems (f . snd)

toList
    :: Tensor t
    => t ns
    -> [ElemT t]
toList = ($[])
       . appEndo
       . execWriter
       . elems (\x -> tell (Endo (x:)) $> x)

unScalar
    :: Tensor t
    => t '[]
    -> ElemT t
unScalar = head . toList


