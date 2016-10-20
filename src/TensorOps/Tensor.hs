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

import           Control.Applicative
import           Control.Monad.Trans.State.Strict
import           Data.Functor
import           Data.Kind
import           Data.List hiding                  ((\\), zip)
import           Data.Monoid
import           Data.Proxy
import           Data.Singletons
import           Data.Type.Combinator
import           Data.Type.Fin
import           Data.Type.Length
import           Data.Type.Product
import           Data.Type.Sing
import           Data.Type.Vector                  as TCV
import           Data.Type.Vector.Util             as TCV
import           Numeric.AD
import           Prelude hiding                    (zip)
import           TensorOps.NatKind
import           TensorOps.Types
import           Type.Class.Known
import           Type.Class.Witness hiding         (inner, outer)
import           Type.Family.List
import           Type.Family.List.Util

konst
    :: (Tensor t, SingI n)
    => ElemT t
    -> t n
konst x = generate (\_ -> x)
{-# INLINE konst #-}

-- konst
--     :: (Tensor t, Floating (ElemT t), SingI n)
--     => ElemT t
--     -> t n
-- konst = getI . TCV.head' . konstN @('S 'Z)
-- {-# INLINE konst #-}

-- konstN
--     :: forall n o t. (Tensor t, Floating (ElemT t), SingI o, Known Nat n)
--     => ElemT t
--     -> Vec n (t o)
-- konstN x = liftT (vrep (I (\ØV -> x))) ØV
-- {-# INLINE konstN #-}

map
    :: forall k (o :: [k]) (t :: [k] -> Type). (SingI o, Tensor t)
    => (ElemT t -> ElemT t)
    -> t o
    -> t o
map f = getI . TCV.head' . liftT ((f . getI . TCV.head') :+ ØV) . (:+ ØV)
{-# INLINE map #-}

zip
    :: (SingI o, Tensor t)
    => (Vec n (ElemT t) -> ElemT t)
    -> Vec n (t o)
    -> t o
zip f = getI . TCV.head' . liftT (f :+ ØV)
{-# INLINE zip #-}

zip2
    :: (SingI o, Tensor t)
    => (ElemT t -> ElemT t -> ElemT t)
    -> t o
    -> t o
    -> t o
zip2 f x y = zip (\case I x' :* I y' :* ØV -> f x' y') (x :+ y :+ ØV)
{-# INLINE zip2 #-}

zip3
    :: (SingI o, Tensor t)
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

-- problem: shouldn't need Sing o if n or m is zero
gradLift
    :: forall o n m t. (Tensor t, Floating (ElemT t), SingI o)
    => Vec m (VFunc n)
    -> Vec n (t o)    -- ^ inputs
    -> Vec m (t o)    -- ^ d target / d outputs
    -> Vec n (t o)    -- ^ d target / d inputs
gradLift fs xs dtdys =
    liftT (vgen_ (\i -> I (uncurry (go i) . splitVec known)))
          (xs `TCV.append'` dtdys)
      \\ xs
  where
    go  :: Fin n
        -> Vec n (ElemT t)
        -> Vec m (ElemT t)
        -> ElemT t
    go i x dtdy = sum $ (vap . liftA2) (\d (VF f) -> d * index' i (grad f x)) dtdy fs
    {-# INLINE go #-}
{-# INLINE gradLift #-}
-- TODO: having to use index' is the downside of the special new form for
-- lifted functions.  but i guess it's just as bad as before because the
-- implementation of liftT would have index''d everything anyways.

inner
    :: forall t ms ns o. (Tensor t, SingI (o ': ns), SingI (ms ++ ns))
    => Length ms
    -> Length ns
    -> t (ms >: o)
    -> t (o ': ns)
    -> t (ms ++ ns)
inner lM lN x = gmul lM (LS LZ) lN x
                    \\ appendSnoc lM (Proxy @o)

outer
    :: (Tensor t, SingI ns, SingI (ms ++ ns))
    => Length ms
    -> Length ns
    -> t ms
    -> t ns
    -> t (ms ++ ns)
outer lM lN x = gmul lM LZ lN x
                    \\ appendNil lM

outerV
    :: (Tensor t, SingI '[n], SingI '[m,n])
    => t '[m]
    -> t '[n]
    -> t '[m,n]
outerV = outer (LS LZ) (LS LZ)

dot
    :: forall (t :: [k] -> Type) (m :: k). (Tensor t, SingI '[m])
    => t '[m]
    -> t '[m]
    -> t '[]
dot = inner LZ LZ

matVec
    :: (Tensor t, SingI '[n], SingI '[m])
    => t '[m, n]
    -> t '[n]
    -> t '[m]
matVec = inner (LS LZ) LZ

vecMat
    :: (Tensor t, SingI '[m,n], SingI '[n])
    => t '[m]
    -> t '[m,n]
    -> t '[n]
vecMat = inner LZ (LS LZ)

matMat
    :: (Tensor t, SingI '[n,o], SingI '[m,o])
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
    :: forall k (t :: [k] -> Type) ns. (Tensor t, SingI ns)
    => (Prod (IndexN k) ns -> ElemT t)
    -> t ns
generate = getI . generateA . fmap I

rows
    :: (Tensor t, Applicative f)
    => Length ms
    -> (t ns -> f (t os))
    -> t (ms ++ ns)
    -> f (t (ms ++ os))
rows l f = ixRows l (\_ -> f)

toRows
    :: Tensor t
    => t (n ': ns)
    -> [t ns]
toRows = ($[])
       . appEndo
       . getConst
       . rows (LS LZ) (\xs -> Const $ Endo (xs:))

ixElems
    :: forall k f (t :: [k] -> Type) ns. (Applicative f, Tensor t, SingI ns)
    => (Prod (IndexN k) ns -> ElemT t -> f (ElemT t))
    -> t ns
    -> f (t ns)
ixElems f = (\\ appendNil l) $
    ixRows l $ \i x ->
      konst <$> f i (unScalar (x :: t '[])) :: f (t '[])
  where
    l :: Length ns
    l = singLength sing

elems
    :: (Applicative f, Tensor t, SingI ns)
    => (ElemT t -> f (ElemT t))
    -> t ns
    -> f (t ns)
elems f = ixElems (\_ x -> f x)

itoList
    :: forall k (t :: [k] -> Type) ns. (Tensor t, SingI ns)
    => t ns
    -> [(Prod (IndexN k) ns, ElemT t)]
itoList = ($ [])
        . appEndo
        . getConst
        . ixElems (\i x -> Const $ Endo ((i,x):))

toList
    :: (Tensor t, SingI ns)
    => t ns
    -> [ElemT t]
toList = ($[])
       . appEndo
       . getConst
       . elems (\x -> Const $ Endo (x:))

unScalar
    :: forall t. Tensor t
    => t '[]
    -> ElemT t
unScalar = (! Ø)