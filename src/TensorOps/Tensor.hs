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

module TensorOps.Tensor
  ( konst
  , map
  , zipN
  , zip
  , zip3
  , add
  , gradLift
  , inner, outer, outerV, dot, matVec, vecMat, matMat
  , fromList, generate, rows, toRows
  , ixElems, elems, itoList, toList, unScalar
  , oneHot, argMax, argMin
  ) where

import           Control.Applicative
import           Control.Monad.Trans.State.Strict
import           Data.Functor
import           Data.Kind
import           Data.List hiding                 ((\\), zip, map, zip3)
import           Data.Monoid
import           Data.Proxy
import           Data.Semigroup
import           Data.Singletons
import           Data.Type.Combinator
import           Data.Type.Fin
import           Data.Type.Length
import           Data.Type.Product hiding         (toList)
import           Data.Type.Sing
import           Data.Type.Vector                 as TCV
import           Data.Type.Vector.Util            as TCV
import           Prelude hiding                   (zip, map, zip3)
import           TensorOps.NatKind
import           TensorOps.Types
import           Type.Class.Higher
import           Type.Class.Known
import           Type.Class.Witness hiding        (inner, outer, Const)
import           Type.Family.List
import           Type.Family.List.Util

konst
    :: (Tensor t, SingI n)
    => ElemT t
    -> t n
konst x = generate (\_ -> x)
{-# INLINE konst #-}

map
    :: forall k (o :: [k]) (t :: [k] -> Type). (SingI o, Tensor t)
    => (ElemT t -> ElemT t)
    -> t o
    -> t o
map f = getI . TCV.head' . liftT ((f . getI . TCV.head') :+ ØV) . (:+ ØV)
{-# INLINE map #-}

add :: (Tensor t, SingI o)
    => t o -> t o -> t o
add x y = sumT [x,y]
{-# INLINE add #-}

zipN
    :: (SingI o, Tensor t)
    => (Vec n (ElemT t) -> ElemT t)
    -> Vec n (t o)
    -> t o
zipN f = getI . TCV.head' . liftT (f :+ ØV)
{-# INLINE zipN #-}

zip :: (SingI o, Tensor t)
    => (ElemT t -> ElemT t -> ElemT t)
    -> t o
    -> t o
    -> t o
zip f x y = zipN (\case I x' :* I y' :* ØV -> f x' y') (x :+ y :+ ØV)
{-# INLINE zip #-}

zip3
    :: (SingI o, Tensor t)
    => (ElemT t -> ElemT t -> ElemT t -> ElemT t)
    -> t o
    -> t o
    -> t o
    -> t o
zip3 f x y z = zipN (\case I x' :* I y' :* I z' :* ØV -> f x' y' z') (x :+ y :+ z :+ ØV)
{-# INLINE zip3 #-}

-- -- | This is a huge bottleneck, I think?
-- --
-- -- Implementation issue -- shouldn't need Sing o if n or m is zero
-- --
-- gradLift
--     :: forall o n m t. (Tensor t, RealFloat (ElemT t), SingI o)
--     => Vec m (VFunc n)
--     -> Vec n (t o)    -- ^ inputs
--     -> Vec m (t o)    -- ^ d target / d outputs
--     -> Vec n (t o)    -- ^ d target / d inputs
-- gradLift fs xs dtdys =
--     liftT (vgen_ (\i -> I (uncurry (go i) . splitVec known)))
--           (xs `TCV.append'` dtdys)
--       \\ xs
--   where
--     go  :: Fin n
--         -> Vec n (ElemT t)
--         -> Vec m (ElemT t)
--         -> ElemT t
--     go i x dtdy = sumV $ (vap . liftA2) (\d f -> d * index' i (vfGrad f x)) dtdy fs
--     {-# INLINE go #-}
-- {-# INLINE gradLift #-}

-- | viable alternative?
gradLift
    :: forall o n m t. (Tensor t, RealFloat (ElemT t), SingI o)
    => VFunc n
    -> Vec n (t o)    -- ^ inputs
    -> t o            -- ^ d target / d outputs
    -> Vec n (t o)    -- ^ d target / d inputs
gradLift f xs dtdy = (\\ xs) $
    vgen_ $ \i -> TCV.head' $ liftT (I (\case I d :* x -> go i x d) :* ØV)
                                    (I dtdy :* xs)
  where
    go  :: Fin n
        -> Vec n (ElemT t)
        -> ElemT t
        -> ElemT t
    go i x d = d * index' i (vfGrad f x)
    {-# INLINE go #-}
{-# INLINE gradLift #-}


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
{-# LANGUAGE generate #-}

rows
    :: (Tensor t, Applicative f, SingI (ms ++ os))
    => Length ms
    -> Length os
    -> (t ns -> f (t os))
    -> t (ms ++ ns)
    -> f (t (ms ++ os))
rows lM lO f = ixRows lM lO (\_ -> f)
{-# LANGUAGE rows #-}

toRows
    :: (Tensor t, SingI n)
    => t (n ': ns)
    -> [t ns]
toRows = ($[])
       . appEndo
       . getConst
       . rows (LS LZ) LZ (\xs -> Const $ Endo (xs:))
{-# LANGUAGE toRows #-}

ixElems
    :: forall k f (t :: [k] -> Type) ns. (Applicative f, Tensor t, SingI ns)
    => (Prod (IndexN k) ns -> ElemT t -> f (ElemT t))
    -> t ns
    -> f (t ns)
ixElems f = (\\ appendNil l) $
    ixRows l LZ $ \i x ->
      konst <$> f i (unScalar (x :: t '[])) :: f (t '[])
  where
    l :: Length ns
    l = singLength sing

ifoldMapElems
    :: forall k m (t :: [k] -> Type) ns. (Monoid m, Tensor t, SingI ns)
    => (Prod (IndexN k) ns -> ElemT t -> m)
    -> t ns
    -> m
ifoldMapElems f = getConst . ixElems (\i -> Const . f i)
{-# INLINE ifoldMapElems #-}

elems
    :: (Applicative f, Tensor t, SingI ns)
    => (ElemT t -> f (ElemT t))
    -> t ns
    -> f (t ns)
elems f = ixElems (\_ x -> f x)
{-# INLINE elems #-}

itoList
    :: forall k (t :: [k] -> Type) ns. (Tensor t, SingI ns)
    => t ns
    -> [(Prod (IndexN k) ns, ElemT t)]
itoList = ($ [])
        . appEndo
        . getConst
        . ixElems (\i x -> Const $ Endo ((i,x):))
{-# LANGUAGE itoList #-}

toList
    :: (Tensor t, SingI ns)
    => t ns
    -> [ElemT t]
toList = ($[])
       . appEndo
       . getConst
       . elems (\x -> Const $ Endo (x:))
{-# LANGUAGE toList #-}

unScalar
    :: forall t. Tensor t
    => t '[]
    -> ElemT t
unScalar = (! Ø)
{-# LANGUAGE unScalar #-}

oneHot
    :: forall k (t :: [k] -> Type) (n :: k).
     ( Tensor t
     , Eq1 (IndexN k)
     , SingI n
     )
    => ElemT t
    -> ElemT t
    -> IndexN k n
    -> t '[n]
oneHot x y i = generate $ \(j :< Ø) ->
                 if j `eq1` i
                   then x
                   else y
{-# LANGUAGE oneHot #-}

argMax
    :: forall k (t :: [k] -> Type) (n :: k).
     ( SingI n
     , Tensor t
     , Ord (ElemT t)
     , NonZero n
     )
    => t '[n]
    -> IndexN k n
argMax = (\case Arg _ i -> i)
       . getMax
       . option (error "TensorOps.Tensor.argMax: Impossible!") id
       . ifoldMapElems @k @(Option (Max (Arg (ElemT t) (IndexN k n))))
           (\(j :< Ø) x -> Option . Just . Max $ Arg x j)
{-# LANGUAGE argMax #-}

argMin
    :: forall k (t :: [k] -> Type) (n :: k).
     ( SingI n
     , Tensor t
     , Ord (ElemT t)
     , NonZero n
     )
    => t '[n]
    -> IndexN k n
argMin = (\case Arg _ i -> i)
       . getMin
       . option (error "TensorOps.Tensor.argMax: Impossible!") id
       . ifoldMapElems @k @(Option (Min (Arg (ElemT t) (IndexN k n))))
           (\(j :< Ø) x -> Option . Just . Min $ Arg x j)
{-# LANGUAGE argMin #-}
