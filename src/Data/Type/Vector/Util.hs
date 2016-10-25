{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.Type.Vector.Util where

import           Control.DeepSeq
import           Data.Bifunctor
import           Data.Distributive
import           Data.Foldable
import           Data.Monoid
import           Data.Type.Combinator
import           Data.Type.Conjunction
import           Data.Type.Fin
import           Data.Type.Nat
import           Data.Type.Vector
import           Type.Class.Known
import           Type.Class.Witness
import           Type.Family.Nat
import           Type.Family.Nat.Util

instance (Known Nat n, Distributive f) => Distributive (VecT n f) where
    distribute xs = vgen_ $ \i -> distribute $ index i <$> xs

instance NFData (f a) => NFData (VecT n f a) where
    rnf = \case
      ØV      -> ()
      x :* xs -> x `deepseq` xs `deepseq` ()

splitVec
    :: Nat n
    -> VecT (n + m) f a
    -> (VecT n f a, VecT m f a)
splitVec = \case
    Z_   -> (ØV,)
    S_ n -> \case
      x :* xs -> first (x :*) (splitVec n xs)
{-# INLINE splitVec #-}

zipVecs
    :: (Traversable g, Applicative g, Known Nat n)
    => (VecT m g a -> b)
    -> VecT m g (VecT n g a)
    -> VecT n g b
zipVecs = liftVec
{-# INLINE zipVecs #-}

liftVec
    :: (Applicative f, Traversable g)
    => (VecT m g a -> b)
    -> VecT m g (f a)
    -> f b
liftVec f xs = f <$> sequenceA xs
{-# INLINE liftVec #-}

zipVecsD
    :: (Distributive g, Known Nat n)
    => (VecT m g a -> b)
    -> VecT m g (VecT n g a)
    -> VecT n g b
zipVecsD = liftVecD
{-# INLINE zipVecsD #-}

liftVecD
    :: (Distributive f, Distributive g)
    => (VecT m g a -> b)
    -> VecT m g (f a)
    -> f b
liftVecD f xs = f <$> distribute xs
{-# INLINE liftVecD #-}

curryV
    :: (VecT ('S n) f a -> b)
    -> f a
    -> VecT n f a
    -> b
curryV f x xs = f (x :* xs)
{-# INLINE curryV #-}

curryV'
    :: (Vec ('S n) a -> b)
    -> a
    -> Vec n a
    -> b
curryV' f x xs = f (I x :* xs)
{-# INLINE curryV' #-}

curryV2'
    :: (Vec N2 a -> b)
    -> a -> a -> b
curryV2' f x y = f (I x :* I y :* ØV)
{-# INLINE curryV2' #-}

curryV3'
    :: (Vec N3 a -> b)
    -> a -> a -> a -> b
curryV3' f x y z = f (I x :* I y :* I z :* ØV)
{-# INLINE curryV3' #-}


uncurryV
    :: (f a -> VecT n f a -> b)
    -> VecT ('S n) f a
    -> b
uncurryV f = \case
    x :* xs -> f x xs
{-# INLINE uncurryV #-}

uncurryV'
    :: (a -> Vec n a -> b)
    -> Vec ('S n) a
    -> b
uncurryV' f = \case
    I x :* xs -> f x xs
{-# INLINE uncurryV' #-}

append'
    :: VecT n f a
    -> VecT m f a
    -> VecT (n + m) f a
append' = \case
    ØV -> id
    x :* xs -> (x :*) . append' xs
{-# INLINE append' #-}

vecFunc
    :: Known Nat n
    => (a -> Vec n b)
    -> Vec n (a -> b)
vecFunc f = vgen_ (\i -> I $ index' i . f)
{-# INLINE vecFunc #-}

unVecFunc
    :: Vec n (a -> b)
    -> a
    -> Vec n b
unVecFunc xs x = fmap ($ x) xs
{-# INLINE unVecFunc #-}

vgenA
    :: Applicative g
    => Nat n
    -> (Fin n -> g (f a))
    -> g (VecT n f a)
vgenA = \case
  Z_   -> \_ -> pure ØV
  S_ n -> \f -> (:*) <$> f FZ <*> vgenA n (f . FS)
{-# INLINE vgenA #-}

uniformVec
    :: Eq (f a)
    => VecT ('S m) f a
    -> Maybe (f a)
uniformVec = \case
    x :* xs | getAll (vfoldMap (All . (== x)) xs) -> Just x
            | otherwise                           -> Nothing
{-# INLINE uniformVec #-}

uncons'
    :: VecT ('S n) f a
    -> (f a, VecT n f a)
uncons' (x :* xs) = (x, xs)

len
    :: VecT n f a
    -> Nat n
len = \case
    ØV      -> Z_
    _ :* xs -> S_ (len xs)

select
    :: forall n f a. ()
    => VecT ('S n) f a
    -> VecT ('S n) (f :&: VecT n f) a
select xs0 = go Z_ ØV (len xs0) xs0
  where
    go  :: forall m o. ()
        => Nat m
        -> VecT m f a
        -> Nat ('S o)
        -> VecT ('S o) f a
        -> VecT ('S o) (f :&: VecT (m + o) f) a
    go m xs = \case
      S_ Z_ -> \case
        y :* ØV -> (y :&: xs) :* ØV
                     \\ addZero m
      S_ o@(S_ p) -> \case
        y :* ys -> (y :&: (xs `append'` ys)) :* go (S_ m) (y :* xs) o ys
                     \\ succAssoc m p

sumV
    :: Num a
    => Vec f a
    -> a
sumV = \case
    ØV          -> 0
    xs@(_ :* _) -> foldl1' (+) xs
{-# INLINE sumV #-}

foldl1'
    :: (a -> a -> a)
    -> Vec ('S n) a
    -> a
foldl1' f = \case
    I x :* ØV          -> x
    I x :* ys@(_ :* _) -> foldl' f x ys
{-# INLINE foldl1' #-}
