{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeOperators        #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.Type.Vector.Util where

import           Control.DeepSeq
import           Data.Bifunctor
import           Data.Distributive
import           Data.Monoid
import           Data.Type.Combinator
import           Data.Type.Fin
import           Data.Type.Nat
import           Data.Type.Vector
import           Type.Class.Known
import           Type.Family.Nat

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

uncurryV
    :: (f a -> VecT n f a -> b)
    -> VecT ('S n) f a
    -> b
uncurryV f = \case
    x :* xs -> f x xs
{-# INLINE uncurryV #-}

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
    => VecT m f a
    -> Maybe (f a)
uniformVec = \case
    ØV      -> Nothing
    x :* xs | getAll (vfoldMap (All . (== x)) xs) -> Just x
            | otherwise                           -> Nothing
{-# INLINE uniformVec #-}

