{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeOperators        #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.Type.Vector.Util where

import           Data.Bifunctor
import           Data.Distributive
-- import           Data.Type.Combinator.Util ()
import           Data.Type.Nat
import           Data.Type.Vector
import           Type.Class.Known
import           Type.Family.Nat

instance (Known Nat n, Distributive f) => Distributive (VecT n f) where
    distribute xs = vgen_ $ \i -> distribute $ index i <$> xs

splitVec
    :: Nat n
    -> VecT (n + m) f a
    -> (VecT n f a, VecT m f a)
splitVec = \case
    Z_   -> (ØV,)
    S_ n -> \case
      x :* xs -> first (x :*) (splitVec n xs)

zipVecs
    :: (Traversable g, Applicative g, Known Nat n)
    => (VecT m g a -> b)
    -> VecT m g (VecT n g a)
    -> VecT n g b
zipVecs = liftVec

liftVec
    :: (Applicative f, Traversable g)
    => (VecT m g a -> b)
    -> VecT m g (f a)
    -> f b
liftVec f xs = f <$> sequenceA xs

zipVecsD
    :: (Distributive g, Known Nat n)
    => (VecT m g a -> b)
    -> VecT m g (VecT n g a)
    -> VecT n g b
zipVecsD = liftVecD

liftVecD
    :: (Distributive f, Distributive g)
    => (VecT m g a -> b)
    -> VecT m g (f a)
    -> f b
liftVecD f xs = f <$> distribute xs

curryV
    :: (VecT ('S n) f a -> b)
    -> f a
    -> VecT n f a
    -> b
curryV f x xs = f (x :* xs)

uncurryV
    :: (f a -> VecT n f a -> b)
    -> VecT ('S n) f a
    -> b
uncurryV f = \case
    x :* xs -> f x xs

append'
    :: VecT n f a
    -> VecT m f a
    -> VecT (n + m) f a
append' = \case
    ØV -> id
    x :* xs -> (x :*) . append' xs
    
