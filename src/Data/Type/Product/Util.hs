{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

module Data.Type.Product.Util where

-- import           Data.Singletons.Prelude.List hiding (Length)
import           Data.Bifunctor
import           Data.Functor.Identity
import           Data.Type.Length
import           Data.Type.Product
import           Prelude hiding                         (replicate)
import           Type.Class.Known
import           Type.Family.List

splitProd
    :: Length ns
    -> Prod f (ns ++ ms)
    -> (Prod f ns, Prod f ms)
splitProd = \case
    LZ   -> \p -> (Ø, p)
    LS l -> \case
      x :< xs -> first (x :<) (splitProd l xs)

-- append'
--     :: Prod f as
--     -> Prod f bs
--     -> Prod f (as ++ bs)
-- append' = \case
--     Ø       -> id
--     x :< xs -> (x :<) . append' xs

overProdInit
    :: Length ns
    -> Length os
    -> (Prod g ns -> Prod g ms)
    -> Prod g (ns ++ os)
    -> Prod g (ms ++ os)
overProdInit lN lO f = runIdentity . prodInit lN lO (Identity . f)

prodInit
    :: Functor f
    => Length ns
    -> Length os
    -> (Prod g ns -> f (Prod g ms))
    -> Prod g (ns ++ os)
    -> f (Prod g (ms ++ os))
prodInit lN lO f = case lN of
    LZ     -> \xs -> (`append'` xs) <$> f Ø
    LS lN' -> \case
      x :< xs -> prodInit lN' lO (\xs' -> f (x :< xs')) xs

overProdSplit
    :: Length ns
    -> (Prod g ns -> Prod g ms)
    -> (Prod g os -> Prod g ps)
    -> Prod g (ns ++ os)
    -> Prod g (ms ++ ps)
overProdSplit lN f g = runIdentity . prodSplit lN (Identity . f) (Identity . g)

prodSplit
    :: Applicative f
    => Length ns
    -> (Prod g ns -> f (Prod g ms))
    -> (Prod g os -> f (Prod g ps))
    -> Prod g (ns ++ os)
    -> f (Prod g (ms ++ ps))
prodSplit lN f g = case lN of
    LZ     -> \xs -> append' <$> f Ø <*> g xs
    LS lN' -> \case
      x :< xs -> prodSplit lN' (\xs' -> f (x :< xs')) g xs

prodSplit'
    :: Functor f
    => Length ns
    -> ((Prod g ns, Prod g os) -> f (Prod g ms, Prod g ps))
    -> Prod g (ns ++ os)
    -> f (Prod g (ms ++ ps))
prodSplit' lN f = case lN of
    LZ     -> \ys -> uncurry append' <$> f (Ø, ys)
    LS lN' -> \case
      x :< xs -> prodSplit' lN' (\(xs', ys) -> f (x :< xs', ys)) xs

replicate
    :: forall f as. Known Length as
    => (forall a. f a)
    -> Prod f as
replicate x = case known :: Length as of
                LZ   -> Ø
                LS l -> x :< replicate x


