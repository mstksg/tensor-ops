{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Type.Product.Util where

import           Control.DeepSeq
import           Data.Bifunctor
import           Data.Functor.Identity
import           Data.Proxy
import           Data.Type.Combinator
import           Data.Type.Conjunction
import           Data.Type.Equality
import           Data.Type.Index
import           Data.Type.Length
import           Data.Type.Length.Util               as TCL
import           Data.Type.Product     as TCP hiding (reverse')
import           Data.Type.Uniform
import           Data.Type.Vector
import           Prelude hiding                      (replicate)
import           Type.Class.Known
import           Type.Class.Witness
import           Type.Family.List
import           Type.Family.List.Util
import           Type.Family.Nat

instance Every NFData (f <$> as) => NFData (Prod f as) where
    rnf = \case
      Ø       -> ()
      x :< xs -> x `deepseq` xs `deepseq` ()

splitProd
    :: Length ns
    -> Prod f (ns ++ ms)
    -> (Prod f ns, Prod f ms)
splitProd = \case
    LZ   -> \p -> (Ø, p)
    LS l -> \case
      x :< xs -> first (x :<) (splitProd l xs)

takeProd
    :: Length ns
    -> Length ms
    -> Prod f (ns ++ ms)
    -> Prod f ns
takeProd = \case
    LZ   -> \_ _ -> Ø
    LS l -> \lM -> \case
      x :< xs -> x :< takeProd l lM xs

overProdInit
    :: Length ns
    -> Length os
    -> (Prod g ns -> Prod g ms)
    -> Prod g (ns ++ os)
    -> Prod g (ms ++ os)
overProdInit lN lO f = runIdentity . prodInit lN lO (Identity . f)
{-# INLINE overProdInit #-}

prodInit
    :: Functor f
    => Length ns
    -> Length os
    -> (Prod g ns -> f (Prod g ms))
    -> Prod g (ns ++ os)
    -> f (Prod g (ms ++ os))
prodInit lN lO f = case lN of
    LZ     -> \xs -> (`TCP.append'` xs) <$> f Ø
    LS lN' -> \case
      x :< xs -> prodInit lN' lO (\xs' -> f (x :< xs')) xs
{-# INLINE prodInit #-}

overProdSplit
    :: Length ns
    -> (Prod g ns -> Prod g ms)
    -> (Prod g os -> Prod g ps)
    -> Prod g (ns ++ os)
    -> Prod g (ms ++ ps)
overProdSplit lN f g = runIdentity . prodSplit lN (Identity . f) (Identity . g)
{-# INLINE overProdSplit #-}

prodSplit
    :: Applicative f
    => Length ns
    -> (Prod g ns -> f (Prod g ms))
    -> (Prod g os -> f (Prod g ps))
    -> Prod g (ns ++ os)
    -> f (Prod g (ms ++ ps))
prodSplit lN f g = case lN of
    LZ     -> \xs -> TCP.append' <$> f Ø <*> g xs
    LS lN' -> \case
      x :< xs -> prodSplit lN' (\xs' -> f (x :< xs')) g xs
{-# INLINE prodSplit #-}

prodSplit'
    :: Functor f
    => Length ns
    -> ((Prod g ns, Prod g os) -> f (Prod g ms, Prod g ps))
    -> Prod g (ns ++ os)
    -> f (Prod g (ms ++ ps))
prodSplit' lN f = case lN of
    LZ     -> \ys -> uncurry TCP.append' <$> f (Ø, ys)
    LS lN' -> \case
      x :< xs -> prodSplit' lN' (\(xs', ys) -> f (x :< xs', ys)) xs
{-# INLINE prodSplit' #-}

vecToProd
    :: forall a b f g as. ()
    => (f b -> g a)
    -> Uniform a as
    -> VecT (Len as) f b
    -> Prod g as
vecToProd f = go
  where
    go  :: forall bs. ()
        => Uniform a bs
        -> VecT (Len bs) f b
        -> Prod g bs
    go = \case
      UØ    -> \case
        ØV      -> Ø
      US uB -> \case
        x :* xs -> f x :< go uB xs

prodToVec
    :: forall a b as f g. ()
    => (f a -> g b)
    -> Uniform a as
    -> Prod f as
    -> VecT (Len as) g b
prodToVec f = go
  where
    go  :: forall bs. ()
        => Uniform a bs
        -> Prod f bs
        -> VecT (Len bs) g b
    go = \case
      UØ   -> \case
        Ø       -> ØV
      US u -> \case
        x :< xs -> f x :* prodToVec f u xs

unselect
    :: forall as bs f. (Known Length as, Known Length bs)
    => Prod (Index as) bs
    -> Prod f bs
    -> Prod (Maybe :.: f) as
unselect is xs = go indices
  where
    go  :: forall cs. ()
        => Prod (Index as) cs
        -> Prod (Maybe :.: f) cs
    go = \case
      Ø       -> Ø
      j :< js -> Comp ((`TCP.index` xs) <$> findIndex j) :< go js
    findIndex
        :: forall a. ()
        => Index as a
        -> Maybe (Index bs a)
    findIndex i = go' indices is
      where
        go' :: forall cs. ()
            => Prod (Index bs) cs
            -> Prod (Index as) cs
            -> Maybe (Index bs a)
        go' = \case
          Ø       -> \_ -> Nothing
          j :< js -> \case
            k :< ks -> case testEquality i k of
              Just Refl -> Just j
              Nothing   -> go' js ks

replicate
    :: forall a f as. ()
    => f a
    -> Uniform a as
    -> Prod f as
replicate x = go
  where
    go  :: forall bs. ()
        => Uniform a bs
        -> Prod f bs
    go = \case
      UØ   -> Ø
      US u -> x :< go u

zipProd
    :: Prod f as
    -> Prod g as
    -> Prod (f :&: g) as
zipProd = \case
    Ø -> \case
      Ø -> Ø
    x :< xs -> \case
      y :< ys -> (x :&: y) :< zipProd xs ys

zipProd3
    :: Prod f as
    -> Prod g as
    -> Prod h as
    -> Prod (f :&: g :&: h) as
zipProd3 = \case
    Ø -> \case
      Ø -> \case
        Ø -> Ø
    x :< xs -> \case
      y :< ys -> \case
        z :< zs -> (x :&: y :&: z) :< zipProd3 xs ys zs


-- zipProd'
--     :: Every c as
--     => (forall a. c a => f a -> g a -> h a)
--     -> Prod f as
--     -> Prod g as
--     -> Prod h as
-- zipProd' f = \case
--     Ø -> \case
--       Ø -> Ø
--     x :< xs -> \case
--       y :< ys -> f x y :< zipProd xs ys


-- collect
--     :: (Every c as, Every d bs)
--     => Prod (Index as) bs
--     -> Prod f bs
--     -> (forall a b. (c a, d b) => f b -> f a -> f a)
--     -> Prod f as
--     -> Prod f as
-- collect = undefined

-- take
--     :: Length as
--     -> Prod f (as ++ bs)
--     -> Prod f as

-- unSnoc
--     :: forall f a as. ()
--     => Proxy a
--     -> Prod f (as ++ '[ a ])
--     -> Prod f as
-- unSnoc p r = case r of
--     -- '[b] ~ (as >: a)
--     -- '[b] ~ (as ++ '[a])
--     (x :: f b) :< Ø -> Ø
--                -- @(x :< xs) = case xs of
--     -- Ø      -> Ø \\ appendSnoc (prodLength r) (Proxy @a)
--     -- -- _ :< _ -> x :< unSnoc p xs

-- appendAssoc

prodLength
    :: Prod f as
    -> Length as
prodLength = \case
    Ø       -> LZ
    _ :< xs -> LS (prodLength xs)


-- reverse'Help
--     :: forall f as bs. ()
--     => Length as
--     -> Prod f (Reverse as)
--     -> Prod f bs
--     -> Prod f (Reverse bs ++ Reverse as)
-- reverse'Help lA pA = \case
--     Ø                ->
--       pA
--     (x :: f a) :< (xs :: Prod f as') ->
--       reverse'Help (lA TCL.>: Proxy @a) (x :< pA) xs
--         \\ reverseSnoc lA (Proxy @a)
--         \\ appendAssoc (undefined :: Length as') (LS LZ :: Length '[a]) (TCL.reverse' lA)

