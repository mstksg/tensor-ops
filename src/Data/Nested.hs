{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Data.Nested where

import           Control.Applicative
import           Data.Kind
import           Data.Singletons
import           Data.Type.Combinator
import           Data.Singletons.Prelude.List hiding (Length)
import           Data.Type.Index
import           Data.Type.Length
import           Data.Type.Product
import           Type.Class.Higher
import           Type.Class.Known
import           Type.Class.Witness
import           Type.Family.List

type family Nest (f :: k -> (Type -> Type) -> Type -> Type)
                 (as :: [k])
              :: Type -> Type where
    Nest f '[]       = I
    Nest f (a ': as) = f a (Nest f as)

class Nesting c v where
    nesting :: Sing a -> Wit (c (v a))

data Nested :: (k -> (Type -> Type) -> Type -> Type) -> [k] -> Type -> Type where
    Nested :: { getNested :: Nest f js a }
           -> Nested f js a

-- data Nested :: (k -> (Type -> Type) -> Type -> Type) -> [k] -> Type -> Type where
--     NØ :: a                   -> Nested v '[]       a
--     NS :: v j (Nested v js) a -> Nested v (j ': js) a

-- deriving instance ListC (Functor <$> (v <$> js))     => Functor (Nested v js)
-- deriving instance ListC (Foldable <$> (v <$> js))    => Foldable (Nested v js)
-- deriving instance (ListC (Functor <$> (v <$> js)), ListC (Traversable <$> (v <$> js)), ListC (Foldable <$> (v <$> js)))
--     => Traversable (Nested v js)

-- instance (Known Length js, ListC (Functor <$> (v <$> js)), ListC (Applicative <$> (v <$> js)))
--             => Applicative (Nested v js) where
--     pure = go known
--       where
--         go  :: ListC (Applicative <$> (v <$> ks))
--             => Length ks
--             -> a
--             -> Nested v ks a
--         go = \case
--           LZ   -> NØ
--           LS l -> NS . pure . go l
--     (<*>) = \case
--       NØ f -> \case
--         NØ x -> NØ (f x)
--       NS fs -> \case
--         NS xs -> NS $ liftA2 (<*>) fs xs


-- instance (SingI js, Nesting Functor v) => Functor (Nested v js) where
--     fmap :: forall a b. (a -> b) -> Nested v js a -> Nested v js b
--     fmap f = go sing
--       where
--         go  :: forall ks. ()
--             => Sing ks
--             -> Nested v ks a
--             -> Nested v ks b
--         go = \case
--           SNil -> \case
--             NØ x  -> NØ (f x)
--           (s :: Sing k) `SCons` ss -> \case
--             NS xs -> NS (fmap (go ss) xs)
--                        \\ nesting @Functor @v @k s

-- instance (SingI js, Functor (Nested v js), Nesting Applicative v) => Applicative (Nested v js) where
--     pure :: forall a. a -> Nested v js a
--     pure x = go sing
--       where
--         go  :: forall ks. ()
--             => Sing ks
--             -> Nested v ks a
--         go = \case
--           SNil                     -> NØ x
--           (s :: Sing k) `SCons` ss -> NS (pure (go ss))
--                                         \\ nesting @Applicative @v @k s
--     (<*>)
--         :: forall a b. ()
--         => Nested v js (a -> b)
--         -> Nested v js a
--         -> Nested v js b
--     (<*>) = go sing
--       where
--         go  :: forall ks. ()
--             => Sing ks
--             -> Nested v ks (a -> b)
--             -> Nested v ks a
--             -> Nested v ks b
--         go = \case
--           SNil -> \case
--             NØ f -> \case
--               NØ x -> NØ (f x)




-- instance Functor (Nested v '[]) where
--     fmap f = \case
--       NØ x -> NØ (f x)

-- instance (Functor (v j), Functor (Nested v js)) => Functor (Nested v (j ': js)) where
--     fmap f = \case
--       NS v -> NS ((fmap.fmap) f v)

-- instance Applicative (Nested v '[]) where
--     pure          = NØ
--     NØ f <*> NØ x = NØ (f x)

-- instance (Applicative (v j), Applicative (Nested v js)) => Applicative (Nested v (j ': js)) where
--     pure          = NS . pure . pure
--     NS f <*> NS x = NS (liftA2 (<*>) f x)

-- instance Foldable (Nested v '[]) where
--     foldMap f = \case
--       NØ x -> f x

-- instance (Foldable (v j), Foldable (Nested v js)) => Foldable (Nested v (j ': js)) where
--     foldMap f = \case
--       NS v -> (foldMap . foldMap) f v

-- instance Traversable (Nested v '[]) where
--     traverse f =
