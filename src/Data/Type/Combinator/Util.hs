{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE StandaloneDeriving         #-}

module Data.Type.Combinator.Util where

import           Data.Type.Combinator
import           Data.Distributive

instance Distributive I where
    distribute x = I $ getI <$> x


newtype Flip2 p b a c where
    Flip2 :: { getFlip2 :: p a b c }
          -> Flip2 p b a c

deriving instance Functor (p a b) => Functor (Flip2 p b a)
deriving instance Applicative (p a b) => Applicative (Flip2 p b a)
deriving instance Traversable (p a b) => Traversable (Flip2 p b a)
deriving instance Foldable (p a b) => Foldable (Flip2 p b a)
deriving instance Show (p a b c) => Show (Flip2 p b a c)
deriving instance Num (p a b c) => Num (Flip2 p b a c)
