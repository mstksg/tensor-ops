module Data.Type.Combinator.Util where

import           Data.Type.Combinator
import           Data.Distributive

instance Distributive I where
    distribute x = I $ getI <$> x
