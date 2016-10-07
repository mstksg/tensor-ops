{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE StandaloneDeriving         #-}

module Data.Type.Combinator.Util where

import           Control.DeepSeq
import           Data.Distributive
import           Data.Type.Combinator
import           GHC.Generics

instance Distributive I where
    distribute x = I $ getI <$> x


newtype Flip2 p b a c where
    Flip2 :: { getFlip2 :: p a b c }
          -> Flip2 p b a c

deriving instance                        Generic (Flip2 p b a c)
deriving instance Functor (p a b)     => Functor (Flip2 p b a)
deriving instance Applicative (p a b) => Applicative (Flip2 p b a)
deriving instance Foldable (p a b)    => Foldable (Flip2 p b a)
deriving instance Traversable (p a b) => Traversable (Flip2 p b a)
deriving instance Show (p a b c)      => Show (Flip2 p b a c)
deriving instance Num (p a b c)       => Num (Flip2 p b a c)

instance NFData (p a b c) => NFData (Flip2 p b a c)

deriving instance Generic (I a)
instance NFData a => NFData (I a)

instance Distributive (p a b) => Distributive (Flip2 p b a) where
    distribute = Flip2 . distribute . fmap getFlip2
