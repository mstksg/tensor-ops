{-# LANGUAGE PolyKinds     #-}
{-# LANGUAGE RankNTypes    #-}
{-# LANGUAGE TypeOperators #-}

module Type.Class.Higher.Util where

import           Control.Monad
import           Data.Monoid
import           Type.Class.Witness
import           Type.Class.Higher

traverse1_
    :: (Foldable1 t, Applicative h)
    => (forall a. f a -> h c)
    -> t f b
    -> h ()
traverse1_ f = ($ pure ()) . appEndo . foldMap1 (Endo . (<*) . void . f)

mapM1_
    :: (Foldable1 t, Applicative h)
    => (forall a. f a -> h c)
    -> t f b
    -> h ()
mapM1_ = traverse1_

forM1_
    :: (Foldable1 t, Applicative h)
    => t f b
    -> (forall a. f a -> h c)
    -> h ()
forM1_ x f = mapM1_ f x

all1
    :: Foldable1 t
    => (forall a. f a -> Bool)
    -> t f b
    -> Bool
all1 p = getAll . foldMap1 (All . p)

produceEq1 :: Eq1 f :- Eq (f a)
produceEq1 = Sub undefined

-- data EqDic :: a
