{-# LANGUAGE GADTs                #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Type.SnocProd where

import           Data.Kind
import           Data.Proxy
import           Data.Singletons
import           Data.Singletons.Prelude.Bool
import           Data.Singletons.Prelude.Eq
import           Data.Singletons.Prelude.List hiding (Length, Reverse)
import           Data.Singletons.Prelude.Ord
import           Data.Singletons.TH
import           Data.Type.Length
import           Data.Type.Length.Util               as TCL
import           Data.Type.Product
import           Data.Type.Product.Util
import           Type.Class.Witness
import           Type.Family.List
import           Type.Family.List.Util

data SnocProd :: (a -> Type) -> [a] -> Type where
    ØS   :: SnocProd f '[]
    (:&) :: SnocProd f as -> f a -> SnocProd f (as >: a)

snocProdHelp
    :: forall f as bs. ()
    => Length bs
    -> SnocProd f bs
    -> Length as
    -> Prod f as
    -> SnocProd f (bs ++ as)
snocProdHelp lB sB = \case
    LZ     -> \case
      Ø                -> sB \\ appendNil lB
    LS lA' -> \case
      (x :: f a) :< xs -> snocProdHelp (lB TCL.>: Proxy @a) (sB :& x) lA' xs
                            \\ appendSnoc lB (Proxy @a)
                            \\ appendAssoc lB (LS LZ :: Length '[a]) lA'

snocProd
    :: Prod f as
    -> SnocProd f as
snocProd p = snocProdHelp LZ ØS (prodLength p) p

snocProdLength
    :: SnocProd f as
    -> Length as
snocProdLength = \case
    ØS               -> LZ
    ss :& (_ :: f a) -> snocProdLength ss TCL.>: Proxy @a

snocProdReverse
    :: SnocProd f as
    -> Prod f (Reverse as)
snocProdReverse = \case
    ØS      -> Ø
    ss :& s -> s :< snocProdReverse ss
                 \\ snocReverse (snocProdLength ss) s

reverseSnocProd
    :: Prod f as
    -> SnocProd f (Reverse as)
reverseSnocProd = \case
    Ø       -> ØS
    x :< xs -> reverseSnocProd xs :& x


-- $(singletons [d|
--   data SnocList a = SnocNil | SnocList a :& a
--     deriving (Show, Ord, Eq)
--   |])

-- infixl 5 :&
-- infixl 5 :%&

-- $(singletons [d|
--   listSnocList :: [a] -> SnocList a
--   listSnocList = \case
--       []   -> SnocNil
--       x:xs -> listSnocList xs :& x

--   snocListList :: SnocList a -> [a]
--   snocListList = \case
--       SnocNil -> []
--       xs :& x -> x : snocListList xs
--   |])

-- snocListLength
--     :: Sing ns
--     -> Length (SnocListList ns)
-- snocListLength = \case
--     SSnocNil -> LZ
--     ss :%& _ -> LS (snocListLength ss)

