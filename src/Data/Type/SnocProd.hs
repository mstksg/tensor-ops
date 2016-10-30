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
import           Data.Type.Length
import           Data.Type.Length.Util  as TCL
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
-- TODO: might recomputing snocProdLength be slow?

reverseSnocProd
    :: Prod f as
    -> SnocProd f (Reverse as)
reverseSnocProd = \case
    Ø       -> ØS
    x :< xs -> reverseSnocProd xs :& x

-- | An implementation of reverse' for Prod that runs in O(n) instead of
-- O(n^2)
prodReverse'
    :: Prod f as
    -> Prod f (Reverse as)
prodReverse' = snocProdReverse . snocProd


