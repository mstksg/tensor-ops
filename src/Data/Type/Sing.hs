{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Data.Type.Sing where

import           Data.Bifunctor
import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude.List hiding (Length, Reverse, sReverse, Head, (%:++))
import           Data.Type.Index
import           Data.Type.Length
import           Data.Type.Nat
import           Data.Type.Product
import           Data.Type.Uniform
import           Type.Class.Known
import           Type.Class.Witness
import           Type.Family.Constraint
import           Type.Family.List
import           Type.Family.Nat
import           Type.Family.Nat.Util

instance Witness ØC (SingI a) (Sing a) where
    q \\ s = withSingI s q


singLength
    :: Sing ns
    -> Length ns
singLength = \case
    SNil        -> LZ
    _ `SCons` s -> LS (singLength s)

singProd
    :: Sing as
    -> Prod Sing as
singProd = \case
    SNil         -> Ø
    s `SCons` ss -> s :< singProd ss

prodSing
    :: Prod Sing as
    -> Sing as
prodSing = \case
    Ø        -> SNil
    s :< ss -> s `SCons` prodSing ss

splitSing
    :: Length ns
    -> Sing (ns ++ ms)
    -> (Sing ns, Sing ms)
splitSing = \case
    LZ   -> \ss -> (SNil, ss)
    LS l -> \case
      s `SCons` ss -> first (s `SCons`) (splitSing l ss)

singProdNat
    :: forall (as :: [N]). ()
    => Sing as
    -> Prod Nat as
singProdNat = \case
    SNil              -> Ø
    (SN n) `SCons` ns -> n :< singProdNat ns


data instance Sing (n :: N) where
    SN :: { getNat :: !(Nat n) } -> Sing n

instance Known Nat a => SingI (a :: N) where
    sing = SN known

entailNat
    :: forall n. (SingI n :- Known Nat n)
entailNat = Sub $ case (sing :: Sing n) of
                    SN n -> Wit \\ n

singSings
    :: forall ns. ()
    => SingI ns :- ListC (SingI <$> ns)
singSings = Sub (witSings (sing :: Sing ns))

witSings
    :: forall ns. ()
    => Sing ns
    -> Wit (ListC (SingI <$> ns))
witSings = \case SNil         -> Wit
                 s `SCons` ss -> case witSings ss of
                                   Wit -> withSingI s Wit


entailEvery
    :: forall (as :: [k]) (f :: k -> Constraint). ()
    => (forall (a :: k). SingI a :- f a)
    -> (SingI as :- Every f as)
entailEvery e = Sub (go (sing :: Sing as))
  where
    go :: forall bs. ()
       => Sing bs
       -> Wit (Every f bs)
    go = \case
      SNil         -> Wit
      s `SCons` ss -> case go ss of
                        Wit -> withSingI s (Wit \\ (e :: SingI (Head bs) :- f (Head bs)))

singUniform
    :: Uniform a (b ': bs)
    -> (SingI b :- SingI a)
singUniform = \case
    US _ -> Sub Wit

entailSing
    :: forall a b. ()
    => (Sing a -> Sing b)
    -> (SingI a :- SingI b)
entailSing f = Sub $ withSingI (f (sing :: Sing a)) Wit

entailSing2
    :: forall a b c. ()
    => (Sing a -> Sing b -> Sing c)
    -> ((SingI a, SingI b) :- SingI c)
entailSing2 f = Sub $ withSingI (f (sing :: Sing a) (sing :: Sing b)) Wit

singWit
    :: forall a p q t. (p, Witness p q t)
    => (Sing a -> t)
    -> (SingI a :- q)
singWit f = Sub $ Wit \\ f (sing :: Sing a)

infixr 5 %:++

(%:++)
    :: Sing as
    -> Sing bs
    -> Sing (as ++ bs)
(%:++) = \case
    SNil         -> id
    x `SCons` xs -> \ys ->
      x `SCons` (xs %:++ ys)

sReverse
    :: Sing as
    -> Sing (Reverse as)
sReverse = \case
    SNil         -> SNil
    x `SCons` xs -> sReverse xs `sSnoc` x

sSnoc
    :: Sing as
    -> Sing a
    -> Sing (as >: a)
sSnoc = \case
    SNil         -> (`SCons` SNil)
    x `SCons` xs -> (x `SCons`) . (xs `sSnoc`)

sOnly
    :: Sing a
    -> Sing '[a]
sOnly = (`SCons` SNil)
