{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveFoldable         #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE DeriveTraversable      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module Data.Nested where

import           Control.Applicative
import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude.List hiding (Length, Reverse, (%:++), sReverse)
import           Data.Type.Combinator
import           Data.Type.Combinator.Util
import           Data.Type.Length                    as TCL
import           Data.Type.Length.Util               as TCL
import           Data.Type.Product
import           Data.Type.Product.Util
import           Data.Type.Sing
import           Data.Type.SnocProd
import           Data.Type.Uniform
import           Type.Class.Witness
import           Type.Family.List
import           Type.Family.List.Util
import           Type.NatKind
import qualified Data.Singletons.TypeLits            as GT
import qualified Data.Type.Nat                       as TCN
import qualified Data.Type.Vector                    as TCV
import qualified Data.Type.Vector.Util               as TCV
import qualified Data.Vector.Sized                   as VS

data Uncons :: (k -> Type -> Type) -> k -> Type -> Type where
    UNil  :: Uncons v (FromNat 0) a
    UCons :: Sing n -> a -> v n a -> Uncons v (Succ n) a

class NatKind k => Vec (v :: k -> Type -> Type) where
    vHead   :: p j -> v (Succ j) a -> a
    vTail   :: v (Succ j) a -> v j a
    vGenA   :: Applicative f => Sing j -> (IndexN k j -> f a) -> f (v j a)
    vIndex  :: IndexN k j -> v j a -> a
    vUncons :: Sing j -> v j a -> Uncons v j a
    vEmpty  :: v (FromNat 0) a
    vCons   :: a -> v j a -> v (Succ j) a
    vITraverse
        :: Applicative f
        => (IndexN k j -> a -> f b)
        -> v j a
        -> f (v j b)

vGen
    :: Vec (v :: k -> Type -> Type)
    => Sing j
    -> (IndexN k j -> a)
    -> v j a
vGen s f = getI $ vGenA s (I . f)

instance Vec (Flip2 VS.VectorT I) where
    vHead _ = getI . VS.head . getFlip2
    vTail = Flip2 . VS.tail . getFlip2
    vGenA = \case
      GT.SNat -> fmap Flip2 . VS.generateA . (fmap I .)
    vIndex i = (VS.!! i) . getFlip2
    vUncons = \case
      GT.SNat -> \case
        Flip2 xs -> case VS.uncons xs of
          VS.VNil           -> UNil
          VS.VCons (I y) ys -> UCons sing y (Flip2 ys)
    vEmpty = Flip2 VS.empty
    vCons x (Flip2 xs) = Flip2 (VS.cons (I x) xs)
    vITraverse f (Flip2 xs) = Flip2 <$> VS.itraverse (\i (I x) -> I <$> f i x) xs

instance Vec (Flip2 TCV.VecT I) where
    vHead _ = getI . TCV.head' . getFlip2
    vTail = Flip2 . TCV.tail' . getFlip2
    vGenA = \case
      SN n -> \f -> Flip2 <$> TCV.vgenA n (fmap I . f)
    vIndex i = TCV.index' i . getFlip2
    vUncons = \case
      SN TCN.Z_ -> \case
        Flip2 TCV.ØV -> UNil
      SN (TCN.S_ n) -> \case
        Flip2 (I x TCV.:* xs) -> UCons (SN n) x (Flip2 xs)
    vEmpty = Flip2 TCV.ØV
    vCons x (Flip2 xs) = Flip2 (I x TCV.:* xs)
    vITraverse f (Flip2 xs) = Flip2 <$> TCV.itraverse (\i (I x) -> I <$> f i x) xs

-- class Nesting (w :: k -> Type) (c :: j -> Constraint) (v :: k -> j -> j) where
--     nesting :: w i -> c a :- c (v i a)

class Nesting1 (w :: k -> Type) (c :: j -> Constraint) (v :: k -> j) where
    nesting1 :: w a -> Wit (c (v a))

instance Functor f => Nesting1 w Functor (Flip2 VS.VectorT f) where
    nesting1 _ = Wit
instance Applicative f => Nesting1 Sing Applicative (Flip2 VS.VectorT f) where
    nesting1 GT.SNat = Wit
instance Foldable f => Nesting1 w Foldable (Flip2 VS.VectorT f) where
    nesting1 _ = Wit
instance Traversable f => Nesting1 w Traversable (Flip2 VS.VectorT f) where
    nesting1 _ = Wit

instance Functor f => Nesting1 w Functor (Flip2 TCV.VecT f) where
    nesting1 _ = Wit
instance Applicative f => Nesting1 Sing Applicative (Flip2 TCV.VecT f) where
    nesting1 (SN n) = Wit \\ n
instance Foldable f => Nesting1 w Foldable (Flip2 TCV.VecT f) where
    nesting1 _ = Wit
instance Traversable f => Nesting1 w Traversable (Flip2 TCV.VecT f) where
    nesting1 _ = Wit


data Nested :: (k -> Type -> Type) -> [k] -> Type -> Type where
    NØ :: a                   -> Nested v '[]       a
    NS :: v j (Nested v js a) -> Nested v (j ': js) a

-- deriving instance ListC (Show <$> ((v <$> js) <&> a)) => Show (Nested v js a)

instance (Num a, Applicative (Nested v js)) => Num (Nested v js a) where
    (+)         = liftA2 (+)
    (*)         = liftA2 (*)
    (-)         = liftA2 (-)
    negate      = fmap negate
    abs         = fmap abs
    signum      = fmap signum
    fromInteger = pure . fromInteger

instance Nesting1 Proxy Functor v => Functor (Nested v js) where
    fmap f = \case
      NØ x  -> NØ (f x)
      NS (xs :: v j (Nested v ks a))
            -> NS $ (fmap.fmap) f xs
                      \\ (nesting1 Proxy :: Wit (Functor (v j)))

instance (SingI js, Nesting1 Sing Applicative v, Nesting1 Proxy Functor v) => Applicative (Nested v js) where
    pure :: forall a. a -> Nested v js a
    pure x = go sing
      where
        go  :: Sing ks
            -> Nested v ks a
        go = \case
          SNil     -> NØ x
          (s :: Sing k) `SCons` ss -> NS (pure (go ss))
                    \\ (nesting1 s :: Wit (Applicative (v k)))
    (<*>) :: forall a b. Nested v js (a -> b) -> Nested v js a -> Nested v js b
    (<*>) = go sing
      where
        go  :: Sing ks
            -> Nested v ks (a -> b)
            -> Nested v ks a
            -> Nested v ks b
        go = \case
          SNil -> \case
            NØ f -> \case
              NØ x -> NØ (f x)
          (s :: Sing k) `SCons` ss -> \case
            NS fs -> \case
              NS xs -> NS $ liftA2 (go ss) fs xs
                              \\ (nesting1 s :: Wit (Applicative (v k)))

instance Nesting1 Proxy Foldable v => Foldable (Nested v js) where
    foldMap f = \case
      NØ x  -> f x
      NS (xs :: v j (Nested v ks a))
            -> (foldMap . foldMap) f xs
                 \\ (nesting1 Proxy :: Wit (Foldable (v j)))

instance (Nesting1 Proxy Functor v, Nesting1 Proxy Foldable v, Nesting1 Proxy Traversable v) => Traversable (Nested v js) where
    traverse f = \case
      NØ x  -> NØ <$> f x
      NS (xs :: v j (Nested v ks a))
            -> NS <$> (traverse . traverse) f xs
                 \\ (nesting1 Proxy :: Wit (Traversable (v j)))


nHead
    :: forall v p j js a. Vec v
    => p j
    -> Nested v (Succ j ': js) a
    -> Nested v js a
nHead p = \case
  NS xs -> vHead p xs

nTail
    :: Vec v
    => Nested v (Succ j ': js) a
    -> Nested v (j ': js) a
nTail = \case
  NS xs -> NS $ vTail xs

unScalar
    :: Nested v '[] a
    -> a
unScalar = \case
  NØ x -> x

unVector
    :: Functor (v j)
    => Nested v '[j] a
    -> v j a
unVector = \case
    NS xs -> unScalar <$> xs

nVector
    :: Functor (v j)
    => v j a
    -> Nested v '[j] a
nVector = NS . fmap NØ

-- genNestedVec
--     :: Vec (v :: k -> Type -> Type)
--     => Sing ns
--     -> (Prod (IndexN k) ns -> a)
--     -> Nested v ns a
-- genNestedVec = \case
--     SNil         -> \f -> NØ (f Ø)
--     s `SCons` ss -> \f -> NS $ vGen s (\i -> genNestedVec ss (f . (i :<)))

genNestedVec
    :: Vec (v :: k -> Type -> Type)
    => Sing ns
    -> (Prod (IndexN k) ns -> a)
    -> Nested v ns a
genNestedVec s f = getI $ genNestedVecA s (I . f)

genNestedVecA
    :: (Vec (v :: k -> Type -> Type), Applicative f)
    => Sing ns
    -> (Prod (IndexN k) ns -> f a)
    -> f (Nested v ns a)
genNestedVecA = \case
    SNil         -> \f -> NØ <$> f Ø
    s `SCons` ss -> \f -> NS <$> vGenA s (\i -> genNestedVecA ss (f . (i :<)))

indexNestedVec
    :: Vec (v :: k -> Type -> Type)
    => Prod (IndexN k) ns
    -> Nested v ns a
    -> a
indexNestedVec = \case
    Ø -> \case
      NØ x  -> x
    i :< is -> \case
      NS xs -> indexNestedVec is (vIndex i xs)

joinNestedVec
    :: forall v ns ms a. Nesting1 Proxy Functor v
    => Nested v ns (Nested v ms a)
    -> Nested v (ns ++ ms) a
joinNestedVec = \case
    NØ x  -> x
    NS (xs :: v j (Nested v js (Nested v ms a))) ->
      NS $ fmap joinNestedVec xs
        \\ (nesting1 Proxy :: Wit (Functor (v j)))

unjoinNestedVec
    :: Nesting1 Proxy Functor v
    => Length ns
    -> Nested v (ns ++ ms) a
    -> Nested v ns (Nested v ms a)
unjoinNestedVec = mapNVecSlices id

mapNVecSlices
    :: forall v ns ms a b. Nesting1 Proxy Functor v
    => (Nested v ms a -> b)
    -> Length ns
    -> Nested v (ns ++ ms) a
    -> Nested v ns b
mapNVecSlices f = \case
    LZ -> NØ . f
    LS l -> \case
      NS (xs :: v j (Nested v js a)) ->
        NS $ mapNVecSlices f l <$> xs
          \\ (nesting1 Proxy :: Wit (Functor (v j)))

reduceTrace
    :: forall ns ms v a.
     ( Num a
     , SingI (Reverse ns ++ ms)
     , Nesting1 Proxy Functor v
     , Nesting1 Proxy Foldable v
     , Nesting1 Sing  Applicative v
     , Vec v
     )
    => Length ns
    -> Length ms
    -> Nested v ns (Nested v (Reverse ns ++ ms) a)
    -> Nested v ms a
reduceTrace lN _ = reduceTraceHelp (reverseSnocProd sN) (prodSing sM)
                     \\ reverseReverse lN
  where
    slN :: SnocLength ns
    slN = snocLength lN
    sN :: Prod Sing (Reverse ns)
    sM :: Prod Sing ms
    (sN, sM) = splitProd (snocLengthReverse slN) (singProd sing)

reduceTraceHelp
    :: forall ns ms v a.
     ( Num a
     , Vec v
     , Nesting1 Proxy Functor     v
     , Nesting1 Proxy Foldable    v
     , Nesting1 Sing  Applicative v
     )
    => SnocProd Sing ns
    -> Sing ms
    -> Nested v ns (Nested v (Reverse ns ++ ms) a)
    -> Nested v ms a
reduceTraceHelp = \case
    ØS -> \_ -> \case
      NØ y -> y
    sNs' :& (sN :: Sing n) -> \sMs x ->
      let lNs' = snocProdLength sNs'
      in  reduceTraceHelp sNs' sMs (mapNVecSlices (f sMs sNs' sN) lNs' x)
            \\ appendSnoc lNs' sN
            \\ snocReverse lNs' sN
  where
    f   :: forall o os. ()
        => Sing ms
        -> SnocProd Sing os
        -> Sing o
        -> Nested v '[o] (Nested v ((o ': Reverse os) ++ ms) a)
        -> Nested v (Reverse os ++ ms) a
    f sm sp so = collapse . diagNV' so . joinNestedVec
                    \\ prodSing (snocProdReverse sp) %:++ sm
      where
        collapse
            :: SingI (Reverse os ++ ms)
            => Nested v (o ': (Reverse os ++ ms)) a
            -> Nested v (Reverse os ++ ms) a
        collapse = \case
          NS xs -> sum xs
                     \\ (nesting1 Proxy :: Wit (Foldable (v o)))

diagNV'
    :: forall v n ns a. (Vec v, Nesting1 Proxy Functor v)
    => Sing n
    -> Nested v (n ': n ': ns) a
    -> Nested v (n ': ns) a
diagNV' s = \case
  NS (xs :: v n (Nested v (n ': ns) a)) -> case vUncons s xs of
    UNil          -> NS vEmpty
    UCons (s' :: Sing n')
          (y :: Nested v (n ': ns) a)
          (ys :: v n' (Nested v (n ': ns) a)) ->
      case nesting1 Proxy :: Wit (Functor (v n')) of
        Wit -> case diagNV' s' (NS (nTail <$> ys)) of
          NS zs -> NS $ vCons (nHead s' y) zs

diagNV
    :: (Vec v, Nesting1 Proxy Functor v)
    => Sing n
    -> Uniform n ms
    -> Nested v (n ': n ': ms) a
    -> Nested v '[n] a
diagNV s = \case
    UØ   -> diagNV' s
    US u -> diagNV s u . diagNV' s

itraverseNestedVec
    :: forall k (v :: k -> Type -> Type) (ns :: [k]) a b f. (Applicative f, Vec v)
    => (Prod (IndexN k) ns -> a -> f b)
    -> Nested v ns a
    -> f (Nested v ns b)
itraverseNestedVec f = \case
    NØ x  -> NØ <$> f Ø x
    NS xs -> NS <$> vITraverse (\i -> itraverseNestedVec (\is -> f (i :< is))) xs

    -- gmul    :: (SingI (ms ++ os), SingI (Reverse os ++ ns), SingI (ms ++ ns))
gmul'
    :: forall ms os ns v a.
     ( Nesting1 Proxy Functor     v
     , Nesting1 Sing  Applicative v
     , Nesting1 Proxy Foldable    v
     , Nesting1 Proxy Traversable v
     , SingI ns
     , SingI (Reverse os)
     , Num a
     )
    => Length ms
    -> Length os
    -> Length ns
    -> Nested v (ms         ++ os) a
    -> Nested v (Reverse os ++ ns) a
    -> Nested v (ms         ++ ns) a
gmul' lM lO _ x y = joinNestedVec $ mapNVecSlices f lM x
  where
    psO :: Prod Sing (Reverse os)
    psO = singProd (sing :: Sing (Reverse os))
    f   :: Nested v os a
        -> Nested v ns a
    f z = squish lO (snocProd psO) z (unjoinNestedVec (TCL.reverse' lO) y)

squish
    :: forall v os ns a.
     ( Num a
     , Nesting1 Proxy Functor     v
     , Nesting1 Sing  Applicative v
     , Nesting1 Proxy Foldable    v
     , Nesting1 Proxy Traversable v
     , SingI ns
     )
    => Length os
    -> SnocProd Sing (Reverse os)
    -> Nested v os a
    -> Nested v (Reverse os) (Nested v ns a)
    -> Nested v ns a
squish lO spO x y = (\\ reverseReverse lO)              $
                    (\\ prodSing (snocProdReverse spO)) $
    sum $ liftA2 (\x' y' -> fmap (x' *) y') x (transposeHelp spO y)

transpose
    :: forall v os a.
     ( Nesting1 Proxy Functor     v
     , Nesting1 Sing  Applicative v
     , Nesting1 Proxy Foldable    v
     , Nesting1 Proxy Traversable v
     )
    => Sing os
    -> Nested v os a
    -> Nested v (Reverse os) a
transpose s = transposeHelp (snocProd (singProd s))

transposeHelp
    :: forall v os a.
     ( Nesting1 Proxy Functor     v
     , Nesting1 Sing  Applicative v
     , Nesting1 Proxy Foldable    v
     , Nesting1 Proxy Traversable v
     )
    => SnocProd Sing os
    -> Nested v os a
    -> Nested v (Reverse os) a
transposeHelp = \case
    ØS -> \case
      NØ x -> NØ x
    (sOs' :: SnocProd Sing os') :& (sO :: Sing o) ->
      (\\ (nesting1 Proxy :: Wit (Functor     (v o)))) $
      (\\ (nesting1 sO    :: Wit (Applicative (v o)))) $ \x ->
        let lOs'  :: Length os'
            lOs'  = snocProdLength sOs'
            x' :: Nested v os' (v o a)
            x' = mapNVecSlices unVector lOs' x
                   \\ appendSnoc lOs' sO
            xT :: Nested v (Reverse os') (v o a)
            xT = transposeHelp sOs' x'
            -- TODO: analyze sequenceA vs. distribute
            y :: v o (Nested v (Reverse os') a)
            y = sequenceA xT
            y' :: Nested v '[o] (Nested v (Reverse os') a)
            y' = nVector y
        in  joinNestedVec y'
              \\ snocReverse lOs' sO



