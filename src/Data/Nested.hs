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

module Data.Nested
  ( Vec(..)
  , Nesting(..)
  , Nesting1(..), nesting1Every
  , Nested
  , genNested, genNestedA
  , indexNested
  , transpose
  , gmul'
  , diagNV
  , joinNested
  , nIxRows
  , vGen, itraverseNested
  , liftNested
  ) where

import           Control.Applicative
import           Control.DeepSeq
import           Data.Distributive
import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude.List hiding (Length, Reverse, (%:++), sReverse)
import           Data.Type.Combinator
import           Data.Type.Combinator.Util
import           Data.Type.Index
import           Data.Type.Length                    as TCL
import           Data.Type.Length.Util               as TCL
import           Data.Type.Product
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
    UCons :: !(Sing n) -> !a -> !(v n a) -> Uncons v (Succ n) a

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
{-# INLINE vGen #-}

instance Vec (Flip2 VS.VectorT I) where
    vHead _ = getI . VS.head . getFlip2
    {-# INLINE vHead #-}
    vTail = Flip2 . VS.tail . getFlip2
    {-# INLINE vTail #-}
    vGenA = \case
      GT.SNat -> fmap Flip2 . VS.generateA . (fmap I .)
    {-# INLINE vGenA #-}
    vIndex i = (VS.!! i) . getFlip2
    {-# INLINE vIndex #-}
    vUncons = \case
      GT.SNat -> \case
        Flip2 xs -> case VS.uncons xs of
          VS.VNil           -> UNil
          VS.VCons (I y) ys -> UCons sing y (Flip2 ys)
    {-# INLINE vUncons #-}
    vEmpty = Flip2 VS.empty
    {-# INLINE vEmpty #-}
    vCons x (Flip2 xs) = Flip2 (VS.cons (I x) xs)
    {-# INLINE vCons #-}
    vITraverse f (Flip2 xs) = Flip2 <$> VS.itraverse (\i (I x) -> I <$> f i x) xs
    {-# INLINE vITraverse #-}

instance Vec (Flip2 TCV.VecT I) where
    vHead _ = getI . TCV.head' . getFlip2
    {-# INLINE vHead #-}
    vTail = Flip2 . TCV.tail' . getFlip2
    {-# INLINE vTail #-}
    vGenA = \case
      SN n -> \f -> Flip2 <$> TCV.vgenA n (fmap I . f)
    {-# INLINE vGenA #-}
    vIndex i = TCV.index' i . getFlip2
    {-# INLINE vIndex #-}
    vUncons = \case
      SN TCN.Z_ -> \case
        Flip2 TCV.ØV -> UNil
      SN (TCN.S_ n) -> \case
        Flip2 (I x TCV.:* xs) -> UCons (SN n) x (Flip2 xs)
    {-# INLINE vUncons #-}
    vEmpty = Flip2 TCV.ØV
    {-# INLINE vEmpty #-}
    vCons x (Flip2 xs) = Flip2 (I x TCV.:* xs)
    {-# INLINE vCons #-}
    vITraverse f (Flip2 xs) = Flip2 <$> TCV.itraverse (\i (I x) -> I <$> f i x) xs
    {-# INLINE vITraverse #-}

class Nesting (w :: k -> Type) (c :: j -> Constraint) (v :: k -> j -> j) where
    nesting :: w i -> c a :- c (v i a)

class Nesting1 (w :: k -> Type) (c :: j -> Constraint) (v :: k -> j) where
    nesting1 :: w a -> Wit (c (v a))

instance Nesting w NFData (Flip2 VS.VectorT I) where
    nesting _ = Sub Wit
instance Functor f      => Nesting1 w    Functor      (Flip2 VS.VectorT f) where
    nesting1 _ = Wit
instance Applicative f  => Nesting1 Sing Applicative  (Flip2 VS.VectorT f) where
    nesting1 GT.SNat = Wit
instance Foldable f     => Nesting1 w    Foldable     (Flip2 VS.VectorT f) where
    nesting1 _ = Wit
instance Traversable f  => Nesting1 w    Traversable  (Flip2 VS.VectorT f) where
    nesting1 _ = Wit
instance Distributive f => Nesting1 Sing Distributive (Flip2 VS.VectorT f) where
    nesting1 GT.SNat = Wit


instance Nesting w NFData (Flip2 TCV.VecT I) where
    nesting _ = Sub Wit
instance Functor f      => Nesting1 w    Functor      (Flip2 TCV.VecT f) where
    nesting1 _ = Wit
instance Applicative f  => Nesting1 Sing Applicative  (Flip2 TCV.VecT f) where
    nesting1 (SN n) = Wit \\ n
instance Foldable f     => Nesting1 w    Foldable     (Flip2 TCV.VecT f) where
    nesting1 _ = Wit
instance Traversable f  => Nesting1 w    Traversable  (Flip2 TCV.VecT f) where
    nesting1 _ = Wit
instance Distributive f => Nesting1 Sing Distributive (Flip2 TCV.VecT f) where
    nesting1 (SN n) = Wit \\ n

nesting1Every
    :: forall p w c v as. Nesting1 w c v
    => p v
    -> Prod w as
    -> Wit (Every c (v <$> as))
nesting1Every p = \case
    Ø       -> Wit
    (w :: w a) :< (ws :: Prod w as')
        -> Wit  \\ (nesting1 w :: Wit (c (v a)))
                \\ (nesting1Every p ws :: Wit (Every c (v <$> as')))

data Nested :: (k -> Type -> Type) -> [k] -> Type -> Type where
    NØ :: !a                     -> Nested v '[]       a
    NS :: !(v j (Nested v js a)) -> Nested v (j ': js) a

instance (NFData a, Nesting Proxy NFData v) => NFData (Nested v js a) where
    rnf = \case
      NØ x  -> deepseq x  ()
      NS (xs :: v j (Nested v ks a))
            -> deepseq xs ()
                 \\ (nesting Proxy :: NFData (Nested v ks a) :- NFData (v j (Nested v ks a)))

-- deriving instance ListC (Show <$> ((v <$> js) <&> a)) => Show (Nested v js a)

instance (Num a, Applicative (Nested v js)) => Num (Nested v js a) where
    (+)         = liftA2 (+)
    {-# INLINE (+) #-}
    (*)         = liftA2 (*)
    {-# INLINE (*) #-}
    (-)         = liftA2 (-)
    {-# INLINE (-) #-}
    negate      = fmap negate
    {-# INLINE negate #-}
    abs         = fmap abs
    {-# INLINE abs #-}
    signum      = fmap signum
    {-# INLINE signum #-}
    fromInteger = pure . fromInteger
    {-# INLINE fromInteger #-}

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
    {-# INLINE pure #-}
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
    {-# INLINE (<*>) #-}

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

instance (Vec v, SingI js, Nesting1 Proxy Functor v) => Distributive (Nested v js) where
    distribute
        :: forall f a. Functor f
        => f (Nested v js a)
        -> Nested v js (f a)
    distribute xs = genNested sing $ \i -> indexNested i <$> xs
    {-# INLINE distribute #-}
    -- distribute = flip go sing
    --   where
    --     go  :: f (Nested v ks a)
    --         -> Sing ks
    --         -> Nested v ks (f a)
    --     go xs = \case
    --       SNil         -> NØ $ unScalar <$> xs
    --       s `SCons` ss -> NS . vGen s $ \i ->
    --                         go (fmap (indexNested' (i :< Ø)) xs) ss

nHead
    :: forall v p j js a. Vec v
    => p j
    -> Nested v (Succ j ': js) a
    -> Nested v js a
nHead p = \case
  NS xs -> vHead p xs
{-# INLINE nHead #-}

nTail
    :: Vec v
    => Nested v (Succ j ': js) a
    -> Nested v (j ': js) a
nTail = \case
  NS xs -> NS $ vTail xs
{-# INLINE nTail #-}

unScalar
    :: Nested v '[] a
    -> a
unScalar = \case
  NØ x -> x
{-# INLINE unScalar #-}

unNest
    :: Nested v (j ': js) a
    -> v j (Nested v js a)
unNest = \case
  NS xs -> xs
{-# INLINE unNest #-}

unVector
    :: Functor (v j)
    => Nested v '[j] a
    -> v j a
unVector = \case
    NS xs -> unScalar <$> xs
{-# INLINE unVector #-}

nVector
    :: Functor (v j)
    => v j a
    -> Nested v '[j] a
nVector = NS . fmap NØ
{-# INLINE nVector #-}

genNested
    :: Vec (v :: k -> Type -> Type)
    => Sing ns
    -> (Prod (IndexN k) ns -> a)
    -> Nested v ns a
genNested s f = getI $ genNestedA s (I . f)
{-# INLINE genNested #-}

genNestedA
    :: (Vec (v :: k -> Type -> Type), Applicative f)
    => Sing ns
    -> (Prod (IndexN k) ns -> f a)
    -> f (Nested v ns a)
genNestedA = \case
    SNil         -> \f -> NØ <$> f Ø
    s `SCons` ss -> \f -> NS <$> vGenA s (\i -> genNestedA ss (f . (i :<)))

indexNested
    :: Vec (v :: k -> Type -> Type)
    => Prod (IndexN k) ns
    -> Nested v ns a
    -> a
indexNested = \case
    Ø -> \case
      NØ x  -> x
    i :< is -> \case
      NS xs -> indexNested is (vIndex i xs)

indexNested'
    :: Vec (v :: k -> Type -> Type)
    => Prod (IndexN k) ms
    -> Nested v (ms ++ ns) a
    -> Nested v ns a
indexNested' = \case
    Ø -> id
    i :< is -> \case
      NS xs -> indexNested' is (vIndex i xs)

joinNested
    :: forall v ns ms a. Nesting1 Proxy Functor v
    => Nested v ns (Nested v ms a)
    -> Nested v (ns ++ ms) a
joinNested = \case
    NØ x  -> x
    NS (xs :: v j (Nested v js (Nested v ms a))) ->
      NS $ fmap joinNested xs
        \\ (nesting1 Proxy :: Wit (Functor (v j)))

unjoinNested
    :: Nesting1 Proxy Functor v
    => Length ns
    -> Nested v (ns ++ ms) a
    -> Nested v ns (Nested v ms a)
unjoinNested = mapNVecSlices id
{-# INLINE unjoinNested #-}

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

itraverseNested
    :: forall k (v :: k -> Type -> Type) (ns :: [k]) a b f. (Applicative f, Vec v)
    => (Prod (IndexN k) ns -> a -> f b)
    -> Nested v ns a
    -> f (Nested v ns b)
itraverseNested f = \case
    NØ x  -> NØ <$> f Ø x
    NS xs -> NS <$> vITraverse (\i -> itraverseNested (\is -> f (i :< is))) xs

    -- gmul    :: (SingI (ms ++ os), SingI (Reverse os ++ ns), SingI (ms ++ ns))
gmul'
    :: forall ms os ns v a.
     ( Nesting1 Proxy Functor      v
     , Nesting1 Sing  Applicative  v
     , Nesting1 Proxy Foldable     v
     , Nesting1 Proxy Traversable  v
     , Nesting1 Sing  Distributive v
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
gmul' lM lO _ x y = joinNested $ mapNVecSlices f lM x
  where
    psO :: Prod Sing (Reverse os)
    psO = singProd (sing :: Sing (Reverse os))
    f   :: Nested v os a
        -> Nested v ns a
    f z = squish lO (snocProd psO) z (unjoinNested (TCL.reverse' lO) y)

squish
    :: forall v os ns a.
     ( Num a
     , Nesting1 Proxy Functor      v
     , Nesting1 Sing  Applicative  v
     , Nesting1 Proxy Foldable     v
     , Nesting1 Proxy Traversable  v
     , Nesting1 Sing  Distributive v
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
     ( Nesting1 Proxy Functor      v
     , Nesting1 Proxy Foldable     v
     , Nesting1 Proxy Traversable  v
     , Nesting1 Sing  Distributive v
     )
    => Sing os
    -> Nested v os a
    -> Nested v (Reverse os) a
transpose s = transposeHelp (snocProd (singProd s))

transposeHelp
    :: forall v os a.
     ( Nesting1 Proxy Functor      v
     , Nesting1 Proxy Foldable     v
     , Nesting1 Proxy Traversable  v
     , Nesting1 Sing  Distributive v
     )
    => SnocProd Sing os
    -> Nested v os a
    -> Nested v (Reverse os) a
transposeHelp = \case
    ØS -> \case
      NØ x -> NØ x
    (sOs' :: SnocProd Sing os') :& (sO :: Sing o) ->
      (\\ (nesting1 Proxy :: Wit (Functor      (v o)))) $
      (\\ (nesting1 sO    :: Wit (Distributive (v o)))) $ \x ->
        let lOs'  :: Length os'
            lOs'  = snocProdLength sOs'
            x' :: Nested v os' (v o a)
            x' = mapNVecSlices unVector lOs' x
                   \\ appendSnoc lOs' sO
            xT :: Nested v (Reverse os') (v o a)
            xT = transposeHelp sOs' x'
            y :: v o (Nested v (Reverse os') a)
            y = distribute xT
            y' :: Nested v '[o] (Nested v (Reverse os') a)
            y' = nVector y
        in  joinNested y'
              \\ snocReverse lOs' sO


nIxRows
    :: forall k (v :: k -> Type -> Type) ns ms a b f. (Nesting1 Proxy Functor v, Applicative f, Vec v)
    => Length ns
    -> (Prod (IndexN k) ns -> Nested v ms a -> f b)
    -> Nested v (ns ++ ms) a
    -> f (Nested v ns b)
nIxRows = \case
    LZ   -> \f -> fmap NØ . f Ø
    LS l -> \f -> \case
      NS (xs :: v j (Nested v js a)) ->
        fmap NS . vITraverse (\i -> nIxRows l (\is ys -> f (i :< is) ys)) $ xs

liftNested
    :: Distributive (Nested v ns)
    => (TCV.Vec m (TCV.Vec n a -> a))
    -> TCV.Vec n (Nested v ns a)
    -> TCV.Vec m (Nested v ns a)
liftNested f xs = fmap (\g -> TCV.liftVecD g xs) f
{-# INLINE liftNested #-}

