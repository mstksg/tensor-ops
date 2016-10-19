{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module Data.Type.Length.Util where

import           Data.Kind
import           Data.Proxy
import           Data.Singletons.Decide
import           Data.Type.Length
import           Data.Type.Nat
import           Data.Type.Product hiding ((>:), append')
import           Prelude hiding           (init)
import           Type.Class.Witness
import           Type.Family.List
import           Type.Family.List.Util
import           Type.Family.Nat
import           Type.Family.Nat.Util
import           Unsafe.Coerce
import qualified Data.Type.Product        as P

append'
    :: Length ns
    -> Length ms
    -> Length (ns ++ ms)
append' = \case
    LZ   -> id
    LS l -> LS . append' l

tail'
    :: Length (n ': ns)
    -> Length ns
tail' = \case
    LS l -> l

-- TODO: could PROBABLY just be unsafeCoerce?
reverse'
    :: forall ns. ()
    => Length ns
    -> Length (Reverse ns)
reverse' = unsafeCoerce
-- reverse' = \case
--     LZ   -> LZ
--     LS l -> reverse' l >: (Proxy @(Head ns))
{-# INLINE reverse' #-}

-- TODO: is this ok to be unsafeCoerce?
(>:)
    :: Length ns
    -> Proxy n
    -> Length (ns >: n)
-- (>:) l _ = unsafeCoerce $ LS l
(>:) = \case
    LZ   -> \_ -> LS LZ
    LS l -> LS . (l >:)
{-# INLINE (>:) #-}

data SnocLength :: [a] -> Type where
    SnocZ :: SnocLength '[]
    SnocS :: SnocLength as -> Proxy a -> SnocLength (as >: a)

snocLengthHelp
    :: forall as bs. ()
    => Length bs
    -> SnocLength bs
    -> Length as
    -> SnocLength (bs ++ as)
snocLengthHelp lB sB = \case
    LZ                            ->
        sB      \\ appendNil lB
    lA@(LS lA') ->
        snocLengthHelp (lB >: p lA) (SnocS sB (p lA)) lA'
                \\ appendSnoc lB (p lA)
                \\ appendAssoc lB (l lA) lA'
  where
    p :: forall c cs. Length (c ': cs) -> Proxy c
    p _ = Proxy
    l :: forall c cs. Length (c ': cs) -> Length '[c]
    l _ = LS LZ

-- | could this be unsafeCoerce?
snocLength
    :: Length as
    -> SnocLength as
snocLength l = snocLengthHelp LZ SnocZ l

-- | could just be unsafeCoerce lol
snocLengthLength
    :: SnocLength as
    -> Length as
snocLengthLength = \case
    SnocZ     -> LZ
    SnocS l s -> snocLengthLength l >: s

snocLengthReverse
    :: SnocLength as
    -> Length (Reverse as)
snocLengthReverse = \case
    SnocZ     -> LZ
    SnocS (s :: SnocLength bs) (p :: Proxy b) ->
      LS (snocLengthReverse s)
        \\ snocReverse (snocLengthLength s) p

-- | A @'MaxLength' n as@ is a witness that the list @as@ has a length of
-- at most @n@.
data MaxLength :: N -> [k] -> Type where
    MLZ :: MaxLength n '[]
    MLS :: !(MaxLength n as) -> MaxLength ('S n) (a ': as)

-- | An @'ExactLength' n as@ is a witness that the list @as@ has a length
-- of exactly @n@.
data ExactLength :: N -> [k] -> Type where
    ELZ :: ExactLength 'Z '[]
    ELS :: !(ExactLength n as) -> ExactLength ('S n) (a ': as)

data Splitting :: N -> ([k] -> Type) -> [k] -> Type where
    Fewer
        :: !(MaxLength n as)
        -> !(f as)
        -> Splitting n f as
    Split
        :: !(ExactLength n as)
        -> !(f as)
        -> !(f (b ': bs))
        -> Splitting n f (as ++ (b ': bs))

splitting
    :: Nat n
    -> Prod f as
    -> Splitting n (Prod f) as
splitting = \case
  Z_   -> \case
    Ø       -> Fewer MLZ Ø
    x :< xs -> Split ELZ Ø (x :< xs)
  S_ n -> \case
    Ø       -> Fewer MLZ Ø
    x :< xs -> case splitting n xs of
      Fewer m xs'    -> Fewer (MLS m) (x :< xs')
      Split e xs' ys -> Split (ELS e) (x :< xs') ys

maxLength
    :: Nat n
    -> Length as
    -> Decision (MaxLength n as)
maxLength = \case
  Z_   -> \case
    LZ   -> Proved    MLZ
    LS _ -> Disproved (\case)
  S_ n -> \case
    LZ   -> Proved MLZ
    LS l -> case maxLength n l of
      Proved m    -> Proved (MLS m)
      Disproved r -> Disproved $ \case
        MLS m -> r m

exactLength
    :: Nat n
    -> Length as
    -> Decision (ExactLength n as)
exactLength = \case
  Z_ -> \case
    LZ   -> Proved ELZ
    LS _ -> Disproved (\case)
  S_ n -> \case
    LZ   -> Disproved (\case)
    LS l -> case exactLength n l of
      Proved e    -> Proved (ELS e)
      Disproved r -> Disproved $ \case
        ELS e -> r e

fromMaxLength
    :: MaxLength n as
    -> Length as
fromMaxLength = \case
    MLZ   -> LZ
    MLS m -> LS (fromMaxLength m)

fromExactLength
    :: ExactLength n as
    -> Length as
fromExactLength = \case
    ELZ   -> LZ
    ELS m -> LS (fromExactLength m)

weakenExactLength
    :: ExactLength n as
    -> MaxLength n as
weakenExactLength = \case
  ELZ   -> MLZ
  ELS e -> MLS (weakenExactLength e)

weakenMaxLength
    :: (n :<=: m)
    -> MaxLength n as
    -> MaxLength m as
weakenMaxLength = \case
    LTEZ -> \case
      MLZ   -> MLZ
    LTES l -> \case
      MLZ   -> MLZ
      MLS s -> MLS (weakenMaxLength l s)

data SplittingEnd :: N -> ([k] -> Type) -> [k] -> Type where
    FewerEnd
        :: !(MaxLength n as)
        -> !(f as)
        -> SplittingEnd n f as
    SplitEnd
        :: !(ExactLength n as)
        -> !(f (b ': bs))
        -> !(f as)
        -> SplittingEnd n f ((b ': bs) ++ as)

-- | Pretty sure this is O(n^2) but what can you do you know
splittingEnd
    :: Nat n
    -> Prod f as
    -> SplittingEnd n (Prod f) as
splittingEnd n xs = case splitting n xs of
    Fewer m xs'   -> FewerEnd m xs'
    Split _ _   _ -> case xs of
      Ø       -> FewerEnd MLZ Ø
      y :< ys -> case splittingEnd n ys of
        FewerEnd m zs     -> case consMaxLength n m of
          Left  e  -> SplitEnd e  (y :< Ø ) zs
          Right m' -> FewerEnd m' (y :< zs)
        SplitEnd e ys' zs -> SplitEnd e (y :< ys') zs

consMaxLength
    :: Nat n
    -> MaxLength n as
    -> Either (ExactLength n as) (MaxLength n (a ': as))
consMaxLength = \case
    Z_   -> \case
      MLZ -> Left ELZ
    S_ n -> \case
      MLZ   -> Right (MLS MLZ)
      MLS m -> case consMaxLength n m of
        Left e   -> Left  (ELS e)
        Right m' -> Right (MLS m')

commuteProd
    :: Length as
    -> Length cs
    -> Prod f (as ++ cs)
    -> Prod f bs
    -> (Prod f as, Prod f (cs ++  bs))
commuteProd = \case
    LZ   -> \_ xs ys -> (Ø, xs `P.append'` ys)
    LS lA -> \lC -> \case
      x :< xs -> \ys ->
        case commuteProd lA lC xs ys of
          (xs', ys') -> (x :< xs', ys')

lengthProd
    :: Length as
    -> Prod Proxy as
lengthProd = \case
    LZ   -> Ø
    LS l -> Proxy :< lengthProd l
