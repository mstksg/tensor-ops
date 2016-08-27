{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module TensorOps.Gradient where

-- import           Control.Applicative
-- import           Data.Singletons.Prelude.List ((:++), Reverse, sReverse)
-- import           Data.Type.Combinator
-- import           Data.Type.Product.Util
-- import           Data.Type.Uniform
-- import           Data.Type.Vector             as TCV
-- import           Data.Type.Vector.Util
-- import           Numeric.AD
-- import           TensorOps.Run
-- import           Type.Class.Known
-- import           Type.Class.Witness
-- import           Type.Family.Nat
import           Data.Proxy
import           Data.Type.Equality hiding       (outer)
import           Data.Type.Length
import           Data.Type.Product hiding        (append')
import           TensorOps.Types
import           Type.Class.Higher
import           Type.Family.List
import           Unsafe.Coerce
import qualified TensorOps.Tensor                as Tensor

gradTOp
    :: (Tensor t, Floating (ElemT t))
    => TOp ns ms
    -> Prod t ns    -- ^ inputs
    -> Prod t ms    -- ^ d target / d outputs
    -> Prod t ns    -- ^ d target / d inputs
gradTOp = \case
    Lift uN uM f -> Tensor.gradLift uN uM f
    GMul lM lO lN -> \case
      x :< y :< Ø -> \case
                      -- lmao
        dtdz :< Ø -> gmul lM lN lO dtdz (coerceT (unsafeCoerce Refl) (transp y))
                  :< gmul (reverseLength lO) (reverseLength lM) lN
                          (coerceT (unsafeCoerce Refl) (transp x))
                          (coerceT (unsafeCoerce Refl) dtdz)
                  :< Ø
    Transp        -> \case
        x :< Ø -> \case
          dtdz :< Ø -> only $ coerceT (unsafeCoerce Refl) (transp dtdz)

coerceT
    :: Tensor t
    => (ns :~: ms)
    -> t ns
    -> t ms
coerceT Refl = id

revRev
    :: Length ns
    -> (ns :~: Reverse (Reverse ns))
revRev _ = unsafeCoerce Refl


    -- MatMat       -> \case
    --   x :< y :< Ø -> \case
    --     dtdo :< Ø -> dtdo `mulMM` transp y
    --               :< transp x `mulMM` dtdo
    --               :< Ø
    -- MatVec       -> \case
    --   x :< y :< Ø -> \case
    --     dtdo :< Ø -> dtdo `outer` y
    --               :< undefined
    --               -- :< _  -- oops i made this too generic
    --               -- :< x `mulMV` dtdo
    --               :< Ø

transpAppend
    :: Length ms
    -> Length ns
    -> t (Reverse (ms ++ ns))
    -> t (Reverse ns ++ Reverse ms)
transpAppend = unsafeCoerce

reverseAppend
    :: Length as
    -> Length bs
    -> (Reverse (as ++ bs) :~: (Reverse bs ++ Reverse as))
reverseAppend _ = unsafeCoerce Refl


reverseLength
    :: forall ns. ()
    => Length ns
    -> Length (Reverse ns)
reverseLength _ = unsafeCoerce Refl

    -- LZ   -> LZ
    -- l'@(LS l) -> case reverseSnoc l (mkP l') of
    --                Refl -> appendLength (reverseLength l) (mkL l')
  -- where
    -- mkP :: forall a as. Length (a ': as) -> Proxy a
    -- mkP _ = Proxy
    -- mkL :: forall a as. Length (a ': as) -> Length '[a]
    -- mkL _ = LS LZ

appendLength
    :: Length ns
    -> Length ms
    -> Length (ns ++ ms)
appendLength = \case
    LZ   -> id
    LS l -> LS . appendLength l

    -- LZ   -> LZ
    -- LS l -> snocLength (reverseLength l) (mkProxy l0)
  -- where
    -- mkProxy :: forall a as. Length (a ': as) -> Proxy a
    -- mkProxy _ = Proxy

reverseReverse
    :: Length ns
    -> (Reverse (Reverse ns) :~: Reverse ns)
reverseReverse _ = unsafeCoerce Refl

-- reverseConcat
--     :: Length as
--     -> Length bs
--     -> (Reverse (as ++ bs) :~: (Reverse bs ++ Reverse as))
-- reverseConcat = \case
--     LZ -> \case
--       LZ   -> Refl
--       LS b -> _

-- reverseSnoc
--     :: Length ns
--     -> Proxy n
--     -> (Reverse (n ': ns) :~: (ns >: n))
-- reverseSnoc l0 p = case l0 of
--     LZ   -> Refl
    -- LS l -> case lengthLast l of
    --           Left Refl -> Refl
    --           Right (Some ll) ->
    --             case reverseSnoc l (mkProxy ll) of
    --               Refl -> Refl
  -- where
    -- mkProxy :: forall a as. LastList as a -> Proxy a
    -- mkProxy _ = Proxy
    -- mkProxy :: forall a as. LastList as a -> Proxy a
    -- mkProxy _ = Proxy
-- (\case Refl -> Refl) . reverseSnoc l

data LastList :: [k] -> k -> * where
    LsZ :: LastList '[a] a
    LsS :: LastList as b -> LastList (a ': as) b

    -- LsS :: Last as a -> Last

lengthLast
    :: Length ns
    -> Either (ns :~: '[]) (Some (LastList ns))
lengthLast = \case
    LZ   -> Left Refl
    LS s -> case lengthLast s of
              Left  Refl      -> Right (Some LsZ     )
              Right (Some ll) -> Right (Some (LsS ll))


snocLength
    :: Length ns
    -> Proxy n
    -> Length (ns >: n)
snocLength = \case
    LZ   -> \_ -> LS LZ
    LS l -> LS . snocLength l

        -- only (x `mulMV` y)
    -- Outer          -> \case
    --   x :< y :< Ø  -> only (x `outer` y)
    -- Transp r is    -> only . transp r is . head'
    -- Fold f         -> only . foldT f     . head'
      -- case liftT uNs uMs (jacobian f) xs of
      -- case
      --   let f' = partials f uNs uMs xs
      --   in  xs

-- data LenRev :: [k] -> [k] -> * where
--     LRZ :: LenRev '[] '[]
--     LRS :: LenRev as (Reverse as) -> LenRev (a ': as) (Reverse as ++ '[a])

-- revLen
--     :: LenRev as bs
--     -> Length (Reverse as)
-- revLen = case

-- rev :: LenRev as bs
--     -> (as :~: Reverse bs)
-- rev = \case
--     LRZ   -> Refl
--     LRS l -> case rev l of
--                Refl -> Refl


