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
-- import           Data.Proxy
-- import           Data.Singletons.Prelude.List ((:++), Reverse, sReverse)
-- import           Data.Type.Equality hiding    (outer)
-- import           Data.Type.Product.Util
-- import           Data.Type.Vector             as TCV
-- import           Data.Type.Vector.Util
-- import           Numeric.AD
-- import           Type.Family.Nat
-- import           Unsafe.Coerce
import           Data.Foldable
import           Data.Kind
import           Data.Maybe
import           Data.Singletons
import           Data.Type.Combinator
import           Data.Type.Conjunction
import           Data.Type.Index
import           Data.Type.Length
import           Data.Type.Length.Util           as TCL
import           Data.Type.Product
import           Data.Type.Product.Util
import           Data.Type.Sing
import           Data.Type.Uniform
import           TensorOps.Run
import           TensorOps.Types
import           Type.Class.Higher
import           Type.Class.Known
import           Type.Class.Witness
import           Type.Family.List
import           Type.Family.List.Util
import qualified TensorOps.Tensor                as Tensor

gradTOp
    :: forall ns ms t. (Tensor t, Floating (ElemT t), SingI ns, SingI ms)
    => TOp ns ms
    -> Prod t ns    -- ^ inputs
    -> Prod t ms    -- ^ d target / d outputs
    -> Prod t ns    -- ^ d target / d inputs
gradTOp = (\case
    Lift uN uM f -> case uN of
      UØ   -> \_ _ -> Ø
      US _ -> \x -> vecToProd getI uN
                  . Tensor.gradLift f (prodToVec I uN x)
                  . prodToVec I uM
    GMul lM lO lN -> \case
      -- lM   :: Length m
      -- lO   :: Length o
      -- lN   :: Length n
      -- x    :: t (Head ns)
      --      :: t (m ++ o)
      -- y    :: t (Head (Tail ns))
      --      :: t (Reverse o ++ n)
      -- dtdz :: t (Head ms)
      --      :: t (m ++ n)
      x :< y :< Ø -> \case
        dtdz :< Ø -> let rlO = TCL.reverse' lO
                         entailCatRev
                                :: p a
                                -> p b
                                -> (SingI (a ++ b) :- SingI (Reverse (a ++ b)))
                         entailCatRev _ _ = entailSing sReverse
      -- gmul :: Length m
      --      -> Length n
      --      -> Length o
      --      -> t (m ++ n)
      --      -> t (Reverse n ++ o)
      --      -> t (m ++ o)
      -- transp y :: t (Reverse (Reverse o ++ n))
      --          :: t (Reverse n ++ Reverse (Reverse o))
      --          :: t (Reverse n ++ o)
      -- therefore we need:
      --   Reverse (Reverse o ++ n)  :~: Reverse n ++ Reverse (Reverse o)
      --   Reverse (Reverse o)       :~: o
                     in  (gmul lM lN lO dtdz (transp y)
                           \\ reverseConcat rlO lN
                           \\ reverseReverse lO
                           \\ entailCatRev rlO lN
                         )
      -- gmul :: Length (Reverse o)
      --      -> Length (Reverse m)
      --      -> Length n
      --      -> t (Reverse o ++ Reverse m)
      --      -> t (Reverse (Reverse m) ++ n)
      --      -> t (Reverse o ++ n)
      -- transp x :: t (Reverse (m ++ o))
      --          :: t (Reverse o ++ Reverse m)
      -- dtdz     :: t (m ++ o)
      --          :: t (Reverse (Reverse m) ++ o)
      -- therefore we need:
      --   Reverse (m ++ o)    :~: Reverse o ++ Reverse m
      --   Reverse (Reverse m) :~: m
                      :< (gmul rlO (TCL.reverse' lM) lN
                               (transp x)
                               dtdz
                            \\ reverseConcat lM lO
                            \\ reverseReverse lM
                            \\ entailCatRev lM lO
                         )
                      :< Ø
    Transp lN     -> \case
        _ :< Ø -> \case
          dtdz :< Ø -> only $ transp dtdz \\ reverseReverse lN
    Shuffle is    -> \_ dtdz ->
      let ixds :: Prod (Index ns :&: t) ms
          ixds = zipProd is dtdz
          f  :: forall n. ()
             => Index ns n
             -> Sing n
             -> t n
          f i s = withSingI s $
                    foldl' (Tensor.zip2 (+)) (Tensor.konst 0) $ foldMap1 g ixds
            where
              g :: forall m. ()
                => (Index ns :&: t) m
                -> [t n]
              g (k :&: d) = case testEquality k i of
                Just Refl -> [d]
                Nothing   -> []
      in  imap1 f (singProd sing :: Prod Sing ns)
    ) \\ (singSings :: SingI ns :- ListC (SingI <$> ns))
      \\ (singSings :: SingI ms :- ListC (SingI <$> ms))

gradTensorOp
    :: forall ns t. (Tensor t, Floating (ElemT t))
    => TensorOp ns '[ '[] ]
    -> Prod t ns    -- ^ inputs
    -> Prod t ns    -- ^ d target / d inputs
gradTensorOp = \case
    OPØ            -> \_ -> only $ Tensor.konst 1
    -- ns ~ a ++ d
    Pop (lA :: Length a)
        (lD :: Length d)
        (o  :: TOp a b)
        (os :: OpPipe TOp (b ++ d) '[ '[] ])
                   -> \x -> let y    :: Prod t (b ++ d)
                                y    = overProdInit lA lD (runTOp o) x
                                dtdy :: Prod t (b ++ d)
                                dtdy = gradTensorOp os y
                                lB   :: Length b
                                lB   = singLength (sing :: Sing b)
                                res  :: Prod t (a ++ d)
                                res  = overProdInit lB lD (gradTOp o (takeProd lA lD x)) dtdy
                            in  res
