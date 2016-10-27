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

import           Data.List hiding                 ((\\))
import           Data.Singletons
import           Data.Singletons.Prelude.List     (Sing(..), sHead)
import           Data.Type.Combinator
import           Data.Type.Conjunction
import           Data.Type.Index
import           Data.Type.Length
import           Data.Type.Length.Util            as TCL
import           Data.Type.Product  as TCP hiding (select, toList)
import           Data.Type.Product.Util           as TCP
import           Data.Type.Sing
import           Data.Type.Uniform
import           TensorOps.Run
import           TensorOps.Types
import           Type.Class.Higher
import           Type.Class.Witness
import           Type.Family.List
import           Type.Family.List.Util
import qualified TensorOps.Tensor                 as TT

-- gradTOp
--     :: forall ns ms t. (Tensor t, RealFloat (ElemT t))
--     => Sing ns
--     -> Sing ms
--     -> TOp ns ms
--     -> Prod t ns    -- ^ inputs
--     -> Prod t ms    -- ^ d target / d outputs
--     -> Prod t ns    -- ^ d target / d inputs
-- gradTOp sNs sMs = (\\ witSings sNs) $
--                   (\\ witSings sMs) $ \case
--     Lift uN uM f -> case uN of
--       UØ   -> \_ _ -> Ø
--       US _ -> \x -> vecToProd getI uN
--                   . TT.gradLift f (prodToVec I uN x)
--                   . prodToVec I uM
--     SumT u  -> \xs -> \case
--       dtdz :< Ø -> mapUniform u (\_ -> dtdz) xs
--     Scale α -> \_ -> only . scaleT α . TCP.head'
--     GMul lM lO lN -> \case
--       x :< y :< Ø -> \case
--         dtdz :< Ø -> let rlO = TCL.reverse' lO
--                          entailCatRev
--                                 :: p a
--                                 -> p b
--                                 -> (SingI (a ++ b) :- SingI (Reverse (a ++ b)))
--                          entailCatRev _ _ = entailSing sReverse
--                      in  (gmul lM lN lO dtdz (transp y)
--                            \\ reverseConcat rlO lN
--                            \\ reverseReverse lO
--                            \\ entailCatRev rlO lN
--                          )
--                       :< (gmul rlO (TCL.reverse' lM) lN
--                                (transp x)
--                                dtdz
--                             \\ reverseConcat lM lO
--                             \\ reverseReverse lM
--                             \\ entailCatRev lM lO
--                          )
--                       :< Ø
--     Transp lN     -> \case
--         _ :< Ø -> \case
--           dtdz :< Ø -> only $ transp dtdz \\ reverseReverse lN
--     Shuffle is    -> \_ dtdz ->
--       let ixds :: Prod (Index ns :&: t) ms
--           ixds = zipProd is dtdz
--           f  :: forall n. ()
--              => Index ns n
--              -> Sing n
--              -> t n
--           -- wow this was a huge bottleneck lol
--           f i s = (\\ s) $
--                     (\case []       -> TT.konst 0
--                            xs@(_:_) -> foldl1' (TT.zip (+)) xs
--                     )
--                     . foldMap1 g
--                     $ ixds
--             where
--               g :: forall m. ()
--                 => (Index ns :&: t) m
--                 -> [t n]
--               g (k :&: d) = case testEquality k i of
--                 Just Refl -> [d]
--                 Nothing   -> []
--       in  imap1 f (singProd sNs)
--     SumRows -> \case
--       x :< Ø -> \case
--         dtdz :< Ø ->
--           -- only $ mapRows (LS LZ) (TT.zip (*) dtdz) x
--           only $ mapRows (LS LZ) (\_ -> dtdz) x
--                    \\ sHead (sHead sNs)
--     -- SumRow (r :: Remove as n bs) -> \case
--     --   (x :: t as) :< Ø -> \case
--     --     (dtdz :: t bs) :< Ø ->
--     --       case remPart (singLength (sing :: Sing as)) r of
--     --         RP lC pA lD -> only $ mapRows (lC TCL.>: pA) lD (TT.zip2 (*) dtdz) x
--     --                          \\ appendSnoc lC pA
--     --                          \\ appendAssoc lC (LS LZ :: Length '[n]) lD
