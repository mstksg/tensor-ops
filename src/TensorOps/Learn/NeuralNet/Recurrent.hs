{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module TensorOps.Learn.NeuralNet.Recurrent where

import           Control.Category hiding        ((.), id)
import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude hiding ((%:++))
import           Data.Type.Conjunction
import           Data.Type.Length               as TCL
import           Data.Type.Length.Util          as TCL
import           Data.Type.Nat
import           Data.Type.Product              as TCP
import           Data.Type.Product.Util         as TCP
import           Data.Type.Sing
import           Data.Type.Vector               as TCV
import           TensorOps.TOp                  as TO
import           TensorOps.Tensor               as TT
import           TensorOps.Types
import           Type.Class.Higher
import           Type.Class.Known
import           Type.Class.Witness
import           Type.Family.List
import           Type.Family.List.Util
import           Unsafe.Coerce

data Network :: ([k] -> Type) -> k -> k -> Type where
    N :: { _nsSs    :: !(Sing ss)
         , _nsPs    :: !(Sing ps)
         , _nOp     :: !(TOp ('[i] ': ss ++ ps) ('[o] ': ss))
         , _nState  :: !(Prod t ss)
         , _nParams :: !(Prod t ps)
         } -> Network t i o

(~*~)
    :: forall k (t :: [k] -> Type) a b c. ()
    => Network t a b
    -> Network t b c
    -> Network t a c
(~*~) = \case
  N (sSs1 :: Sing ss1)
    (sPs1 :: Sing ps1)
    (o1   :: TOp ('[a] ': ss1 ++ ps1) ('[b] ': ss1))
    (s1   :: Prod t ss1)
    (p1   :: Prod t ps1) -> \case
    N (sSs2 :: Sing ss2)
      (sPs2 :: Sing ps2)
      (o2   :: TOp ('[b] ': ss2 ++ ps2) ('[c] ': ss2))
      (s2   :: Prod t ss2)
      (p2   :: Prod t ps2) ->
      let lSs1 :: Length ss1
          lSs1 = singLength sSs1
          lSs2 :: Length ss2
          lSs2 = singLength sSs2
          lPs1 :: Length ps1
          lPs1 = singLength sPs1
          lPs2 :: Length ps2
          lPs2 = singLength sPs2
          o :: TOp ('[a] ': (ss2 ++ ss1) ++ (ps1 ++ ps2)) ('[c] ': ss2 ++ ss1)
                    -- all these proofs lol
          o     = (\\ (unsafeCoerce Refl :: ((ss2 ++ ss1) ++ ps1) ++ ps2 :~: (ss2 ++ ss1) ++ (ps1 ++ ps2))) $
                  (\\ (unsafeCoerce Refl :: ((ss1 ++ ps1) ++ ss2) ++ ps2 :~: (ss1 ++ ps1) ++ (ss2 ++ ps2))) $
                  (\\ appendAssoc lSs1 lSs2 lPs2                  ) $
                  (\\ appendAssoc lSs2 lSs1 lPs1                  ) $
                  (\\ (lSs2 `TCL.append'` lSs1) `TCL.append'` lPs1) $
                  (\\ (lSs1 `TCL.append'` lPs1) `TCL.append'` lSs2) $
                  (\\ lSs1                                        ) $
                  (\\ lSs2                                        ) $
                  (\\ lSs1 `TCL.append'` lPs1                     ) $
                  (\\ lSs2 `TCL.append'` lPs2                     ) $
                    secondOp @'[ '[a] ]
                      (firstOp @ps2 (TO.swap' lSs2 (lSs1 `TCL.append'` lPs1))
                      )
                >>> firstOp @(ss2 ++ ps2) o1
                >>> secondOp @'[ '[b] ] (TO.swap' lSs1 (lSs2 `TCL.append'` lPs2))
                >>> firstOp @ss1 o2
      in  N (sSs2 %:++ sSs1)
            (sPs1 %:++ sPs2)
            o
            (s2 `TCP.append'` s1)
            (p1 `TCP.append'` p2)
infixr 4 ~*~

runNetwork
    :: (RealFloat (ElemT t), Tensor t)
    => t '[i]
    -> Network t i o
    -> (t '[o], Network t i o)
runNetwork x (N sS sO o s p) =
        (\case y :< s' -> (y, N sS sO o s' p))
      . runTOp o
      $ x :< (s `TCP.append'` p)

trainNetwork
    :: Tensor t
    => ElemT t
    -> VecT n t '[i]
    -> VecT n t '[o]
    -> Network t i o
    -> Network t i o
trainNetwork = undefined

trainNetwork1
    :: forall t i o. (Tensor t, RealFloat (ElemT t))
    => TOp '[ '[o], '[o] ] '[ '[] ]
    -> ElemT t
    -> ElemT t
    -> t '[i]
    -> t '[o]
    -> Network t i o
    -> Network t i o
trainNetwork1 loss rP rS x y = \case
    N (sS :: Sing ss)
      (sO :: Sing ps)
      (o  :: TOp ('[i] ': ss ++ ps) ('[o] ': ss))
      (s  :: Prod t ss)
      (p  :: Prod t ps) -> (\\ sS) $
                           (\\ sS %:++ sOnly SNil) $
      let o' :: TOp ('[o] ': '[i] ': ss ++ ps) '[ '[] ]
          o' = secondOp @'[ '[o] ] o
           >>> firstOp loss
           >>> TO.swap' (LS LZ) (singLength sS)
           >>> TO.drop (singLength sS)
          inp :: Prod t ('[o] ': '[i] ': ss ++ ps)
          inp = y :< x :< s `TCP.append'` p
          grad :: Prod t (ss ++ ps)
          grad = dropProd (LS (LS LZ))
               $ gradTOp o' inp
          gS :: Prod t ss
          gP :: Prod t ps
          (gS, gP) = splitProd (singLength sS) grad
          s' :: Prod t ss
          s' = map1 (\(s1 :&: o1 :&: g1) -> TT.zip (stepFunc rS) o1 g1 \\ s1)
             $ zipProd3 (singProd sS) s gS
          p' :: Prod t ps
          p' = map1 (\(s1 :&: o1 :&: g1) -> TT.zip (stepFunc rP) o1 g1 \\ s1)
             $ zipProd3 (singProd sO) p gP
      in  N sS sO o s' p'
  where
    stepFunc :: ElemT t -> ElemT t -> ElemT t -> ElemT t
    stepFunc r o' g' = o' - r * g'
    {-# INLINE stepFunc #-}

foop
    :: forall i o ss ps. (SingI i, SingI (ss ++ ps))
    => Length ss
    -> Length ps
    -> TOp '[ '[o], '[o] ] '[ '[] ]
    -> TOp ('[i] ': ss ++ ps) ('[o] ': ss)
    -> TOp ('[i] ': ss ++ ps ++ '[ '[] ] ++ '[ '[o] ]) (ss ++ ps >: '[])
foop lS lP loss o = (\\ appendAssoc lS lP (LS (LS LZ) :: Length '[ '[], '[o] ])) $
                    (\\ appendAssoc lS lP (LS LZ :: Length '[ '[] ]) ) $
                    (\\ appendAssoc lS lP (LS (LS LZ) :: Length '[ '[], '[] ]) ) $
                    (\\ appendAssoc lP (LS LZ :: Length '[ '[] ]) (LS LZ :: Length '[ '[o] ])) $
                    (\\ appendAssoc lP (LS LZ :: Length '[ '[] ]) (LS LZ :: Length '[ '[] ])) $
                    (\\ appendAssoc lP (LS (LS LZ) :: Length '[ '[], '[o] ]) (LS LZ :: Length '[ '[o] ])) $
                    (\\ appendAssoc lS (lP `TCL.append'` (LS LZ :: Length '[ '[] ])) (LS LZ :: Length '[ '[o] ])) $
                    (\\ appendAssoc lS (lP `TCL.append'` (LS LZ :: Length '[ '[] ])) (LS LZ :: Length '[ '[] ])) $
                    (\\ appendAssoc lS lP (LS (LS LZ) :: Length '[ '[], '[o] ]) ) $
                    (\\ appendAssoc (LS LZ :: Length '[ '[] ]) (LS LZ :: Length '[ '[o] ]) (LS LZ :: Length '[ '[] ])) $
                    (\\ appendAssoc (LS LZ :: Length '[ '[] ]) (LS LZ :: Length '[ '[o] ]) (LS LZ :: Length '[ '[o] ])) $
                    (\\ appendAssoc lS (lP `TCL.append'` (LS (LS LZ) :: Length '[ '[], '[o] ])) (LS LZ :: Length '[ '[o] ])) $
                    (\\ appendSnoc (lS `TCL.append'` lP) (Proxy @'[])) $
                    (\\ appendSnoc lP (Proxy @'[])) $
                    (\\ (unsafeCoerce Refl :: ((ss ++ (ps ++ '[ '[] ])) ++ '[ '[o], '[o] ]) :~: (ss ++ ((ps ++ '[ '[], '[o] ]) ++ '[ '[o] ])))) $
                    (\\ lS `TCL.append'` lP) $
                    (\\ lS `TCL.append'` lP `TCL.append'` (LS (LS LZ) :: Length '[ '[], '[o] ])) $
                    (\\ lS `TCL.append'` lP `TCL.append'` (LS LZ :: Length '[ '[] ])) $
                    (\\ lS                 ) $
      firstOp @'[ '[], '[o] ] (o &&& TO.drop @ps (LS lS))
  >>> firstOp @'[ '[o] ] (TO.swap' (LS LZ :: Length '[ '[o] ]) ((lS `TCL.append'` lP) TCL.>: Proxy @'[]))
  >>> secondOp @(ss ++ ps >: '[])         loss
  >>> secondOp @(ss ++ ps) @'[ '[], '[] ] TO.add

boop
    :: forall ss ps i o n. (SingI i)
    => Sing ss
    -> Sing ps
    -> TOp '[ '[o], '[o] ] '[ '[] ]
    -> TOp ('[i] ': ss ++ ps) ('[o] ': ss)
    -> Nat n
    -> TOp (Replicate n '[i] ++ ss ++ ps ++ '[ '[] ] ++ Replicate n '[o]) (ss ++ ps >: '[])
boop sS sP loss o = \case
    Z_              -> idOp \\ appendSnoc lP (Proxy @'[])
    S_ (m :: Nat m) -> (\\ (unsafeCoerce Refl :: Replicate m '[i] ++ '[i] ': ss ++ ps ++ '[ '[], '[o] ]
                                             :~: '[i] ': Replicate m '[i] ++ ss ++ ps ++ '[ '[], '[o] ]
                           )) $
                       (\\ (unsafeCoerce Refl :: (Replicate m '[i] ++ ss ++ ps ++ '[ '[], '[o] ]) ++ Replicate m '[o]
                                             :~: Replicate m '[i] ++ ss ++ ps ++ '[ '[] ] ++ '[o] ': Replicate m '[o]
                           )) $
                       (\\ (unsafeCoerce Refl :: (Replicate m '[i] ++ ss ++ ps >: '[]) ++ Replicate m '[o]
                                             :~: Replicate m '[i] ++ ss ++ ps ++ '[] ': Replicate m '[o]
                           )) $
                       (\\ sS %:++ sP) $
                       (\\ replicateLength @'[i] m) $
                       (\\ replicateLength @'[i] m `TCL.append'` lS `TCL.append'` lP `TCL.append'` (LS (LS LZ) :: Length '[ '[], '[o] ])) $
                       (\\ replicateLength @'[i] m `TCL.append'` lS `TCL.append'` lP TCL.>: Proxy @'[]) $
          firstOp @(Replicate m '[o]) (
             secondOp @(Replicate m '[i]) (
                 foop lS lP loss o
               )
           )
      >>> boop sS sP loss o m
  where
    lS :: Length ss
    lS = singLength sS
    lP :: Length ps
    lP = singLength sP

unroll
    :: forall ss ps i o n. (SingI (ss ++ ps), SingI i)
    => Sing ss
    -> Sing ps
    -> TOp ('[i] ': ss ++ ps) ('[o] ': ss)
    -> Nat n
    -> TOp (Replicate n '[i] ++ ss ++ ps) (ss ++ Replicate n '[o])
unroll sS sP o = \case
    Z_              -> TO.take lS lP    \\ appendNil lS
    S_ (m :: Nat m) -> (\\ (unsafeCoerce Refl :: (Replicate m '[i] ++ '[i] ': ss ++ ps)
                                             :~: ('[i] ': Replicate m '[i] ++ ss ++ ps)
                           )
                       ) $
                       (\\ (unsafeCoerce Refl :: ((Replicate m '[i] ++ ss ++ ps) ++ '[ '[o] ])
                                             :~: (Replicate m '[i] ++ ss ++ (ps >: '[o]))
                           )
                       ) $
                       (\\ (unsafeCoerce Refl :: ((ss ++ Replicate m '[o]) ++ '[ '[o] ])
                                             :~: (ss ++ '[o] ': Replicate m '[o])
                           )
                       ) $
                       (\\ replicateLength @'[i] m `TCL.append'` lS `TCL.append'` lP) $
                       (\\ lS `TCL.append'` replicateLength @'[o] m) $
                       (\\ replicateLength @'[i] m) $
                       (\\ lS) $
          secondOp @(Replicate m '[i]) @('[i] ': ss ++ ps) @(ss ++ ps >: '[o]) (
                (o &&& TO.drop @ps @('[i] ': ss) (LS lS))
             >>> _
          )
      >>> firstOp @'[ '[o] ] @(Replicate m '[i] ++ ss ++ ps) @(ss ++ Replicate m '[o]) (
            unroll sS sP o m
          )
  where
    lS :: Length ss
    lS = singLength sS
    lP :: Length ps
    lP = singLength sP

-- boop sS sP loss o = \case
--     Z_              -> idOp \\ appendSnoc lP (Proxy @'[])
--     S_ (m :: Nat m) -> (\\ (unsafeCoerce Refl :: Replicate m '[i] ++ '[i] ': ss ++ ps ++ '[ '[], '[o] ]
--                                              :~: '[i] ': Replicate m '[i] ++ ss ++ ps ++ '[ '[], '[o] ]
--                            )) $
--                        (\\ (unsafeCoerce Refl :: (Replicate m '[i] ++ ss ++ ps ++ '[ '[], '[o] ]) ++ Replicate m '[o]
--                                              :~: Replicate m '[i] ++ ss ++ ps ++ '[ '[] ] ++ '[o] ': Replicate m '[o]
--                            )) $
--                        (\\ (unsafeCoerce Refl :: (Replicate m '[i] ++ ss ++ ps >: '[]) ++ Replicate m '[o]
--                                              :~: Replicate m '[i] ++ ss ++ ps ++ '[] ': Replicate m '[o]
--                            )) $
--                        (\\ sS %:++ sP) $
--                        (\\ replicateLength @'[i] m) $
--                        (\\ replicateLength @'[i] m `TCL.append'` lS `TCL.append'` lP `TCL.append'` (LS (LS LZ) :: Length '[ '[], '[o] ])) $
--                        (\\ replicateLength @'[i] m `TCL.append'` lS `TCL.append'` lP TCL.>: Proxy @'[]) $
--           firstOp @(Replicate m '[o]) (
--              secondOp @(Replicate m '[i]) (
--                  foop lS lP loss o
--                )
--            )
--       >>> boop sS sP loss o m
--   where
--     lS :: Length ss
--     lS = singLength sS
--     lP :: Length ps
--     lP = singLength sP
