{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module TensorOps.TOp where

import           Control.Category
import           Data.Foldable
import           Data.Proxy
import           Data.Singletons
import           Data.Type.Combinator
import           Data.Type.Conjunction
import           Data.Type.Index
import           Data.Type.Length                as TCL
import           Data.Type.Length.Util           as TCL
import           Data.Type.Product as TCP hiding (append', toList)
import           Data.Type.Product.Util
import           Data.Type.Sing
import           Data.Type.Uniform
import           Data.Type.Vector                as TCV
import           Numeric.AD
import           Prelude hiding                  (map, replicate, zip, negate, (.), id)
import           TensorOps.Types as T hiding     (gmul)
import           Type.Class.Higher
import           Type.Class.Known
import           Type.Class.Witness hiding       (inner)
import           Type.Family.List
import           Type.Family.List.Util
import           Type.Family.Nat
import qualified Data.Type.Product.Util          as TCP
import qualified TensorOps.Tensor                as TT
import qualified TensorOps.Types                 as T

-- -- | Lift any `R^N -> R^M` function over every element in a n-tensor list,
-- -- producing a m-tensor list.
-- liftOp
--     :: SingI o
--     => Uniform o ns
--     -> Uniform o ms
--     -> Vec (Len ms) (VFunc (Len ns))
--     -> TOp ns ms
-- liftOp = \case
--     UØ -> \case
--       UØ     -> \ØV ->
--         TOp (\_   -> Ø)
--             (\_ _ -> Ø)
--       m@(US _) -> \fs ->
--         TOp (\_   -> vecToProd getI m $
--                       TT.konst . ($ ØV) . vfFunc <$> fs
--             )
--             (\_ _ -> Ø)
--     n@(US _) -> \case
--       UØ    -> \ØV ->
--         TOp (\_   -> Ø                           )
--             (\_ _ -> TCP.replicate (TT.konst 0) n)
--       m@(US _) -> \fs ->
--         TOp (vecToProd getI m . liftT (vfFunc <$> fs) . prodToVec I n)
--             (\x -> vecToProd getI n . TT.gradLift fs (prodToVec I n x) . prodToVec I m)

-- | Lift any `R^N -> R^M` function over every element in a n-tensor list,
-- producing a m-tensor list.
liftOp
    :: SingI o
    => Uniform o ns
    -> VFunc (Len ns)
    -> TOp ns '[o]
liftOp = \case
    UØ -> \f ->
      TOp (\_   -> only . TT.konst $ vfFunc f ØV)
          (\_ _ -> Ø                            )
    n@(US _) -> \f ->
        TOp (only . liftT (vfFunc f) . prodToVec I n)
            (\x -> vecToProd getI n . TT.gradLift f (prodToVec I n x) . TCP.head')

gmul
    :: forall ms os ns. (SingI (Reverse os ++ ns), SingI (ms ++ ns), SingI (ms ++ os))
    => Length ms
    -> Length os
    -> Length ns
    -> TOp '[ (ms ++ os), (Reverse os ++ ns) ] '[ ms ++ ns ]
gmul lM lO lN = TOp f g
  where
    f   :: Tensor t
        => Prod t '[ (ms ++ os), (Reverse os ++ ns) ]
        -> Prod t '[ ms ++ ns ]
    f = \case
      x :< y :< Ø -> only $ T.gmul lM lO lN x y
    g   :: Tensor t
        => Prod t '[ (ms ++ os), (Reverse os ++ ns) ]
        -> Prod t '[ ms ++ ns ]
        -> Prod t '[ (ms ++ os), (Reverse os ++ ns) ]
    g = \case
      x :< y :< Ø -> \case
        dtdz :< Ø -> let rlO = TCL.reverse' lO
                         entailCatRev
                                :: p a
                                -> p b
                                -> (SingI (a ++ b) :- SingI (Reverse (a ++ b)))
                         entailCatRev _ _ = entailSing sReverse
                     in  (T.gmul lM lN lO dtdz (transp y)
                           \\ reverseConcat rlO lN
                           \\ reverseReverse lO
                           \\ entailCatRev rlO lN
                         )
                      :< (T.gmul rlO (TCL.reverse' lM) lN
                               (transp x)
                               dtdz
                            \\ reverseConcat lM lO
                            \\ reverseReverse lM
                            \\ entailCatRev lM lO
                         )
                      :< Ø

-- TODO: allow for arbitrary permutation
transpOp
    :: forall ns. (SingI ns, SingI (Reverse ns))
    => Length ns
    -> TOp '[ns] '[Reverse ns]
transpOp lN = TOp (only . transp . TCP.head')
                  (\_ -> only . transp . TCP.head')
    \\ reverseReverse lN

shuffle
    :: forall ns ms. SingI ns
    => Prod (Index ns) ms
    -> TOp ns ms
shuffle is = TOp (TCP.select is) (\_ -> gr)
  where
    gr  :: forall t. Tensor t
        => Prod t ms
        -> Prod t ns
    gr dtdz = imap1 (\i s -> f i \\ s) (singProd sing)
      where
        ixds :: Prod (Index ns :&: t) ms
        ixds = zipProd is dtdz
        f  :: forall n. SingI n
           => Index ns n
           -> t n
        f i = sumT . foldMap1 g $ ixds
          where
            g :: forall m. ()
              => (Index ns :&: t) m
              -> [t n]
            g (k :&: d) = case testEquality k i of
              Just Refl -> [d]
              Nothing   -> []
    {-# INLINE gr #-}

shuffleF
    :: forall ns ms. ()
    => (forall f. Prod f ns -> Prod f ms)
    -> (forall f. Prod f ms -> Prod f ns)
    -> TOp ns ms
shuffleF f g = TOp f (\_ -> g)
{-# INLINE shuffleF #-}

sumRows
    :: forall n ns. (SingI n, SingI ns)
    => TOp '[ n ': ns ] '[ ns ]
sumRows = TOp (only . T.sumRows . TCP.head')
              (\case
                  x :< Ø -> \case
                    dtdz :< Ø -> only $ mapRows (LS LZ) (\_ -> dtdz) x
              )

sumOp
    :: SingI n
    => Uniform n ns
    -> TOp ns '[n]
sumOp u = TOp (only . sumT . toList . prodToVec I u)
              (\xs -> \case
                  dtdz :< Ø -> mapUniform u (\_ -> dtdz) xs
              )

scale
    :: SingI ns
    => (forall a. RealFloat a => a)
    -> TOp '[ ns ] '[ ns ]
scale α = TOp (only . scaleT α . TCP.head')
              (\_ -> only . scaleT α . TCP.head')
{-# INLINE scale #-}

first
    :: forall ns ms os. (Known Length ns, Known Length ms)
    => TOp ns ms
    -> TOp (ns ++ os) (ms ++ os)
first = (*** idOp @os)

konst
    :: forall n ns. SingI n
    => Uniform n ns
    -> (forall a. RealFloat a => a)
    -> TOp '[] ns
konst u x = TOp (\_ -> TCP.replicate (TT.konst x) u)
                (\_ _ -> Ø)

negate :: SingI ns => TOp '[ns] '[ns]
negate = scale (-1)

map' :: SingI n
      => (forall a. RealFloat a => a -> a)
     -> (forall a. RealFloat a => a -> a)
     -> TOp '[n] '[n]
map' f f' = liftOp (US UØ)
                   (VF (f . getI . TCV.head')
                       ((:+ ØV) . f' . getI . TCV.head')
                   )
{-# INLINE map' #-}


map :: SingI n
    => (forall a. RealFloat a => a -> a)
    -> TOp '[n] '[n]
map f = map' f (diff f)
{-# INLINE map #-}

add :: SingI n
    => TOp '[ n, n ] '[ n ]
add = TOp (\case x :< y :< Ø -> only $ sumT [x,y])
          (\_ -> \case
            dtdz :< Ø -> dtdz :< dtdz :< Ø
          )
{-# INLINE add #-}

zipN'
    :: SingI n
    => Uniform n ns
    -> (forall a. RealFloat a => Vec (Len ns) a -> a)
    -> (forall a. RealFloat a => Vec (Len ns) a -> Vec (Len ns) a)
    -> TOp ns '[n]
zipN' u f f' = liftOp u (VF f f')
{-# INLINE zipN' #-}

zipN
    :: SingI n
    => Uniform n ns
    -> (forall a. RealFloat a => Vec (Len ns) a -> a)
    -> TOp ns '[n]
zipN u f = zipN' u f (grad f)
{-# INLINE zipN #-}

zip'
    :: SingI n
    => (forall a. RealFloat a => a -> a -> a)
    -> (forall a. RealFloat a => a -> a -> (a, a))
    -> TOp '[ n, n ] '[ n ]
zip' f f' = zipN' (US (US UØ)) (\case I x :* I y :* ØV -> f x y)
                               (\case I x :* I y :* ØV ->
                                        let (dx, dy) = f' x y
                                        in  dx :+ dy :+ ØV
                               )
{-# INLINE zip' #-}

zip
    :: SingI n
    => (forall a. RealFloat a => a -> a -> a)
    -> TOp '[ n, n ] '[ n ]
zip f = zipN (US (US UØ)) (\case I x :* I y :* ØV -> f x y)
{-# INLINE zip #-}

zip3'
    :: SingI n
    => (forall a. RealFloat a => a -> a -> a -> a)
    -> (forall a. RealFloat a => a -> a -> a -> (a, a, a))
    -> TOp '[ n, n, n ] '[ n ]
zip3' f f' = zipN' (US (US (US UØ))) (\case I x :* I y :* I z :* ØV -> f x y z)
                                     (\case I x :* I y :* I z :* ØV ->
                                              let (dx, dy, dz) = f' x y z
                                              in  dx :+ dy :+ dz :+ ØV
                                     )
{-# INLINE zip3' #-}

zip3
    :: SingI n
    => (forall a. RealFloat a => a -> a -> a -> a)
    -> TOp '[ n, n, n ] '[ n ]
zip3 f = zipN (US (US (US UØ))) (\case I x :* I y :* I z :* ØV -> f x y z)
{-# INLINE zip3 #-}

replicate
    :: SingI n
    => Uniform n ns
    -> TOp '[ n ] ns
replicate u = TOp (flip TCP.replicate u . TCP.head')
                  (\_ -> only . sumT . toList . prodToVec I u)
{-# INLINE replicate #-}

duplicate
    :: SingI n
    => TOp '[ n ] '[ n, n ]
duplicate = TOp (\case x :< Ø -> x :< x :< Ø)
                (\_ -> \case
                    d1 :< d2 :< Ø -> only $ sumT [d1, d2]
                )
{-# INLINE duplicate #-}

inner
    :: forall ms ns o. (SingI (o ': ns), SingI (ms >: o), SingI (ms ++ ns))
    => Length ms
    -> Length ns
    -> TOp '[ms >: o, o ': ns] '[ ms ++ ns ]
inner lM lN = gmul lM (LS LZ) lN
                \\ appendSnoc lM (Proxy @o)
{-# INLINE inner #-}

outer
    :: (SingI ms, SingI ns, SingI (ms ++ ns))
    => Length ms
    -> Length ns
    -> TOp '[ms, ns] '[ ms ++ ns ]
outer lM lN = gmul lM LZ lN
                \\ appendNil lM

dot :: SingI m
    => TOp '[ '[m], '[m] ] '[ '[] ]
dot = inner LZ LZ
{-# INLINE dot #-}

swap :: TOp '[ms,ns] '[ns,ms]
swap = TOp (\case x :< y :< Ø -> y :< x :< Ø)
           (\_ -> \case
              d1 :< d2 :< Ø -> d2 :< d1 :< Ø
           )
{-# INLINE swap #-}
