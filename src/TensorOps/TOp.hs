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

import           Data.Proxy
import           Data.Type.Combinator
import           Data.Type.Index
import           Data.Type.Length
import           Data.Type.Product
import           Data.Type.Uniform
import           Data.Type.Vector          as TCV
import           Numeric.AD
import           Prelude hiding            (map, replicate, zip, negate)
import           TensorOps.Types hiding    (OpPipe(..))
import           Type.Class.Witness hiding (inner)
import           Type.Family.List
import           Type.Family.List.Util
import           Type.Family.Nat
import qualified Data.Type.Product.Util    as TCP

konst
    :: forall n ns. ()
    => Uniform n ns
    -> (forall a. Floating a => a)
    -> TOp '[] ns
konst u x = Lift UØ u (vrep (I (VF (\ØV -> x) (\ØV -> ØV))))
              \\ uniformLength u
{-# INLINE konst #-}

negate
    :: TOp '[ns] '[ns]
negate = Scale (-1)

-- | TODO: version with some data type w/ num instance?
map' :: (forall a. Floating a => a -> a)
     -> (forall a. Floating a => a -> a)
     -> TOp '[n] '[n]
map' f f' = Lift (US UØ) (US UØ)
                 (VF (f . getI . TCV.head')
                     ((:+ ØV) . f' . getI . TCV.head')
               :+ ØV
                 )
{-# INLINE map' #-}


map :: (forall a. Floating a => a -> a)
    -> TOp '[n] '[n]
map f = map' f (diff f)
{-# INLINE map #-}

mapN' :: Uniform n ns
      -> (forall a. Floating a => a -> a)
      -> (forall a. Floating a => a -> a)
      -> TOp ns ns
mapN' u f f' = Lift u u (vgen_ $ \i -> I (VF (\v -> f (index' i v))
                                             (\v -> vgen_ $ \i' -> I $
                                                      if i' == i
                                                        then f' (index' i v)
                                                        else 0
                                             )
                                         )
                        )
                 \\ uniformLength u
{-# INLINE mapN' #-}

mapN :: Uniform n ns
     -> (forall a. Floating a => a -> a)
     -> TOp ns ns
mapN u f = mapN' u f (diff f)
{-# INLINE mapN #-}

add :: TOp '[ n, n ] '[ n ]
add = SumT (US (US UØ))
{-# INLINE add #-}

zip' :: Uniform n ns
     -> (forall a. Floating a => Vec (Len ns) a -> a)
     -> (forall a. Floating a => Vec (Len ns) a -> Vec (Len ns) a)
     -> TOp ns '[n]
zip' u f f' = Lift u (US UØ) (VF f f' :+ ØV)
{-# INLINE zip' #-}

zip :: Uniform n ns
    -> (forall a. Floating a => Vec (Len ns) a -> a)
    -> TOp ns '[n]
zip u f = zip' u f (grad f)
{-# INLINE zip #-}

zip2'
    :: (forall a. Floating a => a -> a -> a)
    -> (forall a. Floating a => a -> a -> (a, a))
    -> TOp '[ n, n ] '[ n ]
zip2' f f' = zip' (US (US UØ)) (\case I x :* I y :* ØV -> f x y)
                               (\case I x :* I y :* ØV ->
                                        let (dx, dy) = f' x y
                                        in  dx :+ dy :+ ØV
                               )
{-# INLINE zip2' #-}

zip2
    :: (forall a. Floating a => a -> a -> a)
    -> TOp '[ n, n ] '[ n ]
zip2 f = zip (US (US UØ)) (\case I x :* I y :* ØV -> f x y)
{-# INLINE zip2 #-}

zip3'
    :: (forall a. Floating a => a -> a -> a -> a)
    -> (forall a. Floating a => a -> a -> a -> (a, a, a))
    -> TOp '[ n, n, n ] '[ n ]
zip3' f f' = zip' (US (US (US UØ))) (\case I x :* I y :* I z :* ØV -> f x y z)
                                    (\case I x :* I y :* I z :* ØV ->
                                             let (dx, dy, dz) = f' x y z
                                             in  dx :+ dy :+ dz :+ ØV
                                    )
{-# INLINE zip3' #-}

zip3
    :: (forall a. Floating a => a -> a -> a -> a)
    -> TOp '[ n, n, n ] '[ n ]
zip3 f = zip (US (US (US UØ))) (\case I x :* I y :* I z :* ØV -> f x y z)
{-# INLINE zip3 #-}

replicate
    :: Uniform n ns
    -> TOp '[ n ] ns
replicate u = Shuffle (TCP.replicate IZ u)
{-# INLINE replicate #-}

duplicate
    :: TOp '[ n ] '[ n, n ]
duplicate = replicate (US (US UØ))
{-# INLINE duplicate #-}

inner
    :: forall ms ns o. ()
    => Length ms
    -> Length ns
    -> TOp '[ms >: o, o ': ns] '[ ms ++ ns ]
inner lM lN = GMul lM (LS LZ) lN
                \\ appendSnoc lM (Proxy @o)
{-# INLINE inner #-}

dot :: TOp '[ '[m], '[m] ] '[ '[] ]
dot = inner LZ LZ
{-# INLINE dot #-}

swap :: TOp '[ms,ns] '[ns,ms]
swap = Shuffle (IS IZ :< IZ :< Ø)
{-# INLINE swap #-}
