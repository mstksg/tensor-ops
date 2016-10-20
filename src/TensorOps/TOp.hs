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
import           Data.Type.Product.Util    as TCP
import           Data.Type.Uniform
import           Data.Type.Vector          as TCV
import           Prelude hiding            (map, replicate, zip)
import           TensorOps.Types hiding    (OpPipe(..))
import           Type.Class.Witness hiding (inner)
import           Type.Family.List
import           Type.Family.List.Util
import           Type.Family.Nat

konst
    :: forall o. ()
    => (forall a. Floating a => a)
    -> TOp '[] '[o]
konst x = Lift UØ (I (\ØV -> x))
{-# INLINE konst #-}

map :: (forall a. Floating a => a -> a)
    -> TOp '[n] '[n]
map f = Lift (US UØ) (US UØ) (VF (f . getI . TCV.head') :+ ØV)
{-# INLINE map #-}

mapN :: Uniform n ns
     -> (forall a. Floating a => a -> a)
     -> TOp ns ns
mapN u f = Lift u u (vgen_ $ \i -> I (VF $ \v -> f (index' i v)))
             \\ uniformLength u
{-# INLINE mapN #-}

zip :: Uniform n ns
    -> (forall a. Floating a => Vec (Len ns) a -> a)
    -> TOp ns '[n]
zip u f = Lift u (US UØ) (VF f :+ ØV)
{-# INLINE zip #-}

zip2
    :: (forall a. Floating a => a -> a -> a)
    -> TOp '[ n, n ] '[ n ]
zip2 f = zip (US (US UØ)) (\case I x :* I y :* ØV -> f x y)
{-# INLINE zip2 #-}

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

-- transpose :: TOp '[ '[m,n] ] '[ '[n,m] ]
-- transpose = Transp Refl (IS IZ :< IZ :< Ø)

-- sum :: Known Length ns => TOp '[n ': ns] '[ns]
-- sum = Fold known F.sum
