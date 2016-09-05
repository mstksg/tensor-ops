{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE KindSignatures   #-}
{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE TypeOperators    #-}

import           Data.Kind
import           Data.Singletons
import           Data.Type.Index
import           Data.Type.Length
import           Data.Type.Product
import           Data.Type.Uniform
import           GHC.TypeLits
import           TensorOps.LTensor
import           TensorOps.Types
import           Type.Class.Known
import           Type.Family.List
import qualified TensorOps.TOp     as TO


ffLayer
    -- :: (SingI '[o,i], SingI '[o], SingI '[i])
    -- :: (SingI '[ '[i], '[o,i], '[o]], SingI '[ '[o] ], SingI '[ '[o,i], '[i]], SingI '[ '[o], '[o] ])
    -- :: (SingI o, SingI i)
    :: (SingI i, SingI o)
    => TensorOp '[ '[i], '[o,i], '[o]] '[ '[o] ]
ffLayer = Pop (LS (LS LZ)) known (Shuffle (IS IZ :< IZ :< Ø))
        $ Pop known        known (GMul (LS LZ) (LS LZ) LZ)
        $ Pop known        known (TO.zip2 (+))
        $ OPØ

data Layer :: ([k] -> Type) -> k -> k -> Type where
    L :: { lOp      :: TensorOp ('[i] ': os) '[ '[o] ]
         , lParams  :: Prod l os
         } -> Layer l i o

main :: IO ()
main = print 1
