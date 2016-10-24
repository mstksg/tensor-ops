{-# LANGUAGE ApplicativeDo       #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}

import           Control.Exception
import           Control.Monad
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans.State.Strict
import           Data.Either.Validation
import           Data.Finite
import           Data.Foldable
import           Data.IDX
import           Data.Kind
import           Data.Maybe
import           Data.Proxy
import           Data.String
import           Data.Type.Combinator
import           Data.Type.Product
import           Data.Type.Vector
import           GHC.TypeLits
import           System.Directory
import           System.FilePath
import           System.Random.MWC
import           TensorOps.Backend.BTensor
import           TensorOps.Types
import           Text.Printf
import           Type.Family.Nat
import qualified Codec.Compression.GZip           as GZ
import qualified Data.ByteString.Lazy             as BS
import qualified Data.Text.Lazy                   as T
import qualified Data.Text.Lazy.Encoding          as T
import qualified Data.Text.Lazy.IO                as T
import qualified Data.Vector.Unboxed              as VU
import qualified Network.HTTP.Simple              as HTTP
import qualified TensorOps.Tensor                 as TT

mnistBase :: String
mnistBase = "http://yann.lecun.com/exdb/mnist"

dataDir :: FilePath
dataDir = "data/mnist"

mnistFiles :: Matrix '[N2, N2] FilePath
mnistFiles = ("train-images-idx3-ubyte" :+ "train-labels-idx1-ubyte" :+ ØV)
          :* ("t10k-images-idx3-ubyte"  :+ "t10k-labels-idx1-ubyte"  :+ ØV)
          :* ØV

main :: IO ()
main = do
    createDirectoryIfMissing True dataDir

    printf "Loading data from %s\n" dataDir
    mnistBs <- forM mnistFiles $ \u -> do
      BS.readFile (dataDir </> u) `catch` \(_ :: IOException) -> do
        printf "'%s' not found; downloading from %s ...\n" u mnistBase
        b <- GZ.decompress . HTTP.getResponseBody
               <$> HTTP.httpLBS (fromString (mnistBase </> u -<.> "gz"))
        BS.writeFile (dataDir </> u) b
        return b

    let f   :: Vec N2 FilePath
            -> Vec N2 BS.ByteString
            -> I (Validation [String] (FilePath, FilePath, IDXData, IDXLabels))
        f (I uIm :* I uLb :* ØV) (I bIm :* I bLb :* ØV) = I $ do
            im <- maybe (Failure [printf "Could not decode image %s." uIm]) Success
                    $ decodeIDX bIm
            lb <- maybe (Failure [printf "Could not decode labels %s." uLb]) Success
                    $ decodeIDXLabels bLb
            pure (uIm, uLb, im, lb)

        mnistDat' :: Either [String] (Vec N2 [(Int, VU.Vector Int)])
        mnistDat' = do
          imlb <- validationToEither . sequenceA $ vap f mnistFiles mnistBs
          forM imlb $ \(uIm, uLb, im, lb) ->
            maybe (Left [printf "Could not combine %s and %s." uIm uLb]) Right
              $ labeledIntData lb im

    mnistDat <- either (ioError . userError . unlines) return mnistDat'

    learn (Proxy @(BTensorV (HMat Double))) mnistDat

processDat
    :: forall (n :: Nat) (l :: Nat) t. (Num (ElemT t), KnownNat n, KnownNat l, Tensor t)
    => (Int, VU.Vector Int)
    -> Maybe (t '[n], t '[l])
processDat (l,d) = (,) <$> x <*> y
  where
    x :: Maybe (t '[n])
    x = TT.fromList . map fromIntegral $ VU.toList d
    y :: Maybe (t '[l])
    y = flip fmap (packFinite (fromIntegral l) :: Maybe (Finite l)) $ \l' ->
          TT.generate $ \(i :< Ø) -> if i == l' then 1 else 0

learn
    :: Proxy t
    -> Vec N2 [(Int, VU.Vector Int)]
    -> IO ()
learn _ dat = withSystemRandom $ \g -> do
    print ()
