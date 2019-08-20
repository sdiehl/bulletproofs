{-# LANGUAGE NoImplicitPrelude #-}

-- To run this, run "stack bench"

module Main where

import Protolude

import Criterion.Main
import qualified Crypto.PubKey.ECC.Types as Crypto
import qualified Bulletproofs.RangeProof as RP
import qualified Bulletproofs.Utils as Utils
import qualified Bulletproofs.Fq as Fq

upperBound :: Integer
upperBound = 2 ^ (2 ^ 6)

benchInput :: (Fq.Fq, Fq.Fq)
benchInput = (7238283, 827361)

proof :: (Fq.Fq, Fq.Fq) -> IO (RP.RangeProof Fq.Fq)
proof input = do
  Right proof <- runExceptT $ RP.generateProof upperBound input
  pure proof

prepareProof :: IO (Crypto.Point, RP.RangeProof Fq.Fq)
prepareProof = do
  proofObj <- proof benchInput
  let cm = Utils.commit (fst benchInput) (snd benchInput)
  pure (cm, proofObj)

verify :: Crypto.Point -> RP.RangeProof Fq.Fq -> Bool
verify = RP.verifyProof upperBound

rangeproofBenchmarks :: [Benchmark]
rangeproofBenchmarks
  = [ bench "Proving" $ nfAppIO proof benchInput
    , env prepareProof $ \ ~(cm, proofObj) -> bench "Verifying" $ nf (uncurry verify) (cm, proofObj)
    ]

main :: IO ()
main = defaultMain
  [ bgroup "Rangeproof" rangeproofBenchmarks ]
