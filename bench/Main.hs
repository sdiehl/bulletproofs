{-# LANGUAGE NoImplicitPrelude #-}

-- To run this, run "stack bench"

module Main where

import Protolude

import Criterion.Main
import Data.Curve.Weierstrass.SECP256K1 (PA, Fr)

import qualified Bulletproofs.RangeProof as RP
import qualified Bulletproofs.Utils as Utils

upperBound :: Integer
upperBound = 2 ^ (2 ^ 6)

benchInput :: (Fr, Fr)
benchInput = (7238283, 827361)

proof :: (Fr, Fr) -> IO (RP.RangeProof Fr PA)
proof input = do
  Right proof <- runExceptT $ RP.generateProof upperBound input
  pure proof

prepareProof :: IO (PA, RP.RangeProof Fr PA)
prepareProof = do
  proofObj <- proof benchInput
  let cm = uncurry Utils.commit benchInput
  pure (cm, proofObj)

verify :: PA -> RP.RangeProof Fr PA -> Bool
verify = RP.verifyProof upperBound

rangeproofBenchmarks :: [Benchmark]
rangeproofBenchmarks
  = [ bench "Proving" $ nfAppIO proof benchInput
    , env prepareProof $ \ ~(cm, proofObj) -> bench "Verifying" $ nf (uncurry verify) (cm, proofObj)
    ]

main :: IO ()
main = defaultMain
  [ bgroup "Rangeproof" rangeproofBenchmarks ]
