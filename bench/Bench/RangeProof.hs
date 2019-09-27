module Bench.RangeProof where

import Protolude
import Criterion.Main
import Data.Curve.Weierstrass.SECP256K1 (PA, Fr)

import qualified Bulletproofs.RangeProof as RP
import qualified Bulletproofs.Utils as Utils

upperBound :: Integer
upperBound = 2 ^ (2 ^ 6)

rangeInput :: (Fr, Fr)
rangeInput = (7238283, 827361)

runProver :: (Fr, Fr) -> IO (RP.RangeProof Fr PA)
runProver input = do
  proofE <- runExceptT $ RP.generateProof upperBound input
  case proofE of
    Left err -> panic $ "Prover encountered error: " <> show err
    Right proof -> pure proof

prepareProof :: IO (PA, RP.RangeProof Fr PA)
prepareProof = do
  let cm = uncurry Utils.commit rangeInput
  proofObj <- runProver rangeInput
  pure (cm, proofObj)

verify :: PA -> RP.RangeProof Fr PA -> Bool
verify = RP.verifyProof upperBound

benchmark :: [Benchmark]
benchmark
  = [ bench "Proving" $ nfAppIO runProver rangeInput
    , env prepareProof $ \ ~(cm, proofObj) ->
        bench "Verifying" $ nf (uncurry $ RP.verifyProof upperBound) (cm, proofObj)
    ]
