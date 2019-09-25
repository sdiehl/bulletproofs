module Example.RangeProof where

import Protolude
import Control.Monad.Random (MonadRandom, getRandomR)
import Data.Curve.Weierstrass.SECP256K1 (Fr)
import Data.Field.Galois (rnd)

import qualified Bulletproofs.RangeProof as RP
import qualified Bulletproofs.MultiRangeProof as MRP
import Bulletproofs.Utils (commit)

testSingleRangeProof :: Integer -> (Fr, Fr) -> IO Bool
testSingleRangeProof upperBound (v, vBlinding) = do
  let vCommit = commit v vBlinding
  -- Prover
  proofE <- runExceptT $ RP.generateProof upperBound (v, vBlinding)
  -- Verifier
  case proofE of
    Left err -> panic $ show err
    Right proof@RP.RangeProof{..}
      -> pure $ RP.verifyProof upperBound vCommit proof

testMultiRangeProof :: Integer -> [(Fr, Fr)] -> IO Bool
testMultiRangeProof upperBound vsAndvBlindings = do
  let vCommits = fmap (uncurry commit) vsAndvBlindings
  -- Prover
  proofE <- runExceptT $ MRP.generateProof upperBound vsAndvBlindings
  -- Verifier
  case proofE of
    Left err -> panic $ show err
    Right proof@RP.RangeProof{..}
      -> pure $ MRP.verifyProof upperBound vCommits proof

setupV :: MonadRandom m => Integer -> m (Fr, Fr)
setupV n = do
  v <- fromInteger <$> getRandomR (1, 2^n - 1) -- value that needs to be in a certain range
  vBlinding <- rnd -- blinding value
  pure (v, vBlinding)

runExamples :: IO ()
runExamples = do
  n <- (2 ^) <$> getRandomR (0 :: Integer, 7)
  let upperBound = 2 ^ n
  (v, vBlinding) <- setupV n
  singleRangeProof <- testSingleRangeProof upperBound (v, vBlinding)
  putText $ "Single-range proof success: " <> show singleRangeProof
  vsAndvBlindings <- replicateM 5 (setupV n)
  testMultiRangeProof <- testMultiRangeProof upperBound vsAndvBlindings
  putText $ "Multi-range proof success: " <> show singleRangeProof

