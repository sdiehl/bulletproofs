module Bulletproofs.RangeProof.Prover (
  generateProof,
  generateProofUnsafe,
) where

import Protolude

import Control.Monad.Random (MonadRandom)
import Data.Curve.Weierstrass.SECP256K1 (PA, Fr)

import Bulletproofs.RangeProof.Internal
import qualified Bulletproofs.MultiRangeProof.Prover as MRP

-- | Prove that a value lies in a specific range
generateProof
  :: (MonadRandom m)
  => Integer                -- ^ Upper bound of the range we want to prove
  -> (Fr, Fr)
  -- ^ Values we want to prove in range and their blinding factors
  -> ExceptT (RangeProofError Fr) m (RangeProof Fr PA)
generateProof upperBound (v, vBlinding) =
  MRP.generateProof upperBound [(v, vBlinding)]

-- | Generate range proof from valid inputs
generateProofUnsafe
  :: (MonadRandom m)
  => Integer    -- ^ Upper bound of the range we want to prove
  -> (Fr, Fr)
  -- ^ Values we want to prove in range and their blinding factors
  -> m (RangeProof Fr PA)
generateProofUnsafe upperBound (v, vBlinding) =
  MRP.generateProofUnsafe upperBound [(v, vBlinding)]

