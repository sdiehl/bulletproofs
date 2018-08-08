module Bulletproofs.RangeProof.Prover (
  generateProof,
  generateProofUnsafe,
) where

import Protolude

import Crypto.Random.Types (MonadRandom(..))

import Bulletproofs.Utils (AsInteger, Field)
import Bulletproofs.RangeProof.Internal
import qualified Bulletproofs.MultiRangeProof.Prover as MRP

-- | Prove that a value lies in a specific range
generateProof
  :: (AsInteger f, Eq f, Field f, Show f, MonadRandom m)
  => Integer                -- ^ Upper bound of the range we want to prove
  -> (Integer, Integer)
  -- ^ Values we want to prove in range and their blinding factors
  -> ExceptT RangeProofError m (RangeProof f)
generateProof upperBound (v, vBlinding) =
  MRP.generateProof upperBound [(v, vBlinding)]

-- | Generate range proof from valid inputs
generateProofUnsafe
  :: (AsInteger f, Eq f, Field f, Show f, MonadRandom m)
  => Integer    -- ^ Upper bound of the range we want to prove
  -> (Integer, Integer)
  -- ^ Values we want to prove in range and their blinding factors
  -> m (RangeProof f)
generateProofUnsafe upperBound (v, vBlinding) =
  MRP.generateProofUnsafe upperBound [(v, vBlinding)]

