{-# LANGUAGE RecordWildCards, MultiWayIf #-}

module Bulletproofs.RangeProof.Verifier (
  verifyProof,
  verifyTPoly,
  verifyLRCommitment,
) where

import Protolude

import Data.Curve.Weierstrass.SECP256K1 (PA, Fr)

import Bulletproofs.RangeProof.Internal
import qualified Bulletproofs.MultiRangeProof.Verifier as MRP

-- | Verify that a commitment was computed from a value in a given range
verifyProof
  :: Integer        -- ^ Range upper bound
  -> PA   -- ^ Commitments of in-range values
  -> RangeProof Fr PA
  -- ^ Proof that a secret committed value lies in a certain interval
  -> Bool
verifyProof upperBound vCommit proof@RangeProof{..}
  = MRP.verifyProof upperBound [vCommit] proof

-- | Verify the constant term of the polynomial t
-- t = t(x) = t0 + t1*x + t2*x^2
-- This is what binds the proof to the actual original Pedersen commitment V to the actual value
verifyTPoly
  :: Integer         -- ^ Dimension n of the vectors
  -> PA    -- ^ Commitment of in-range value
  -> RangeProof Fr PA
  -- ^ Proof that a secret committed value lies in a certain interval
  -> Fr              -- ^ Challenge x
  -> Fr              -- ^ Challenge y
  -> Fr              -- ^ Challenge z
  -> Bool
verifyTPoly n vCommit
  = MRP.verifyTPoly n [vCommit]

-- | Verify the inner product argument for the vectors l and r that form t
verifyLRCommitment
  :: Integer         -- ^ Dimension n of the vectors
  -> RangeProof Fr PA
  -- ^ Proof that a secret committed value lies in a certain interval
  -> Fr              -- ^ Challenge x
  -> Fr              -- ^ Challenge y
  -> Fr              -- ^ Challenge z
  -> Bool
verifyLRCommitment n
  = MRP.verifyLRCommitment n 1
