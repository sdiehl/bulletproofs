{-# LANGUAGE RecordWildCards, MultiWayIf, NamedFieldPuns  #-}

module Bulletproofs.RangeProof.Verifier (
  verifyProof,
  verifyTPoly,
  verifyLRCommitment,
) where

import Protolude

import qualified Crypto.PubKey.ECC.Types as Crypto
import PrimeField (PrimeField(..), toInt)

import Bulletproofs.RangeProof.Internal
import Bulletproofs.Curve
import Bulletproofs.Utils

import qualified Bulletproofs.MultiRangeProof.Verifier as MRP

-- | Verify that a commitment was computed from a value in a given range
verifyProof
  :: KnownNat p
  => Integer        -- ^ Range upper bound
  -> Crypto.Point   -- ^ Commitments of in-range values
  -> RangeProof (PrimeField p)
  -- ^ Proof that a secret committed value lies in a certain interval
  -> Bool
verifyProof upperBound vCommit proof@RangeProof{..}
  = MRP.verifyProof upperBound [vCommit] proof

-- | Verify the constant term of the polynomial t
-- t = t(x) = t0 + t1*x + t2*x^2
-- This is what binds the proof to the actual original Pedersen commitment V to the actual value
verifyTPoly
  :: KnownNat p
  => Integer         -- ^ Dimension n of the vectors
  -> Crypto.Point    -- ^ Commitment of in-range value
  -> RangeProof (PrimeField p)
  -- ^ Proof that a secret committed value lies in a certain interval
  -> PrimeField p              -- ^ Challenge x
  -> PrimeField p              -- ^ Challenge y
  -> PrimeField p              -- ^ Challenge z
  -> Bool
verifyTPoly n vCommit
  = MRP.verifyTPoly n [vCommit]

-- | Verify the inner product argument for the vectors l and r that form t
verifyLRCommitment
  :: KnownNat p
  => Integer         -- ^ Dimension n of the vectors
  -> RangeProof (PrimeField p)
  -- ^ Proof that a secret committed value lies in a certain interval
  -> PrimeField p              -- ^ Challenge x
  -> PrimeField p              -- ^ Challenge y
  -> PrimeField p              -- ^ Challenge z
  -> Bool
verifyLRCommitment n
  = MRP.verifyLRCommitment n 1
