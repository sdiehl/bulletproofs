{-# LANGUAGE RecordWildCards, MultiWayIf, NamedFieldPuns  #-}

module Bulletproofs.MultiRangeProof.Verifier (
  verifyProof,
  verifyTPoly,
  verifyLRCommitment,
) where

import Protolude

import Data.Curve.Weierstrass.SECP256K1 (PA, Fr)
import Data.Curve.Weierstrass hiding (char)

import Bulletproofs.RangeProof.Internal
import Bulletproofs.Utils
import Bulletproofs.InnerProductProof as IPP hiding (verifyProof)
import qualified Bulletproofs.InnerProductProof as IPP

-- | Verify that a commitment was computed from a value in a given range
verifyProof
  :: Integer        -- ^ Range upper bound
  -> [PA]   -- ^ Commitments of in-range values
  -> RangeProof Fr PA
  -- ^ Proof that a secret committed value lies in a certain interval
  -> Bool
verifyProof upperBound vCommits proof@RangeProof{..}
  = and
      [ verifyTPoly n vCommitsExp2 proof x y z
      , verifyLRCommitment n mExp2 proof x y z
      ]
  where
    x = shamirX aCommit sCommit t1Commit t2Commit y z
    y = shamirY aCommit sCommit
    z = shamirZ aCommit sCommit y
    n = logBase2 upperBound
    m = length vCommits
    -- Vector of values passed must be of length 2^x
    vCommitsExp2 = vCommits ++ residueCommits
    residueCommits = replicate (2 ^ log2Ceil m - m) O
    mExp2 = fromIntegral $ length vCommitsExp2

-- | Verify the constant term of the polynomial t
-- t = t(x) = t0 + t1*x + t2*x^2
-- This is what binds the proof to the actual original Pedersen commitment V to the actual value
verifyTPoly
  :: Integer         -- ^ Dimension n of the vectors
  -> [PA]   -- ^ Commitments of in-range values
  -> RangeProof Fr PA
  -- ^ Proof that a secret committed value lies in a certain interval
  -> Fr              -- ^ Challenge x
  -> Fr              -- ^ Challenge y
  -> Fr              -- ^ Challenge z
  -> Bool
verifyTPoly n vCommits proof@RangeProof{..} x y z
  = lhs == rhs
  where
    m = fromIntegral $ length vCommits
    lhs = commit t tBlinding
    rhs =
          sumExps ((*) (z ^ 2) <$> powerVector z m) vCommits
          `add`
          (gen `mul` delta n m y z)
          `add`
          (t1Commit `mul` x)
          `add`
          (t2Commit `mul` (x ^ 2))

-- | Verify the inner product argument for the vectors l and r that form t
verifyLRCommitment
  :: Integer         -- ^ Dimension n of the vectors
  -> Integer
  -> RangeProof Fr PA
  -- ^ Proof that a secret committed value lies in a certain interval
  -> Fr              -- ^ Challenge x
  -> Fr              -- ^ Challenge y
  -> Fr              -- ^ Challenge z
  -> Bool
verifyLRCommitment n m proof@RangeProof{..} x y z
  = IPP.verifyProof
      nm
      IPP.InnerProductBase { bGs = gs, bHs = hs', bH = u }
      commitmentLR
      productProof
  where
    commitmentLR = computeLRCommitment n m aCommit sCommit t tBlinding mu x y z hs'
    hs' = zipWith (\yi hi-> hi `mul` recip yi) (powerVector y nm) hs
    uChallenge = shamirU tBlinding mu t
    u = gen `mul` uChallenge
    nm = n * m
