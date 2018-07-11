{-# LANGUAGE RecordWildCards, MultiWayIf, NamedFieldPuns, ViewPatterns #-}

module Bulletproofs.RangeProof.Verifier (
  verifyProof,
  verifyTPoly,
  verifyLRCommitment,
) where

import Protolude
import Prelude (zipWith3)

import qualified Crypto.PubKey.ECC.Generate as Crypto
import qualified Crypto.PubKey.ECC.Prim as Crypto
import qualified Crypto.PubKey.ECC.Types as Crypto

import Bulletproofs.RangeProof.Internal
import Bulletproofs.Curve
import Bulletproofs.Utils
import Bulletproofs.Fq as Fq

import Bulletproofs.InnerProductProof as IPP hiding (verifyProof)
import qualified Bulletproofs.InnerProductProof as IPP

-- | Verify that a commitment was computed from a value in a given range
verifyProof
  :: Integer        -- ^ Range upper bound
  -> Crypto.Point   -- ^ Commitment of an in-range value
  -> RangeProof
  -- ^ Proof that a secret committed value lies in a certain interval
  -> Bool
verifyProof upperBound vCommit proof@RangeProof{..}
  = and
      [ verifyTPoly n vCommit proof x y z
      , verifyLRCommitment n proof x y z
      ]
  where
    x = shamirX aCommit sCommit t1Commit t2Commit y z
    y = shamirY aCommit sCommit
    z = shamirZ aCommit sCommit y
    hs' = zipWith (\yi hi-> inv yi `mulP` hi) (powerVector y n) hs
    n = logBase2 upperBound

-- | Verify the constant term of the polynomial t
-- t = t(x) = t0 + t1*x + t2*x^2
-- This is what binds the proof to the actual original Pedersen commitment V to the actual value
verifyTPoly
  :: Integer         -- ^ Dimension n of the vectors
  -> Crypto.Point    -- ^ Commitment of an in-range value
  -> RangeProof
  -- ^ Proof that a secret committed value lies in a certain interval
  -> Fq              -- ^ Challenge x
  -> Fq              -- ^ Challenge y
  -> Fq              -- ^ Challenge z
  -> Bool
verifyTPoly n vCommit proof@RangeProof{..} x y z
  = lhs == rhs
  where
    lhs = commit t tBlinding
    rhs = (fqSquare z `mulP` vCommit)
          `addP`
          (delta n y z `mulP` g)
          `addP`
          (x `mulP` t1Commit)
          `addP`
          (fqSquare x `mulP` t2Commit)

-- | Verify the inner product argument for the vectors l and r that form t
verifyLRCommitment
  :: Integer         -- ^ Dimension n of the vectors
  -> RangeProof
  -- ^ Proof that a secret committed value lies in a certain interval
  -> Fq              -- ^ Challenge x
  -> Fq              -- ^ Challenge y
  -> Fq              -- ^ Challenge z
  -> Bool
verifyLRCommitment n proof@RangeProof{..} x y z
  = IPP.verifyProof
      n
      IPP.InnerProductBase { bGs = gs, bHs = hs', bH = u }
      commitmentLR
      productProof
  where
    commitmentLR = computeLRCommitment n aCommit sCommit t tBlinding mu x y z hs'
    hs' = zipWith (\yi hi-> inv yi `mulP` hi) (powerVector y n) hs
    uChallenge = shamirU tBlinding mu t
    u = uChallenge `mulP` g


