{-# LANGUAGE RecordWildCards, ViewPatterns #-}
module Bulletproofs.ArithmeticCircuit.Verifier where

import Protolude hiding (head)
import Data.List (head)

import qualified Crypto.PubKey.ECC.Prim as Crypto
import qualified Crypto.PubKey.ECC.Types as Crypto
import PrimeField (PrimeField(..), toInt)

import Bulletproofs.Curve
import Bulletproofs.Utils hiding (shamirZ)
import Bulletproofs.RangeProof.Internal hiding (delta)
import qualified Bulletproofs.InnerProductProof as IPP

import Bulletproofs.ArithmeticCircuit.Internal

-- | Verify that a zero-knowledge proof holds
-- for an arithmetic circuit given committed input values
verifyProof
  :: (KnownNat p)
  => [Crypto.Point]
  -> ArithCircuitProof (PrimeField p)
  -> ArithCircuit (PrimeField p)
  -> Bool
verifyProof vCommits proof@ArithCircuitProof{..} (padCircuit -> ArithCircuit{..})
  = verifyLRCommitment && verifyTPoly
  where
    GateWeights{..} = weights
    n = fromIntegral $ length $ head wL
    qLen = fromIntegral $ length wL

    x = shamirGs tCommits
    y = shamirGxGxG aiCommit aoCommit sCommit
    z = shamirZ y

    ys = powerVector y n
    zs = drop 1 (powerVector z (qLen + 1))
    zwL = zs `vectorMatrixProduct` wL
    zwR = zs `vectorMatrixProduct` wR
    zwO = zs `vectorMatrixProduct` wO

    hs' = zipWith mulP (powerVector (recip y) n) hs

    wLCommit = sumExps (zs `vectorMatrixProduct` wL) hs'
    wRCommit = sumExps wRExp gs
    wOCommit = sumExps (zs `vectorMatrixProduct` wO) hs'
    wRExp = powerVector (recip y) n `hadamardp` (zs `vectorMatrixProduct` wL)

    uChallenge = shamirU tBlinding mu t
    u = uChallenge `mulP` g

    verifyTPoly = lhs == rhs
      where
        lhs = commit t tBlinding
        rhs = (gExp `mulP` g)
            `addP` tCommitsExpSum
            `addP` sumExps vExp vCommits
        gExp = (x ^ 2) * (k + cQ)
        cQ = zs `dot` cs
        vExp = (*) (x ^ 2) <$> (zs `vectorMatrixProduct` commitmentWeights)
        k = delta n y zwL zwR
        xs = 0 : x : 0 : (((^) x) <$> [3..6])
        tCommitsExpSum = sumExps xs tCommits

    verifyLRCommitment
      = IPP.verifyProof
          n
          IPP.InnerProductBase { bGs = gs, bHs = hs', bH = u }
          commitmentLR
          productProof
      where
        gExp = (*) x <$> (powerVector (recip y) n `hadamardp` zwR)
        hExp = (((*) x <$> zwL) ^+^ zwO) ^-^ ys
        commitmentLR = (x `mulP` aiCommit)
                     `addP` ((x ^ 2) `mulP` aoCommit)
                     `addP` ((x ^ 3) `mulP` sCommit)
                     `addP` sumExps gExp gs
                     `addP` sumExps hExp hs'
                     `addP` Crypto.pointNegate curve (mu `mulP` h)
                     `addP` (t `mulP` u)
