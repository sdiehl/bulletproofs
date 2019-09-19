{-# LANGUAGE RecordWildCards, ViewPatterns #-}
module Bulletproofs.ArithmeticCircuit.Verifier where

import Protolude hiding (head)
import Data.List (head)

import Data.Curve.Weierstrass.SECP256K1 (PA, Fr)
import Data.Curve.Weierstrass

import Bulletproofs.Utils hiding (shamirZ)
import qualified Bulletproofs.InnerProductProof as IPP

import Bulletproofs.ArithmeticCircuit.Internal

-- | Verify that a zero-knowledge proof holds
-- for an arithmetic circuit given committed input values
verifyProof
  :: [PA]
  -> ArithCircuitProof Fr PA
  -> ArithCircuit Fr
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

    hs' = zipWith mul hs (powerVector (recip y) n)

    uChallenge = shamirU tBlinding mu t
    u = gen `mul` uChallenge

    verifyTPoly = lhs == rhs
      where
        lhs = commit t tBlinding
        rhs = (gen `mul` gExp)
            `add` tCommitsExpSum
            `add` sumExps vExp vCommits
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
        gExp = (*) x <$> (powerVector (recip y) n `hadamard` zwR)
        hExp = (((*) x <$> zwL) ^+^ zwO) ^-^ ys
        commitmentLR = (aiCommit `mul` x)
                     `add` (aoCommit `mul` (x ^ 2))
                     `add` (sCommit `mul` (x ^ 3))
                     `add` sumExps gExp gs
                     `add` sumExps hExp hs'
                     `add` (inv (h `mul` mu))
                     `add` (u `mul` t)
