{-# LANGUAGE RecordWildCards #-}
module Bulletproofs.ArithmeticCircuit.Verifier where

import Protolude hiding (head)
import Data.List (head)

import Crypto.Random.Types (MonadRandom(..))
import qualified Crypto.PubKey.ECC.Generate as Crypto
import qualified Crypto.PubKey.ECC.Prim as Crypto
import qualified Crypto.PubKey.ECC.Types as Crypto

import Bulletproofs.Fq as Fq
import Bulletproofs.Curve
import Bulletproofs.Utils hiding (shamirZ)
import Bulletproofs.RangeProof.Internal hiding (delta)
import qualified Bulletproofs.InnerProductProof as IPP

import Bulletproofs.ArithmeticCircuit.Internal

verifyProof
  :: [Crypto.Point]
  -> ArithCircuitProof
  -> ArithCircuit Fq
  -> Bool
verifyProof vCommits proof@ArithCircuitProof{..} ArithCircuit{..}
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

    hs' = zipWith mulP (powerVector (inv y) n) hs

    wLCommit = foldl' addP Crypto.PointO (zipWith mulP (zs `vectorMatrixProduct` wL) hs')
    wRCommit = foldl' addP Crypto.PointO (zipWith mulP wRExp gs)
    wOCommit = foldl' addP Crypto.PointO (zipWith mulP (zs `vectorMatrixProduct` wO) hs')
    wRExp = powerVector (inv y) n `hadamardp` (zs `vectorMatrixProduct` wL)

    uChallenge = shamirU tBlinding mu t
    u = uChallenge `mulP` g

    verifyTPoly = lhs == rhs
      where
        lhs = commit t tBlinding
        rhs = (gExp `mulP` g)
            `addP` tCommitsExpSum
            `addP` foldl' addP Crypto.PointO ( zipWith mulP vExp vCommits )
        gExp = fqSquare x * (k + cQ)
        cQ = zs `dotp` cs
        vExp = (*) (fqSquare x) <$> (zs `vectorMatrixProduct` commitmentWeights)
        k = delta n y zwL zwR
        xs = Fq.new 0 : x : Fq.new 0 : (fqPower x <$> [3..6])
        tCommitsExpSum = foldl' addP Crypto.PointO (zipWith mulP xs tCommits)

    verifyLRCommitment
      = IPP.verifyProof
          n
          IPP.InnerProductBase { bGs = gs, bHs = hs', bH = u }
          commitmentLR
          productProof
      where
        gExp = (*) x <$> (powerVector (inv y) n `hadamardp` zwR)
        hExp = (((*) x <$> zwL) `fqAddV` zwO) `fqSubV` ys
        commitmentLR = (x `mulP` aiCommit)
                     `addP` (fqSquare x `mulP` aoCommit)
                     `addP` (fqCube x `mulP` sCommit)
                     `addP` foldl' addP Crypto.PointO (zipWith mulP gExp gs)
                     `addP` foldl' addP Crypto.PointO (zipWith mulP hExp hs')
                     `addP` Crypto.pointNegate curve (mu `mulP` h)
                     `addP` (t `mulP` u)
