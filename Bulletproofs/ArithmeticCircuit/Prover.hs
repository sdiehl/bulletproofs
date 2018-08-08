{-# LANGUAGE RecordWildCards #-}
module Bulletproofs.ArithmeticCircuit.Prover where

import Protolude

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

generateProof
  :: (MonadRandom m)
  => ArithCircuit Fq
  -> ArithWitness Fq
  -> m ArithCircuitProof
generateProof ArithCircuit{..} ArithWitness{..} = do
  let GateWeights{..} = weights
  let Assignment{..} = inputs
  [aiBlinding, aoBlinding, sBlinding] <- replicateM 3 (Fq.random n)

  let aiCommit = commitBitVector aiBlinding aL aR  -- commitment to aL, aR
      aoCommit = commitBitVector aoBlinding aO []  -- commitment to aO

  (sL, sR) <- chooseBlindingVectors n              -- choose blinding vectors sL, sR
  let sCommit = commitBitVector sBlinding sL sR    -- commitment to sL, sR

  let y = shamirGxGxG aiCommit aoCommit sCommit
      z = shamirZ y
      ys = powerVector y n
      zs = drop 1 (powerVector z (qLen + 1))

      zwL = zs `vectorMatrixProduct` wL
      zwR = zs `vectorMatrixProduct` wR
      zwO = zs `vectorMatrixProduct` wO

      -- Polynomials
      [lPoly, rPoly] = computePolynomials aL aR aO sL sR y z zwL zwR zwO
      tPoly = multiplyPoly lPoly rPoly

      w = (aL `vectorMatrixProductT` wL)
        `fqAddV` (aR `vectorMatrixProductT` wR)
        `fqAddV` (aO `vectorMatrixProductT` wO)

      t2 = (aL `dotp` (aR `hadamardp` ys))
         - (aO `dotp` ys)
         + (zs `dotp` w)
         + delta n y zwL zwR

  tBlindings <- insertAt 2 (Fq.new 0) . (:) (Fq.new 0) <$> replicateM 5 (Fq.random n)
  let tCommits = zipWith commit tPoly tBlindings

  let x = shamirGs tCommits
      evalTCommit = foldl' addP Crypto.PointO (zipWith mulP (powerVector x 7) tCommits)

  let ls = evaluatePolynomial n lPoly x
      rs = evaluatePolynomial n rPoly x
      t = ls `dotp` rs

      commitTimesWeigths = commitBlinders `vectorMatrixProductT` commitmentWeights
      zGamma = dotp zs commitTimesWeigths
      tBlinding = sum (zipWith (\i blinding -> blinding * fqPower x i) [0..] tBlindings)
                + (fqSquare x * zGamma)

      mu = aiBlinding * x + aoBlinding * fqSquare x + sBlinding * fqCube x

  let uChallenge = shamirU tBlinding mu t
      u = uChallenge `mulP` g
      hs' = zipWith mulP (powerVector (inv y) n) hs
      gExp = (*) x <$> (powerVector (inv y) n `hadamardp` zwR)
      hExp = (((*) x <$> zwL) `fqAddV` zwO) `fqSubV` ys
      commitmentLR = (x `mulP` aiCommit)
                   `addP` (fqSquare x `mulP` aoCommit)
                   `addP` (fqCube x `mulP` sCommit)
                   `addP` foldl' addP Crypto.PointO (zipWith mulP gExp gs)
                   `addP` foldl' addP Crypto.PointO (zipWith mulP hExp hs')
                   `addP` Crypto.pointNegate curve (mu `mulP` h)
                   `addP` (t `mulP` u)

  let productProof = IPP.generateProof
                        IPP.InnerProductBase { bGs = gs, bHs = hs', bH = u }
                        commitmentLR
                        IPP.InnerProductWitness { ls = ls, rs = rs }

  pure ArithCircuitProof
      { tBlinding = tBlinding
      , mu = mu
      , t = t
      , aiCommit = aiCommit
      , aoCommit = aoCommit
      , sCommit = sCommit
      , tCommits = tCommits
      , productProof = productProof
      }
  where
    n = fromIntegral $ length (aL inputs) -- # multiplication gates
    qLen = fromIntegral $ length commitmentWeights
    removeSnd vs = take 1 vs ++ drop 2 vs

    computePolynomials aL aR aO sL sR y z zwL zwR zwO
      = [ [l0, l1, l2, l3]
        , [r0, r1, r2, r3]
        ]
      where
        l0 = replicate (fromIntegral n) (Fq.new 0)
        l1 = aL `fqAddV` (powerVector (inv y) n `hadamardp` zwR)
        l2 = aO
        l3 = sL

        r0 = zwO `fqSubV` powerVector y n
        r1 = (powerVector y n `hadamardp` aR) `fqAddV` zwL
        r2 = replicate (fromIntegral n) (Fq.new 0)
        r3 = powerVector y n `hadamardp` sR

