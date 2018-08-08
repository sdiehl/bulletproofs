{-# LANGUAGE RecordWildCards, MultiWayIf, ScopedTypeVariables #-}

module Bulletproofs.MultiRangeProof.Prover (
  generateProof,
  generateProofUnsafe,
) where

import Protolude

import Crypto.Random.Types (MonadRandom(..))
import Crypto.Number.Generate (generateMax)
import qualified Crypto.PubKey.ECC.Generate as Crypto
import qualified Crypto.PubKey.ECC.Prim as Crypto
import qualified Crypto.PubKey.ECC.Types as Crypto
import Linear.Vector ((^+^), (^-^))
import Linear.Metric (dot)

import Bulletproofs.Curve
import Bulletproofs.Utils
import Bulletproofs.RangeProof.Internal

import Bulletproofs.InnerProductProof as IPP hiding (generateProof)
import qualified Bulletproofs.InnerProductProof as IPP

-- | Prove that a list of values lie in a specific range
generateProof
  :: (AsInteger f, Eq f, Field f, Show f, MonadRandom m)
  => Integer                -- ^ Upper bound of the range we want to prove
  -> [(Integer, Integer)]
  -- ^ Values we want to prove in range and their blinding factors
  -> ExceptT RangeProofError m (RangeProof f)
generateProof upperBound vsAndvBlindings = do
  unless (upperBound < q) $ throwE $ UpperBoundTooLarge upperBound

  case doubleLogM of
     Nothing -> throwE $ NNotPowerOf2 upperBound
     Just n -> do
       unless (checkRanges n vs) $ throwE $ ValuesNotInRange vs

       lift $ generateProofUnsafe upperBound vsAndvBlindingsExp2

  where
    doubleLogM :: Maybe Integer
    doubleLogM = do
      x <- logBase2M upperBound
      logBase2M x
      pure x
    vs = fst <$> vsAndvBlindings
    m = length vsAndvBlindings
    residue = replicate (2 ^ log2Ceil m - m) (0, 0)
    -- Vector of values passed must be of length 2^x
    vsAndvBlindingsExp2 = vsAndvBlindings ++ residue


-- | Generate range proof from valid inputs
generateProofUnsafe
  :: forall f m
   . (AsInteger f, Eq f, Field f, Show f, MonadRandom m)
  => Integer    -- ^ Upper bound of the range we want to prove
  -> [(Integer, Integer)]
  -- ^ Values we want to prove in range and their blinding factors
  -> m (RangeProof f)
generateProofUnsafe upperBound vsAndvBlindings = do
  let n = logBase2 upperBound
      m = fromIntegral $ length vsAndvBlindings
      nm = n * m

      vsF :: [f]
      vsF = (fromInteger . fst) <$> vsAndvBlindings

      vBlindingsF :: [f]
      vBlindingsF = (fromInteger . snd) <$> vsAndvBlindings

  let aL = reversedEncodeBitMulti n vsF
      aR = complementaryVector aL

  (sL, sR) <- chooseBlindingVectors nm

  [aBlinding, sBlinding]
    <- replicateM 2 ((fromInteger :: Integer -> f) <$> generateMax (2^nm))

  (aCommit, sCommit) <- commitBitVectors aBlinding sBlinding aL aR sL sR

  -- Oracle generates y, z from a, c
  let y = shamirY aCommit sCommit
      z = shamirZ aCommit sCommit y

  let lrPoly@LRPolys{..} = computeLRPolys n m aL aR sL sR y z
      tPoly@TPoly{..} = computeTPoly lrPoly

  [t1Blinding, t2Blinding]
    <- replicateM 2 ((fromInteger :: Integer -> f) <$> generateMax (2^nm))


  let t1Commit = commit t1 t1Blinding
      t2Commit = commit t2 t2Blinding

  -- Oracle generates x from previous data in transcript
  let x = shamirX aCommit sCommit t1Commit t2Commit y z

  let ls = l0 ^+^ ((*) x <$> l1)
      rs = r0 ^+^ ((*) x <$> r1)
      t = t0 + (t1 * x) + (t2 * fSquare x)

  unless (t == dot ls rs) $
    panic "Error on: t = dot l r"

  unless (t1 == dot l1 r0 + dot l0 r1) $
    panic "Error on: t1 = dot l1 r0 + dot l0 r1"

  let tBlinding = sum (zipWith (\vBlindingF j -> (z ^ (j + 1)) * vBlindingF) vBlindingsF [1..m])
                + (t2Blinding * fSquare x)
                + (t1Blinding * x)
      mu = aBlinding + (sBlinding * x)

  let uChallenge = shamirU tBlinding mu t
      u = uChallenge `mulP` g
      hs' = zipWith (\yi hi-> recip yi `mulP` hi) (powerVector y nm) hs
      commitmentLR = computeLRCommitment n m aCommit sCommit t tBlinding mu x y z hs'
      productProof = IPP.generateProof
                        InnerProductBase { bGs = gs, bHs = hs', bH = u }
                        commitmentLR
                        InnerProductWitness { ls = ls, rs = rs }

  pure RangeProof
      { tBlinding = tBlinding
      , mu = mu
      , t = t
      , aCommit = aCommit
      , sCommit = sCommit
      , t1Commit = t1Commit
      , t2Commit = t2Commit
      , productProof = productProof
      }


-- | Compute l and r polynomials to prove knowledge of aL, aR without revealing them.
-- We achieve it by transferring the vectors l, r.
-- The two terms of the dot product above are set as the constant term,
-- while sL, sR are the coefficient of x^1 , in the following two linear polynomials,
-- which are combined into a quadratic in x:
-- l(x) = (a L − z1 n ) + s L x
-- r(x) = y^n ◦ (aR + z * 1^n + sR * x) + z^2 * 2^n
computeLRPolys
  :: (Eq f, Num f)
  => Integer
  -> Integer
  -> [f]
  -> [f]
  -> [f]
  -> [f]
  -> f
  -> f
  -> LRPolys f
computeLRPolys n m aL aR sL sR y z
  = LRPolys
        { l0 = aL ^-^ ((*) z <$> powerVector 1 nm)
        , l1 = sL
        , r0 = (powerVector y nm `hadamardp` (aR ^+^ z1nm))
               ^+^
                foldl' (\acc j -> iter j ^+^ acc) (replicate (fromIntegral nm) 0) [1..m]
        , r1 = hadamardp (powerVector y nm) sR
        }
  where
    z1nm = (*) z <$> powerVector 1 nm
    nm = n * m
    iter j = (*) (z ^ (j + 1)) <$> (powerVector 0 ((j - 1) * n) ++ powerVector 2 n ++ powerVector 0 ((m - j) * n))



-- | Compute polynomial t from polynomial r
-- t(x) = l(x) · r(x) = t0 + t1 * x + t2 * x^2
computeTPoly :: Num f => LRPolys f -> TPoly f
computeTPoly lrPoly@LRPolys{..}
  = TPoly
    { t0 = t0
    , t1 = (dot (l0 ^+^ l1) (r0 ^+^ r1) - t0) - t2
    , t2 = t2
    }
  where
    t0 = dot l0 r0
    t2 = dot l1 r1



