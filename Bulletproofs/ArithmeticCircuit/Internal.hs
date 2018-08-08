{-# LANGUAGE ViewPatterns, RecordWildCards #-}

module Bulletproofs.ArithmeticCircuit.Internal where

import Protolude hiding (head)
import Data.List (head)
import qualified Data.List as List
import qualified Data.Map as Map

import System.Random.Shuffle (shuffleM)
import qualified Crypto.Random.Types as Crypto (MonadRandom(..))
import Crypto.Number.Generate (generateMax, generateBetween)
import Control.Monad.Random (MonadRandom)
import qualified Crypto.PubKey.ECC.Types as Crypto
import qualified Crypto.PubKey.ECC.Prim as Crypto

import Bulletproofs.Fq as Fq
import Bulletproofs.Curve
import Bulletproofs.Utils
import Bulletproofs.RangeProof.Internal
import qualified Bulletproofs.InnerProductProof as IPP

data ArithCircuitProof
  = ArithCircuitProof
    { tBlinding :: Fq
    , mu :: Fq
    , t :: Fq
    , aiCommit :: Crypto.Point
    , aoCommit :: Crypto.Point
    , sCommit :: Crypto.Point
    , tCommits :: [Crypto.Point]
    , productProof :: IPP.InnerProductProof
    } deriving (Show, Eq)

data ArithCircuit f
  = ArithCircuit
    { weights :: GateWeights f
    , commitmentWeights :: [[f]]
    , cs :: [f]
    } deriving (Show, Eq)


data GateWeights f
  = GateWeights
    { wL :: [[f]] -- WL in Z(Q x n)
    , wR :: [[f]] -- WR in Z(Q x n)
    , wO :: [[f]] -- WO in Z(Q x n)
    } deriving (Show, Eq)

data ArithWitness f
  = ArithWitness
  { inputs :: Assignment f
  , commitments :: [Crypto.Point]
  , commitBlinders :: [Fq]
  } deriving (Show, Eq)

data Assignment f
  = Assignment
    { aL :: [f] -- aL. Vector of left inputs of each multiplication gate
    , aR :: [f] -- aR. Vector of right inputs of each multiplication gate
    , aO :: [f] -- aO. Vector of outputs of each multiplication gate
    } deriving (Show, Eq)


delta :: Integer -> Fq -> [Fq] -> [Fq] -> Fq
delta n y zwL zwR= (powerVector (inv y) n `hadamardp` zwR) `dotp` zwL

commitBitVector :: Fq -> [Fq] -> [Fq] -> Crypto.Point
commitBitVector vBlinding vL vR = vLG `addP` vRH `addP` vBlindingH
  where
    vBlindingH = vBlinding `mulP` h
    vLG = foldl' addP Crypto.PointO ( zipWith mulP vL gs )
    vRH = foldl' addP Crypto.PointO ( zipWith mulP vR hs )

shamirGxGxG :: Crypto.Point -> Crypto.Point -> Crypto.Point -> Fq
shamirGxGxG p1 p2 p3
  = Fq.new $ oracle $ show q <> pointToBS p1 <> pointToBS p2 <> pointToBS p3

shamirGs :: [Crypto.Point] -> Fq
shamirGs ps = Fq.new $ oracle $ show q <> foldMap pointToBS ps

shamirZ :: Fq -> Fq
shamirZ z = Fq.new $ oracle $ show q <> show z

---------------------------------------------
-- Linear algebra
---------------------------------------------

vectorMatrixProduct :: [Fq] -> [[Fq]] -> [Fq]
vectorMatrixProduct v m
  = sum . zipWith (*) v <$> transpose m

vectorMatrixProductT :: [Fq] -> [[Fq]] -> [Fq]
vectorMatrixProductT v m
  = sum . zipWith (*) v <$> m

matrixVectorProduct :: [[Fq]] -> [Fq] -> [Fq]
matrixVectorProduct m v
  = head $ matrixProduct m [v]

powerMatrix :: [[Fq]] -> Integer -> [[Fq]]
powerMatrix m 0 = m
powerMatrix m n = matrixProduct m (powerMatrix m (n-1))

matrixProduct :: Num a => [[a]] -> [[a]] -> [[a]]
matrixProduct a b = (\ar -> sum . zipWith (*) ar <$> transpose b) <$> a

evaluatePolynomial :: Integer -> [[Fq]] -> Fq -> [Fq]
evaluatePolynomial (fromIntegral -> n) poly x
  = foldl'
    (\acc (idx, e) -> acc `fqAddV` ((*) (fqPower x idx) <$> e))
    (replicate n (Fq.new 0))
    (zip [0..] poly)

multiplyPoly :: Num n => [[n]] -> [[n]] -> [n]
multiplyPoly l r
  = snd <$> Map.toList (foldl' (\accL (i, li)
      -> foldl'
          (\accR (j, rj) -> case Map.lookup (i + j) accR of
              Just x -> Map.insert (i + j) (x + (li `dotp` rj)) accR
              Nothing -> Map.insert (i + j) (li `dotp` rj) accR
          ) accL (zip [0..] r))
      (Map.empty :: Num n => Map.Map Int n)
      (zip [0..] l))

insertAt :: Int -> a -> [a] -> [a]
insertAt z y xs = as ++ (y : bs)
  where
    (as, bs) = splitAt z xs

genIdenMatrix :: Integer -> [[Fq]]
genIdenMatrix size = (\x -> (\y -> fromIntegral (fromEnum (x == y))) <$> [1..size]) <$> [1..size]

genZeroMatrix :: Integer -> Integer -> [[Fq]]
genZeroMatrix (fromIntegral -> n) (fromIntegral -> m) = replicate n (replicate m 0)

generateWv :: MonadRandom m => Integer -> Integer -> m [[Fq]]
generateWv lConstraints m
  | lConstraints < m = panic "Number of constraints must be bigger than m"
  | otherwise = shuffleM (genIdenMatrix m ++ genZeroMatrix (lConstraints - m) m)

generateGateWeights :: Crypto.MonadRandom m => Integer -> Integer -> m (GateWeights Fq)
generateGateWeights lConstraints n = do
  [wL, wR, wO] <- replicateM 3 ((\i -> insertAt (fromIntegral i) (oneVector n) (replicate (fromIntegral lConstraints - 1) (zeroVector n))) <$> generateMax (fromIntegral lConstraints))
  pure $ GateWeights wL wR wO
  where
    zeroVector x = replicate (fromIntegral x) 0
    oneVector x = replicate (fromIntegral x) 1

generateRandomAssignment :: Crypto.MonadRandom m => Integer -> m (Assignment Fq)
generateRandomAssignment n = do
  aL <- replicateM (fromIntegral n) (Fq.random n)
  aR <- replicateM (fromIntegral n) (Fq.random n)
  let aO = aL `hadamardp` aR
  pure $ Assignment aL aR aO

computeInputValues :: GateWeights Fq -> [[Fq]] -> Assignment Fq -> [Fq] -> [Fq]
computeInputValues GateWeights{..} wV Assignment{..} cs
  = solveLinearSystem $ zipWith (\row s -> reverse $ s : row) wV solutions
  where
    solutions = vectorMatrixProductT aL wL
        `fqAddV` vectorMatrixProductT aR wR
        `fqAddV` vectorMatrixProductT aO wO
        `fqSubV` cs

gaussianReduce :: [[Fq]] -> [[Fq]]
gaussianReduce matrix = fixlastrow $ foldl reduceRow matrix [0..length matrix-1]
  where
    -- Swaps element at position a with element at position b.
    swap xs a b
     | a > b = swap xs b a
     | a == b = xs
     | a < b = let (p1, p2) = splitAt a xs
                   (p3, p4) = splitAt (b - a - 1) (List.tail p2)
               in p1 ++ [xs List.!! b] ++ p3 ++ [xs List.!! a] ++ List.tail p4

    -- Concat the lists and repeat
    reduceRow matrix1 r = take r matrix2 ++ [row1] ++ nextrows
      where
        --First non-zero element on or below (r,r).
        firstnonzero = head $ filter (\x -> matrix1 List.!! x List.!! r /= 0) [r..length matrix1-1]
        --Matrix with row swapped (if needed)
        matrix2 = swap matrix1 r firstnonzero
        --Row we're working with
        row = matrix2 List.!! r
        --Make it have 1 as the leading coefficient
        row1 = (\x -> x *  inv (row List.!! r)) <$> row
        --Subtract nr from row1 while multiplying
        subrow nr = let k = nr List.!! r in zipWith (\a b -> k*a - b) row1 nr
        --Apply subrow to all rows below
        nextrows = subrow <$> drop (r + 1) matrix2


    fixlastrow matrix' = a ++ [List.init (List.init row) ++ [1, z * inv nz]]
      where
        a = List.init matrix'; row = List.last matrix'
        z = List.last row
        nz = List.last (List.init row)

-- Solve a matrix (must already be in REF form) by back substitution.
substituteMatrix :: [[Fq]] -> [Fq]
substituteMatrix matrix = foldr next [List.last (List.last matrix)] (List.init matrix)
  where
    next row found = let
      subpart = List.init $ drop (length matrix - length found) row
      solution = List.last row - sum (zipWith (*) found subpart)
      in solution : found

solveLinearSystem :: [[Fq]] -> [Fq]
solveLinearSystem = reverse . substituteMatrix . gaussianReduce
