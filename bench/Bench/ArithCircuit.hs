module Bench.ArithCircuit where

import Protolude

import Criterion.Main
import Data.Curve.Weierstrass.SECP256K1 (PA, Fr)
import Bulletproofs.ArithmeticCircuit
import Bulletproofs.Utils (hadamard, commit)
-------------
-- Examples
-------------

-- Example 1
--
-- bL0     bR0    bL1      10
--  |       |      |       |
--  |--[+]--|      |--[+]--|
--      |              |
--      | bO0      bO1 |
--      |  =        =  |
--      |  aL      aR  |
--      |-----[x]------|
--             |
--             | aO
--             |
arithCircuitExample1 :: Fr -> Fr -> (ArithCircuit Fr, Assignment Fr, ArithWitness Fr PA)
arithCircuitExample1 x z =
  let wL = [[1], [0]]
      wR = [[0], [1]]
      wO = [[0], [0]]
      cs = [7 + 3, 2 + 10]
      aL = [10]
      aR = [12]
      aO = zipWith (*) aL aR
      gateWeights = GateWeights wL wR wO
      circuit = ArithCircuit gateWeights [] cs
      assignment = Assignment aL aR aO
      witness = ArithWitness assignment [] []
  in (circuit, assignment, witness)

-- Example 2
--
-- 5 linear constraint (q = 5):
-- aO[0] = aO[1]
-- aL[0] = V[0] - z
-- aL[1] = V[2] - z
-- aR[0] = V[1] - z
-- aR[1] = V[3] - z
--
-- 2 multiplication constraint (implicit) (n = 2):
-- aL[0] * aR[0] = aO[0]
-- aL[1] * aR[1] = aO[1]
--
-- 4 input values (m = 4)
arithCircuitExample2 :: Fr -> Fr -> (ArithCircuit Fr, Assignment Fr, ArithWitness Fr PA)
arithCircuitExample2 x z =
  let wL = [[0, 0]
           ,[1, 0]
           ,[0, 1]
           ,[0, 0]
           ,[0, 0]]
      wR = [[0, 0]
           ,[0, 0]
           ,[0, 0]
           ,[1, 0]
           ,[0, 1]]
      wO = [[1, -1]
           ,[0, 0]
           ,[0, 0]
           ,[0, 0]
           ,[0, 0]]
      wV = [[0, 0, 0, 0]
           ,[1, 0, 0, 0]
           ,[0, 0, 1, 0]
           ,[0, 1, 0 ,0]
           ,[0, 0, 0, 1]]
      cs = [0, -z, -z, -z, -z]
      aL = [4 - z, 9 - z]
      aR = [9 - z, 4 - z]
      aO = aL `hadamard` aR
      vs = [4, 9, 9, 4]
      blinders = [1, 2, 3, 4]
      commitments = zipWith commit vs blinders
      gateWeights = GateWeights wL wR wO
      circuit = ArithCircuit gateWeights wV cs
      assignment = Assignment aL aR aO
      witness = ArithWitness assignment commitments blinders
  in (circuit, assignment, witness)

exampleX :: Fr
exampleX = 11

exampleZ :: Fr
exampleZ = 12

runProtocolBench :: (ArithCircuit Fr, Assignment Fr, ArithWitness Fr PA) -> Benchmark
runProtocolBench (arithCircuit, assignment, arithWitness) = bgroup "Bulletproofs"
  [ bench "Prover" $ nfIO (generateProof arithCircuit arithWitness)
  , env (generateProof arithCircuit arithWitness) $ \proof ->
      bench "Verifier" $ nf (verifyProof (commitments arithWitness) proof) arithCircuit
  ]

benchmark :: [Benchmark]
benchmark =
  [ runProtocolBench $ arithCircuitExample2 exampleX exampleZ
  , runProtocolBench $ arithCircuitExample1 exampleX exampleZ
  ]
