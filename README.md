<p align="center">
<a href="https://www.adjoint.io">
  <img width="250" src="./.assets/adjoint.png" alt="Adjoint Logo" />
</a>
</p>

[![CircleCI](http://circleci.com/gh/adjoint-io/bulletproofs.svg?style=shield)](https://circleci.com/gh/adjoint-io/bulletproofs)
[![Hackage](https://img.shields.io/hackage/v/bulletproofs.svg)](http://hackage.haskell.org/package/bulletproofs)

Bulletproofs are short zero-knowledge arguments of knowledge that do not require a trusted setup.
Argument systems are proof systems with computational soundness.

Bulletproofs are suitable for proving statements on committed values, such as range proofs, verifiable suffles, arithmetic circuits, etc.
They rely on the discrete logarithmic assumption and are made non-interactive using
the Fiat-Shamir heuristic.

The core algorithm of Bulletproofs is the inner-product algorithm presented by Groth [2].
The algorithm provides an argument of knowledge of two binding vector Pedersen commitments that satisfy a given inner product relation.
Bulletproofs build on the techniques of Bootle et al. [3] to introduce a communication efficient inner-product proof that reduces
overall communication complexity of the argument to only 2log<sub>2</sub>(n) where n is the dimension
of the two vectors of commitments.


## Range proofs

Bulletproofs present a protocol for conducting short and aggregatable range proofs.
They encode a proof of the range of a committed number in an inner product, using polynomials.
Range proofs are proofs that a secret value lies in a certain interval.
Range proofs do not leak any information about the secret value, other
than the fact that they lie in the interval.

The proof algorithm can be sketched out in 5 steps:

Let _v_ be a value in _[0, n)_ and **a<sub>L</sub>** a vector of bit such that <**a<sub>L</sub>**, **2<sup>n</sup>**> = _v_.
The components of **a<sub>L</sub>** are the binary digits of _v_.
We construct a complementary vector **a<sub>R</sub>** = **a<sub>L</sub>** − **1**<sup>n</sup>
and require that **a<sub>L</sub>** ◦ **a<sub>R</sub>** = 0 holds.

- **P -> V : A, S** - where A and S are blinded Pedersen commitments to **a<sub>L</sub>** and **a<sub>R</sub>**.

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp; ![equation](https://latex.codecogs.com/gif.latex?\\&space;<img src="/tex/ca584568df041d6ebed0dd40b840f074.svg?invert_in_darkmode&sanitize=true" align=middle width=896.4067497pt height=45.84475500000001pt/>)

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp; ![equation](https://latex.codecogs.com/gif.latex?\\&space;<img src="/tex/de2dc9af18bc83a3e4d3278058817e38.svg?invert_in_darkmode&sanitize=true" align=middle width=889.56201015pt height=45.84475500000001pt/>)

- **V -> P : y, z** - Verifier sends challenges _y_ and _z_ to fix **A** and **S**.

- **P -> V : T<sub>1</sub>, T<sub>2</sub>** - where T<sub>1</sub> and T<sub>2</sub> are commitments to
the coefficients t<sub>1</sub>, of a polynomial t constructed from the existing values in the protocol.

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp; ![equation](https://latex.codecogs.com/gif.latex?\\&space;<img src="/tex/b78caf7d6bab1d3897fda12c5e75d8c7.svg?invert_in_darkmode&sanitize=true" align=middle width=897.8724050999999pt height=52.054622400000014pt/>)

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp; ![equation](https://latex.codecogs.com/gif.latex?\\&space;<img src="/tex/b239cf6a16f39997e6cd4ef870fc20a6.svg?invert_in_darkmode&sanitize=true" align=middle width=1373.80499025pt height=52.05461910000002pt/>)

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp; ![equation](https://latex.codecogs.com/gif.latex?\\&space;<img src="/tex/803924b311f2909f1bca21d35a066dcf.svg?invert_in_darkmode&sanitize=true" align=middle width=463.5880887pt height=24.65753399999998pt/>)

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp; ![equation](https://latex.codecogs.com/gif.latex?\\&space;<img src="/tex/db07025954c1a9260e8cb5c6f1ba6514.svg?invert_in_darkmode&sanitize=true" align=middle width=865.31701245pt height=47.67123240000001pt/>)

- **V -> P : x** - Verifier challenges Prover with value _x_.

- **P -> V : tau, mu, t, l, r** - Prover sends several commitments that the verifier will then check.

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp; ![equation](https://latex.codecogs.com/gif.latex?\\&space;<img src="/tex/cc313c8e792a2fb80c21f19d60148870.svg?invert_in_darkmode&sanitize=true" align=middle width=900.9872173499999pt height=48.85840080000001pt/>)

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp; ![equation](https://latex.codecogs.com/gif.latex?\\&space;<img src="/tex/57e119ae4949d2b984a2664620913cfe.svg?invert_in_darkmode&sanitize=true" align=middle width=596.9465469pt height=22.831056599999986pt/>)

See [Prover.hs](https://github.com/adjoint-io/bulletproofs/blob/master/Bulletproofs/RangeProof/Prover.hs "Prover.hs") for implementation details.

The interaction described is made non-interactive using the Fiat-Shamir Transform wherein all the random
challenges made by V are replaced with a hash of the transcript up until that point.

## Inner-product range proof

The size of the proof is further reduced by leveraging the compact O(log<sub>n</sub>) inner product proof.

The inner-product argument in the protocol allows to prove knowledge of vectors **l** and **r**, whose inner product is _t_ and
the commitment _P_ ∈  _G_ is a commitment of these two vectors. We can therefore replace sending
(tau, mu, t, **l**, **r**) with a transfer of (tau, mu, t) and an execution of an inner product argument.

Then, instead of sharing **l** and **r**, which has a communication cost of 2n elements, the inner-product
argument transmits only 2 [log<sub>2</sub>] + 2 elements. In total, the prover sends only 2 [log<sub>2</sub>(n)] + 4
group elements and 5 elements in _Z_<sub>p</sub>

## Aggregating Logarithmic Proofs

We can construct a single proof of range of multiple values, while only incurring an additional space cost of 2 log<sub>2</sub>(m) for
_m_ additional values _v_, as opposed to a multiplicative factor of _m_ when creating _m_ independent range proofs.

The aggregate range proof makes use of the inner product argument. It uses 2 [log<sub>2</sub> (n * m)] + 4 group elements and 5 elements in Z<sub>p</sub>.

See [Multi range proof example](https://github.com/adjoint-io/bulletproofs/tree/master#multi-range-proof)

## Usage

**Single range proof**

```haskell
import Data.Curve.Weierstrass.SECP256K1 (Fr)
import qualified Bulletproofs.RangeProof as RP
import Bulletproofs.Utils (commit)

testSingleRangeProof :: Integer -> (Fr, Fr) -> IO Bool
testSingleRangeProof upperBound (v, vBlinding) = do
  let vCommit = commit v vBlinding

  -- Prover
  proofE <- runExceptT (RP.generateProof upperBound (v, vBlinding))

  -- Verifier
  case proofE of
    Left err -> panic (show err)
    Right proof@RP.RangeProof{..}
      -> pure (RP.verifyProof upperBound vCommit proof)
```

**Multi range proof**

```haskell
import Data.Curve.Weierstrass.SECP256K1 (Fr)
import qualified Bulletproofs.MultiRangeProof as MRP
import Bulletproofs.Utils (commit)

testMultiRangeProof :: Integer -> [(Fr, Fr)] -> IO Bool
testMultiRangeProof upperBound vsAndvBlindings = do
  let vCommits = fmap (uncurry commit) vsAndvBlindings

  -- Prover
  proofE <- runExceptT (MRP.generateProof upperBound vsAndvBlindings)

  -- Verifier
  case proofE of
    Left err -> panic (show err)
    Right proof@RP.RangeProof{..}
      -> pure (MRP.verifyProof upperBound vCommits proof)
```


Note that the upper bound _u_ must be such that `u = 2 ^ n`, where _n_ is also a power of 2.
This implementation uses the elliptic curve secp256k1, a Koblitz curve, which
has 128 bit security.
See [Range proofs examples](./example/Example/RangeProof.hs) for further details.

## Zero-knowledge proofs for Arithmetic Circuits

An arithmetic circuit over a field and variables (a<sub>1</sub>, ..., a<sub>n</sub>) is a directed acyclic graph whose vertices are called gates.

Arithmetic circuit can be described alternatively as a list of multiplication gates with a collection of linear consistency equations
relating the inputs and outputs of the gates. Any circuit described as an acyclic graph can be efficiently converted into this alternative description.

Bulletproofs present a protocol to generate zero-knowledge argument for arithmetic circuits using the inner product argument,
which allows to get a proof of size 2 log<sub>2</sub>(n) + 13 elements and include committed values as inputs to the arithmetic circuit.

In the protocol, the Prover proves that the hadamard product of _a<sub>L</sub>_ and _a<sub>R</sub>_ and a set of linear constraints hold.
The input values _v_ used to generate the proof are then committed and shared with the Verifier.

```haskell
import Data.Curve.Weierstrass.SECP256K1 (Fr)
import Data.Field.Galois (rnd)
import Bulletproofs.ArithmeticCircuit
import Bulletproofs.Utils (hadamard, commit)

--  Example:
--  2 linear constraints (q = 2):
--  aL[0] + aL[1] + aL[2] + aL[3] = v[0]
--  aR[0] + aR[1] + aR[2] + aR[3] = v[1]
--
--  4 multiplication constraints (implicit) (n = 4):
--  aL[0] * aR[0] = aO[0]
--  aL[1] * aR[1] = aO[1]
--  aL[2] * aR[2] = aO[2]
--  aL[3] * aR[3] = aO[3]
--
--  2 input values (m = 2)

arithCircuitExample :: ArithCircuit Fr
arithCircuitExample = ArithCircuit
  { weights = GateWeights
    { wL = [[1, 1, 1, 1]
           ,[0, 0, 0, 0]]
    , wR = [[0, 0, 0, 0]
           ,[1, 1, 1, 1]]
    , wO = [[0, 0, 0, 0]
           ,[0, 0, 0, 0]]
    }
  , commitmentWeights = [[1, 0]
                        ,[0, 1]]
  , cs = [0, 0]
  }

testArithCircuitProof :: ([Fr], [Fr]) -> ArithCircuit Fr -> IO Bool
testArithCircuitProof (aL, aR) arithCircuit = do
  let m = 2

  -- Multiplication constraints
  let aO = aL `hadamard` aR

  -- Linear constraints
      v0 = sum aL
      v1 = sum aR

  commitBlinders <- replicateM m rnd
  let commitments = zipWith commit [v0, v1] commitBlinders

  let arithWitness = ArithWitness
        { assignment = Assignment aL aR aO
        , commitments = commitments
        , commitBlinders = commitBlinders
        }

  proof <- generateProof arithCircuit arithWitness

  pure (verifyProof commitments proof arithCircuit)
```
See [Aritmetic circuit example](./example/Example/ArithmeticCircuit.hs) for further details.

**References**:

1.  Bunz B., Bootle J., Boneh D., Poelstra A., Wuille P., Maxwell G.
    "Bulletproofs: Short Proofs for Confidential Transactions and More". Stanford, UCL, Blockstream, 2017

2. Groth J. "Linear Algebra with Sub-linear Zero-Knowledge Arguments". University College London, 2009

3. Bootle J., Cerully A., Chaidos P., Groth J, Petit C. "Efficient Zero-Knowledge Arguments for
Arithmetic Circuits in the Discrete Log Setting". University College London and University of Oxford, 2016.

**Notation**:

- ◦ : Hadamard product
- <> :Inner product
- **a**: Vector

## Disclaimer

This is experimental code meant for research-grade projects only. Please do not
use this code in production until it has matured significantly.

## License

```
Copyright 2018-2019 Adjoint Inc

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
```
