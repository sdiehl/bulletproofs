# Changelog for bulletproofs

## 1.1

* Use elliptic-curve library as dependency
* Update to galois-field-1.0

## 1.0.1

* Fix arithmoi dependency.
* Fix galois-field dependency.

## 1.0

* Use galois-field library as dependency
* Remove custom definition of Fq
* Remove Fractional constraints and use PrimeField instead
* Update interface of rangeproofs to guarantee the use of prime fields

## 0.4

* Use double exponentiation to improve performance.
* Use Control.Exception.assert to make sure debugging assertions are not checked
  when compiled with optimisations.
* Add benchmarks for rangeproofs.

## 0.3

* Update dependencies

## 0.2

* Prove and verify computations of arithmetic circuits using Bulletproofs
  protocol.
* Extend range proofs with support for multi-range proofs.
* Add documentation and provide examples to explain and use arithmetic circuits.
* Provide examples for using aggregated range proofs.
* Add multi-range proofs documentation.

## 0.1

* Initial release.
* Implementation of the Bulletproofs protocol for range proofs
* Use of the improved inner-product argument to reduce the communication complexity
* Support for SECp256k1 curve

