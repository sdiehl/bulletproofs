{-# LANGUAGE ScopedTypeVariables #-}

module TestField where

import Protolude

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit

import qualified Crypto.PubKey.ECC.Prim as Crypto

import Bulletproofs.Utils
import Bulletproofs.Fq as Fq
import Bulletproofs.Curve

import TestCommon

prop_addMod :: Fq -> Fq -> Property
prop_addMod x y
  = (x + y) `mulP` g === (x `mulP` g) `addP` (y `mulP` g)

prop_subMod :: Fq -> Fq -> Property
prop_subMod x y
  = (x - y) `mulP` g === (x `mulP` g) `addP` Crypto.pointNegate curve (y `mulP` g)

-------------------------------------------------------------------------------
-- Laws of field operations
-------------------------------------------------------------------------------

testFieldLaws
  :: forall a . (Num a, Fractional a, Eq a, Arbitrary a, Show a)
  => Proxy a
  -> TestName
  -> TestTree
testFieldLaws _ descr
  = testGroup ("Test field laws of " <> descr)
    [ testProperty "commutativity of addition"
      $ commutes ((+) :: a -> a -> a)
    , testProperty "commutativity of multiplication"
      $ commutes ((*) :: a -> a -> a)
    , testProperty "associavity of addition"
      $ associates ((+) :: a -> a -> a)
    , testProperty "associavity of multiplication"
      $ associates ((*) :: a -> a -> a)
    , testProperty "additive identity"
      $ isIdentity ((+) :: a -> a -> a) 0
    , testProperty "multiplicative identity"
      $ isIdentity ((*) :: a -> a -> a) 1
    , testProperty "additive inverse"
      $ isInverse ((+) :: a -> a -> a) negate 0
    , testProperty "multiplicative inverse"
      $ \x -> (x /= (0 :: a)) ==> isInverse ((*) :: a -> a -> a) recip 1 x
    , testProperty "multiplication distributes over addition"
      $ distributes ((*) :: a -> a -> a) (+)
    ]

-------------------------------------------------------------------------------
-- Fq
-------------------------------------------------------------------------------

test_fieldLaws_Fq :: TestTree
test_fieldLaws_Fq = testFieldLaws (Proxy :: Proxy Fq) "Fq"
