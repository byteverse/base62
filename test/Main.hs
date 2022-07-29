{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

import Control.Applicative (liftA2)
import Data.Primitive (ByteArray)
import Data.Bits ((.&.))
import Data.Char (chr)
import Test.Tasty (TestTree,defaultMain,testGroup)
import Test.Tasty.HUnit (testCase,(@=?))
import Test.Tasty.QuickCheck (testProperty,(===),choose)
import Test.Tasty.QuickCheck (Arbitrary,arbitrary,counterexample)
import Data.WideWord.Word128 (Word128(Word128))

import qualified Test.Tasty.QuickCheck
import qualified Data.Bytes as Bytes
import qualified Data.Bytes.Text.Ascii as Ascii
import qualified Data.Word.Base62 as W
import qualified GHC.Exts as Exts

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "base62"
  [ testGroup "Word64"
    [ testProperty "isomorphic" $ \w ->
        Just w === W.decode64 (Bytes.fromByteArray (W.encode64 w))
    , testCase "A" $
        Nothing
        @=?
        W.decode64 (Ascii.fromString "1IdHllabYuAOlNK4")
    ]
  , testGroup "Word128"
    [ testProperty "isomorphic" $ \w ->
        let enc = W.encode128 w in
        counterexample ("Encoded as: " ++ show enc ++ "\nRendered as: " ++ str enc)
          $ Just w === W.decode128 (Bytes.fromByteArray enc)
    , testCase "A" $
        Nothing
        @=?
        W.decode128 (Ascii.fromString "7n42DGM5Tflk9n8mt7Fhc9")
    ]
  ]

instance Arbitrary Word128 where
  -- It is useful to explicitly generate some small values
  -- since they follow a different code path than large ones.
  arbitrary = choose (0,2 :: Int) >>= \case
    0 -> fmap (Word128 0) arbitrary
    1 -> liftA2 Word128
      (fmap (0xFFFF .&.) arbitrary)
      arbitrary
    2 -> liftA2 Word128 arbitrary arbitrary
    _ -> error "Word128.arbitrary: not possible"
  shrink x = if x > 5
    then [x - div x 9, x - div x 11, x - div x 13]
    else []

str :: ByteArray -> String
str = map (chr . fromIntegral) . Exts.toList
