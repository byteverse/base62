{-# LANGUAGE MagicHash        #-}
{-# LANGUAGE TypeApplications #-}

import Test.Tasty (TestTree,defaultMain,testGroup)
import Test.Tasty.QuickCheck (testProperty,(===))

import qualified Data.Bytes as Bytes
import qualified Data.Word.Base62 as W

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "base62"
  [ testGroup "Word64"
    [ testProperty "encode_" $ \w ->
        Just w === W.decode64 (Bytes.fromByteArray (W.encode64_ w))
    ]
  ]

