{-# language BangPatterns #-}
{-# language DataKinds #-}
{-# language GADTSyntax #-}
{-# language LambdaCase #-}
{-# language MagicHash #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}
{-# language TypeApplications #-}
{-# language UnboxedTuples #-}

module Data.Word.Base62
  ( encode64_
  , builder64_
  , decode64
  ) where

import Data.ByteArray.Builder.Small.Unsafe (Builder(..),run)
import Data.Bytes.Types (Bytes(Bytes))
import Data.Char (ord)
import Data.Primitive (ByteArray(..),readByteArray,writeByteArray)
import Data.Primitive (MutableByteArray(MutableByteArray))
import GHC.Exts (Char(C#),quotRemWord#,indexCharArray#)
import GHC.Exts (Int(I#),Word#,(+#),(-#),writeWord8Array#)
import GHC.ST (ST(ST))
import GHC.Word (Word64(W64#),Word8(W8#),Word(W#))

import qualified Data.Bytes as Bytes

-- | Base62 encode a 64-bit word. Leading zero bits are suppressed.
-- For example:
--
-- >>> encode64_ 213635
-- tZj
--
-- Note that this will encode the number 0 as the character 0 rather
-- than as the empty byte array.
encode64_ :: Word64 -> ByteArray
encode64_ = run . builder64_

builder64_ :: Word64 -> Builder 11
{-# inline builder64_ #-}
builder64_ (W64# w) = builder64_# w

builder64_# :: Word# -> Builder 11
{-# noinline builder64_# #-}
builder64_# w0 = Builder
  (\marr off0 s0 -> case w0 of
    0## -> case writeWord8Array# marr off0 48## s0 of
      s1 -> (# s1, off0 +# 1# #)
    _ -> let go ix w s1 = case w of
               0## -> case reverseBytes (MutableByteArray marr) (I# off0) (I# (ix -# 1# )) of
                 ST f -> case f s1 of
                   (# s2, (_ :: ()) #) -> (# s2, ix #)
               _ ->
                 let !(# q, r #) = quotRemWord# w 62##
                  in case writeWord8Array# marr ix (unW8 (encodeByte (W# r))) s1 of
                       s2 -> go (ix +# 1#) q s2
          in go off0 w0 s0
  )

-- Reverse the bytes in the designated slice. This takes
-- an inclusive start offset and an inclusive end offset.
reverseBytes :: MutableByteArray s -> Int -> Int -> ST s ()
{-# inline reverseBytes #-}
reverseBytes arr begin end = go begin end where
  go ixA ixB = if ixA < ixB
    then do
      a :: Word8 <- readByteArray arr ixA
      b :: Word8 <- readByteArray arr ixB
      writeByteArray arr ixA b
      writeByteArray arr ixB a
      go (ixA + 1) (ixB - 1)
    else pure ()

-- Precondition: argument is less than 62.
encodeByte :: Word -> Word8
encodeByte w
  | w < 10 = unsafeW8 (c2w '0' + w)
  | w < 36 = unsafeW8 ((c2w 'A' - 10) + w)
  | otherwise = unsafeW8 ((c2w 'a' - 36) + w)

-- We use Char here since it produces more readable Core.
-- Performance is not impacted in any way.
decodeByte :: Char -> Maybe Word
decodeByte w
  | w >= '0' && w <= '9' = Just (c2w w - c2w '0')
  | w >= 'A' && w <= 'Z' = Just (c2w w - (c2w 'A' - 10))
  | w >= 'a' && w <= 'z' = Just (c2w w - (c2w 'a' - 36))
  | otherwise = Nothing

c2w :: Char -> Word
c2w = fromIntegral . ord

-- Precondition: the argument is less than 256
unsafeW8 :: Word -> Word8
unsafeW8 (W# w) = W8# w

unW8 :: Word8 -> Word#
unW8 (W8# w) = w

unW :: Word -> Word#
unW (W# w) = w

-- | Decode a base62-encoded 64-bit number. This rejects the empty
-- string rather than decoding it as zero.
decode64 :: Bytes -> Maybe Word64
{-# inline decode64 #-}
decode64 b@(Bytes arr off len) = case len of
  0 -> Nothing
  _ -> case decode64# 0 b of
    (# (# #) | #) -> Nothing
    (# | w #) -> Just (W64# w)

-- Worker-wrapper will turn this into good code as long as
-- we do not put a noinline pragma on it.
decode64# :: Word -> Bytes -> (# (# #) | Word# #)
decode64# !acc b@(Bytes arr off len) = case len of
  0 -> (# | unW acc #)
  _ -> case decodeByte (indexAsciiArray arr off) of
    Nothing -> (# (# #) | #)
    Just w -> decode64# (acc * 62 + w) (Bytes.unsafeDrop 1 b)

indexAsciiArray :: ByteArray -> Int -> Char
indexAsciiArray (ByteArray arr) (I# i) = C# (indexCharArray# arr i)
