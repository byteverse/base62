{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnboxedTuples #-}

{- | This module provides functions for encoding fixed-width words
using the base-62 encoding scheme. The encoding functions in this
module produce byte sequences that are ASCII-compatible text
encodings (e.g. ISO-8859-1 and UTF-8). Similarly, the decoding
functions only decode byte sequences that are an ASCII-compatible
text encoding of characters in the class @[A-Za-Z0-9]@. Other
encodings (notably UTF-16) are not supported but would be
accepted in a pull request.
-}
module Data.Word.Base62
  ( -- * 64-bit Word
    encode64
  , builder64
  , decode64

    -- * 128-bit Word
  , encode128
  , shortText128
  , text128
  , builder128
  , decode128
  ) where

import Data.ByteString.Short.Internal (ShortByteString (SBS))
import Data.Bytes.Builder.Bounded.Unsafe (Builder (..))
import Data.Bytes.Types (Bytes (Bytes))
import Data.Char (ord)
import Data.Primitive (ByteArray (..), MutableByteArray (MutableByteArray), readByteArray, writeByteArray)
import Data.Text (Text)
import Data.Text.Short (ShortText)
import Data.WideWord.Word128 (Word128 (Word128))
import GHC.Exts (ByteArray#, Char (C#), Int (I#), Int#, Word64#, Word8#, indexCharArray#, isTrue#, quotRemWord#, word64ToWord#, wordToWord64#, (+#), (-#), (>#))
import GHC.ST (ST (ST))
import GHC.Word (Word64 (W64#), Word8 (W8#))

import qualified Arithmetic.Nat as Nat
import qualified Data.Bytes as Bytes
import qualified Data.Bytes.Builder.Bounded as Builder
import qualified Data.Text.Short as TS
import qualified Data.Text.Short.Unsafe as TS
import qualified GHC.Exts as Exts

{- | Base62 encode a 64-bit word. Leading zero bits are suppressed.
Note that this will encode the number 0 as the character '0' rather
than as the empty byte array.
-}
encode64 :: Word64 -> ByteArray
encode64 = Builder.run Nat.constant . builder64

-- | Base62 encode a 64-bit word as a builder.
builder64 :: Word64 -> Builder 11
{-# INLINE builder64 #-}
builder64 (W64# w) = builder64# w

-- | Base62 encode a 128-bit word. Leading zero bits are suppressed.
encode128 :: Word128 -> ByteArray
{-# INLINE encode128 #-}
encode128 = Builder.run Nat.constant . builder128

-- | Base62 encode a 128-bit word as @ShortText@.
shortText128 :: Word128 -> ShortText
{-# INLINE shortText128 #-}
shortText128 !w = case encode128 w of
  ByteArray x -> TS.fromShortByteStringUnsafe (SBS x)

-- | Base62 encode a 128-bit word as @Text@.
text128 :: Word128 -> Text
{-# INLINE text128 #-}
text128 = TS.toText . shortText128

-- | Base62 encode a 128-bit word as a builder.
builder128 :: Word128 -> Builder 22
{-# INLINE builder128 #-}
builder128 (Word128 (W64# a) (W64# b)) = builder128# a b

builder64# :: Word64# -> Builder 11
{-# NOINLINE builder64# #-}
builder64# w0 =
  Builder
    ( \marr off0 s0 -> case word64ToWord# w0 of
        0## -> case Exts.writeWord8Array# marr off0 (Exts.wordToWord8# 48##) s0 of
          s1 -> (# s1, off0 +# 1# #)
        _ ->
          let go ix w s1 = case word64ToWord# w of
                0## -> case reverseBytes (MutableByteArray marr) (I# off0) (I# (ix -# 1#)) of
                  ST f -> case f s1 of
                    (# s2, (_ :: ()) #) -> (# s2, ix #)
                _ ->
                  let !(# q0, r0 #) = quotRemWord# (word64ToWord# w) 62##
                      !q = wordToWord64# q0
                      !r = wordToWord64# r0
                   in case Exts.writeWord8Array# marr ix (unW8 (encodeByte (W64# r))) s1 of
                        s2 -> go (ix +# 1#) q s2
           in go off0 w0 s0
    )

-- Always outputs exactly ten digits. They do not need to be reversed.
builder62pow10# :: Word64# -> Builder 10
{-# NOINLINE builder62pow10# #-}
builder62pow10# w0 =
  Builder
    ( \marr off0 s0 ->
        let go ix d w s1 = case d of
              0# -> (# s1, ix +# 11# #)
              _ ->
                let !(# q0, r0 #) = quotRemWord# (word64ToWord# w) 62##
                    !q = wordToWord64# q0
                    !r = wordToWord64# r0
                 in case Exts.writeWord8Array# marr ix (unW8 (encodeByte (W64# r))) s1 of
                      s2 -> go (ix -# 1#) (d -# 1#) q s2
         in go (off0 +# 9#) 10# w0 s0
    )

builder128# :: Word64# -> Word64# -> Builder 22
{-# NOINLINE builder128# #-}
builder128# wa wb =
  Builder
    ( \marr off0 s0 -> case word64ToWord# wa of
        0## -> case builder64# wb of Builder f -> f marr off0 s0
        _ -> case quotRem (Word128 (W64# wa) (W64# wb)) (Word128 0 n62pow10) of
          (upper@(Word128 upperHi (W64# upperLo)), (Word128 shouldBeZeroA (W64# lower))) -> case shouldBeZeroA of
            0 -> case upperHi of
              0 -> case builder64# upperLo `Builder.append` builder62pow10# lower of Builder f -> f marr off0 s0
              _ -> case quotRem upper (Word128 0 n62pow10) of
                (Word128 shouldBeZeroB (W64# x), Word128 shouldBeZeroC (W64# y)) -> case shouldBeZeroB of
                  0 -> case shouldBeZeroC of
                    0 -> case builder64# x `Builder.append` (builder62pow10# y `Builder.append` builder62pow10# lower) of Builder f -> f marr off0 s0
                    _ -> errorWithoutStackTrace "Data.Word.Base62: logical error c"
                  _ -> errorWithoutStackTrace "Data.Word.Base62: logical error b"
            _ -> errorWithoutStackTrace "Data.Word.Base62: logical error a"
    )

-- Reverse the bytes in the designated slice. This takes
-- an inclusive start offset and an inclusive end offset.
reverseBytes :: MutableByteArray s -> Int -> Int -> ST s ()
{-# INLINE reverseBytes #-}
reverseBytes arr begin end = go begin end
 where
  go ixA ixB =
    if ixA < ixB
      then do
        a :: Word8 <- readByteArray arr ixA
        b :: Word8 <- readByteArray arr ixB
        writeByteArray arr ixA b
        writeByteArray arr ixB a
        go (ixA + 1) (ixB - 1)
      else pure ()

-- Precondition: argument is less than 62.
encodeByte :: Word64 -> Word8
encodeByte w
  | w < 10 = unsafeW8 (c2w '0' + w)
  | w < 36 = unsafeW8 ((c2w 'A' - 10) + w)
  | otherwise = unsafeW8 ((c2w 'a' - 36) + w)

-- We use Char here since it produces more readable Core.
-- Performance is not impacted in any way.
decodeByte :: Char -> Maybe Word64
decodeByte w
  | w >= '0' && w <= '9' = Just (c2w w - c2w '0')
  | w >= 'A' && w <= 'Z' = Just (c2w w - (c2w 'A' - 10))
  | w >= 'a' && w <= 'z' = Just (c2w w - (c2w 'a' - 36))
  | otherwise = Nothing

c2w :: Char -> Word64
c2w = fromIntegral . ord

-- Precondition: the argument is less than 256
unsafeW8 :: Word64 -> Word8
unsafeW8 (W64# w) = W8# (Exts.wordToWord8# (word64ToWord# w))

unW8 :: Word8 -> Word8#
unW8 (W8# w) = w

{- | Decode a base62-encoded 64-bit word. This rejects the empty
string rather than decoding it as zero. This also rejects encoded
numbers greater than or equal to @2^64@.
-}
decode64 :: Bytes -> Maybe Word64
{-# INLINE decode64 #-}
decode64 b@(Bytes _ _ len) = case len of
  0 -> Nothing
  _ -> case decode64# 0 b of
    (# (# #) | #) -> Nothing
    (# | w #) -> Just (W64# w)

-- Worker-wrapper will turn this into good code as long as
-- we do not put a noinline pragma on it. It is recursive,
-- so it cannot inline anywhere.
decode64# :: Word64 -> Bytes -> (# (# #) | Word64# #)
decode64# !acc@(W64# acc#) b@(Bytes arr off len) = case len of
  0 -> (# | acc# #)
  _ -> case decodeByte (indexAsciiArray arr off) of
    Nothing -> (# (# #) | #)
    Just w ->
      -- If we overflow, the accumulator will shrink. We
      -- return Nothing in this case.
      let (overflow, acc') = unsignedPushBase62 acc w
       in if overflow
            then (# (# #) | #)
            else decode64# acc' (Bytes.unsafeDrop 1 b)

n62pow10 :: Word64
n62pow10 = 62 * 62 * 62 * 62 * 62 * 62 * 62 * 62 * 62 * 62

n62pow20 :: Word128
n62pow20 = Word128 0 n62pow10 * Word128 0 n62pow10

-- Precondition: there are at least 10 bytes starting at the offset.
-- The result is in [0,62^10) Notice that we do not need to check
-- for overflow in this function. While @off@ tracks the actual
-- position in the bytearray, @d@ tracks the number of digits
-- consumed by this particular function. The caller should always
-- set @d@ to 0.
unsafeDecode62pow10# :: Word64 -> ByteArray -> Int -> Int -> (# (# #) | Word64# #)
unsafeDecode62pow10# !acc@(W64# acc#) !arr !off !d =
  if d < 10
    then case decodeByte (indexAsciiArray arr off) of
      Nothing -> (# (# #) | #)
      Just w ->
        let acc' = acc * 62 + w
         in unsafeDecode62pow10# acc' arr (off + 1) (d + 1)
    else (# | acc# #)

{- | Decode a base62-encoded 128-bit word. This rejects the empty
string rather than decoding it as zero. This also rejects encoded
numbers greater than or equal to @2^128@.
-}
decode128 :: Bytes -> Maybe Word128
{-# INLINE decode128 #-}
decode128 (Bytes (ByteArray arr) (I# off) (I# len)) =
  case decode128# arr off len of
    (# (# #) | #) -> Nothing
    (# | (# a, b #) #) -> Just (Word128 (W64# a) (W64# b))

decode128# :: ByteArray# -> Int# -> Int# -> (# (# #) | (# Word64#, Word64# #) #)
{-# NOINLINE decode128# #-}
decode128# arr off len
  | isTrue# (len ># 22#) = (# (# #) | #) -- always overflows
  | isTrue# (len ># 20#) =
      case unsafeDecode62pow10# 0 (ByteArray arr) (I# (off +# len -# 10#)) 0 of
        (# (# #) | #) -> (# (# #) | #)
        (# | c #) -> case unsafeDecode62pow10# 0 (ByteArray arr) (I# (off +# len -# 20#)) 0 of
          (# (# #) | #) -> (# (# #) | #)
          (# | b #) -> case decode64# 0 (Bytes (ByteArray arr) (I# off) (I# (len -# 20#))) of
            (# (# #) | #) -> (# (# #) | #)
            (# | a #) ->
              if W64# a < 484
                then
                  let r0 = Word128 0 (W64# c) + (Word128 0 n62pow10 * (Word128 0 (W64# b)))
                      !r1@(Word128 (W64# r1x) (W64# r1y)) = n62pow20 * Word128 0 (W64# a) + r0
                   in if r1 >= r0
                        then (# | (# r1x, r1y #) #)
                        else (# (# #) | #)
                else (# (# #) | #)
  | isTrue# (len ># 10#) =
      case unsafeDecode62pow10# 0 (ByteArray arr) (I# (off +# len -# 10#)) 0 of
        (# (# #) | #) -> (# (# #) | #)
        (# | b #) -> case decode64# 0 (Bytes (ByteArray arr) (I# off) (I# (len -# 10#))) of
          (# (# #) | #) -> (# (# #) | #)
          (# | a #) -> case Word128 0 (W64# b) + (fromIntegral n62pow10 * Word128 0 (W64# a)) of
            Word128 (W64# x) (W64# y) -> (# | (# x, y #) #)
  | otherwise = case decode64# 0 (Bytes (ByteArray arr) (I# off) (I# len)) of
      (# (# #) | #) -> (# (# #) | #)
      (# | w #) -> (# | (# wordToWord64# 0##, w #) #)

indexAsciiArray :: ByteArray -> Int -> Char
indexAsciiArray (ByteArray arr) (I# i) = C# (indexCharArray# arr i)

unsignedPushBase62 :: Word64 -> Word64 -> (Bool, Word64)
{-# INLINE unsignedPushBase62 #-}
unsignedPushBase62 (W64# a) (W64# b) =
  let !(# ca, r0 #) = Exts.timesWord2# (word64ToWord# a) 62##
   in case ca of
        0## ->
          let !r0' = wordToWord64# r0
              !r1 = Exts.plusWord64# r0' b
           in case Exts.ltWord64# r1 r0' of
                1# -> (True, 0)
                _ -> (False, W64# r1)
        _ -> (True, 0)
