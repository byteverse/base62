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
  ( -- * 64-bit Word
    encode64_
  , builder64_
  , decode64
    -- * 128-bit Word
  , encode128_
  , builder128_
  , decode128
  ) where

import Data.ByteArray.Builder.Bounded.Unsafe (Builder(..))
import Data.Bytes.Types (Bytes(Bytes))
import Data.Char (ord)
import Data.Primitive (ByteArray(..),readByteArray,writeByteArray)
import Data.Primitive (MutableByteArray(MutableByteArray))
import Data.WideWord.Word128 (Word128(Word128))
import GHC.Exts (Char(C#),quotRemWord#,indexCharArray#)
import GHC.Exts (ByteArray#,Int#,Int(I#),Word#,(+#),(-#),writeWord8Array#)
import GHC.Exts (isTrue#,(>#))
import GHC.ST (ST(ST))
import GHC.Word (Word64(W64#),Word8(W8#),Word(W#))

import qualified Arithmetic.Nat as Nat
import qualified Data.Bytes as Bytes
import qualified Data.ByteArray.Builder.Bounded as Builder

-- | Base62 encode a 64-bit word. Leading zero bits are suppressed.
-- For example:
--
-- >>> encode64_ 213635
-- tZj
--
-- Note that this will encode the number 0 as the character 0 rather
-- than as the empty byte array.
encode64_ :: Word64 -> ByteArray
encode64_ = Builder.run Nat.constant . builder64_

builder64_ :: Word64 -> Builder 11
{-# inline builder64_ #-}
builder64_ (W64# w) = builder64_# w

encode128_ :: Word128 -> ByteArray
encode128_ = Builder.run Nat.constant . builder128_

builder128_ :: Word128 -> Builder 22
{-# inline builder128_ #-}
builder128_ (Word128 (W64# a) (W64# b)) = builder128_# a b

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

-- Always outputs exactly ten digits. They do not need to be reversed.
builder62pow10# :: Word# -> Builder 10
{-# noinline builder62pow10# #-}
builder62pow10# w0 = Builder
  (\marr off0 s0 -> 
    let go ix d w s1 = case d of
          0# -> (# s1, ix +# 11# #) 
          _ ->
            let !(# q, r #) = quotRemWord# w 62##
             in case writeWord8Array# marr ix (unW8 (encodeByte (W# r))) s1 of
                  s2 -> go (ix -# 1# ) (d -# 1# ) q s2
     in go (off0 +# 9# ) 10# w0 s0
  )

builder128_# :: Word# -> Word# -> Builder 22
{-# noinline builder128_# #-}
builder128_# wa wb = Builder
  (\marr off0 s0 -> case wa of
    0## -> case builder64_# wb of Builder f -> f marr off0 s0
    _ -> case quotRem (Word128 (W64# wa) (W64# wb)) (Word128 0 n62pow10) of
      (upper@(Word128 upperHi (W64# upperLo)), (Word128 shouldBeZeroA (W64# lower))) -> case shouldBeZeroA of
        0 -> case upperHi of
          0 -> case builder64_# upperLo `Builder.append` builder62pow10# lower of Builder f -> f marr off0 s0
          _ -> case quotRem upper (Word128 0 n62pow10) of
            (Word128 shouldBeZeroB (W64# x),Word128 shouldBeZeroC (W64# y)) -> case shouldBeZeroB of
              0 -> case shouldBeZeroC of
                0 -> case builder64_# x `Builder.append` (builder62pow10# y `Builder.append` builder62pow10# lower) of Builder f -> f marr off0 s0
                _ -> error "Data.Word.Base62: logical error c"
              _ -> error "Data.Word.Base62: logical error b"
        _ -> error "Data.Word.Base62: logical error a"
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
decode64 b@(Bytes _ _ len) = case len of
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
    Just w ->
      -- If we overflow, the accumulator will shrink. We
      -- return Nothing in this case.
      let acc' = acc * 62 + w
       in if acc' >= acc
            then decode64# acc' (Bytes.unsafeDrop 1 b)
            else (# (# #) | #)

n62pow10 :: Word64
n62pow10 = 62 * 62 * 62 * 62 * 62 * 62 * 62 * 62 * 62 * 62

-- n62pow20 :: Word28
-- n62pow20 = Word128 0 n62pow10 * Word128 0 n62pow10

-- Precondition: there are at least 10 bytes starting at the offset.
-- The result is in [0,62^10) Notice that we do not need to check
-- for overflow in this function. While @off@ tracks the actual
-- position in the bytearray, @d@ tracks the number of digits
-- consumed by this particular function. The caller should always
-- set @d@ to 0.
unsafeDecode62pow10# :: Word -> ByteArray -> Int -> Int -> (# (# #) | Word# #)
unsafeDecode62pow10# !acc !arr !off !d = if d < 10
  then case decodeByte (indexAsciiArray arr off) of
    Nothing -> (# (# #) | #)
    Just w ->
      let acc' = acc * 62 + w
       in unsafeDecode62pow10# acc' arr (off + 1) (d + 1)
  else (# | unW acc #)

decode128 :: Bytes -> Maybe Word128
{-# inline decode128 #-}
decode128 (Bytes (ByteArray arr) (I# off) (I# len)) =
  case decode128# arr off len of
    (# (# #) | #) -> Nothing
    (# | (# a, b #) #) -> Just (Word128 (W64# a) (W64# b))

decode128# :: ByteArray# -> Int# -> Int# -> (# (# #) | (# Word#, Word# #) #)
{-# noinline decode128# #-}
decode128# arr off len
  | isTrue# (len ># 20# ) =
      case unsafeDecode62pow10# 0 (ByteArray arr) (I# (off +# len -# 10# )) 0 of
        (# (# #) | #) -> (# (# #) | #)
        (# | c #) -> case unsafeDecode62pow10# 0 (ByteArray arr) (I# (off +# len -# 20# )) 0 of
          (# (# #) | #) -> (# (# #) | #)
          (# | b #) -> case decode64# 0 (Bytes (ByteArray arr) (I# off) (I# (len -# 20# ))) of
            (# (# #) | #) -> (# (# #) | #)
            (# | a #) -> case Word128 0 (W64# c) + (Word128 0 n62pow10 * (Word128 0 (W64# b) + (Word128 0 n62pow10 * Word128 0 (W64# a)))) of
              Word128 (W64# x) (W64# y) -> (# | (# x, y #) #)
  | isTrue# (len ># 10# ) =
      case unsafeDecode62pow10# 0 (ByteArray arr) (I# (off +# len -# 10# )) 0 of
        (# (# #) | #) -> (# (# #) | #)
        (# | b #) -> case decode64# 0 (Bytes (ByteArray arr) (I# off) (I# (len -# 10# ))) of
          (# (# #) | #) -> (# (# #) | #)
          (# | a #) -> case Word128 0 (W64# b) + (fromIntegral n62pow10 * Word128 0 (W64# a)) of
            Word128 (W64# x) (W64# y) -> (# | (# x, y #) #)
  | otherwise = case decode64# 0 (Bytes (ByteArray arr) (I# off) (I# len)) of
      (# (# #) | #) -> (# (# #) | #)
      (# | w #) -> (# | (# 0##, w #) #)

indexAsciiArray :: ByteArray -> Int -> Char
indexAsciiArray (ByteArray arr) (I# i) = C# (indexCharArray# arr i)
