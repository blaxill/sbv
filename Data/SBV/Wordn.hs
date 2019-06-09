{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE UndecidableInstances  #-}

module Data.SBV.Wordn
  ( Wordn
  , Intn
  , SWordn
  , SIntn
  ) where

import           GHC.Enum           (boundedEnumFrom, boundedEnumFromThen,
                                     predError, succError)
import           GHC.TypeLits       (KnownNat, Nat, natVal)

import           Data.Binary        (Binary, get, put)
import           Data.Bits
import           Data.Data          (Data)
import           Data.Proxy         (Proxy (..))
import           Data.Typeable      (Typeable)

import           Data.SBV
import           Data.SBV.Control
import           Data.SBV.Internals


newtype Wordn (n :: Nat) = Wordn Integer
  deriving (Eq, Ord, Data, Typeable)
newtype Intn (n :: Nat) = Intn Integer
  deriving (Eq, Ord, Data, Typeable)

natInt :: KnownNat n => Proxy n -> Int
natInt = fromEnum . natVal

maxWordn :: KnownNat n => Proxy n -> Integer
maxWordn p = (1 `shiftL` natInt p) - 1

maxIntn :: KnownNat n => Proxy n -> Integer
maxIntn p = (1 `shiftL` (natInt p - 1)) - 1

minIntn :: KnownNat n => Proxy n -> Integer
minIntn p = (-maxIntn p) -1

wordn :: forall n . (KnownNat n) => Integer -> Wordn n
wordn x = Wordn (x .&. maxWordn (Proxy @n))

intn :: forall n . (KnownNat n) => Integer -> Intn n
intn x = Intn (signum  x * (x .&. maxIntn (Proxy @n)))

instance (KnownNat n) => SMTValue (Wordn n) where
  sexprToVal = fmap wordn . sexprToVal
instance (KnownNat n) => SMTValue (Intn n) where
  sexprToVal = fmap intn . sexprToVal

instance Show (Wordn n) where
  show (Wordn x) = show x
instance Show (Intn n) where
  show (Intn x) = show x

instance (KnownNat n) => Read (Wordn n) where
  readsPrec p s = [ (wordn x, s') | (x, s') <- readsPrec p s ]
instance (KnownNat n) => Read (Intn n) where
  readsPrec p s = [ (intn x, s') | (x, s') <- readsPrec p s ]

instance (KnownNat n) => Bounded (Wordn n) where
  minBound = Wordn 0
  maxBound = Wordn (maxWordn $ Proxy @n)
instance (KnownNat n) => Bounded (Intn n) where
  minBound = Intn 0
  maxBound = Intn (maxIntn $ Proxy @n)

instance (KnownNat n) => Enum (Wordn n) where
  succ (Wordn x) = if x < maxWordn (Proxy @n) then Wordn (succ x) else succError "Wordn"
  pred (Wordn x) = if x > 0 then Wordn (pred x) else predError "Wordn"
  toEnum i = Wordn (toEnum i)
  fromEnum (Wordn x) = fromEnum x
  enumFrom                                     = boundedEnumFrom
  enumFromThen                                 = boundedEnumFromThen
  enumFromTo     (Wordn x) (Wordn y)           = map Wordn (enumFromTo x y)
  enumFromThenTo (Wordn x) (Wordn y) (Wordn z) = map Wordn (enumFromThenTo x y z)
instance (KnownNat n) => Enum (Intn n) where
  succ (Intn x) = if x < maxIntn (Proxy @n) then Intn (succ x) else succError "Intn"
  pred (Intn x) = if x > minIntn (Proxy @n) then Intn (pred x) else predError "Intn"
  toEnum i = Intn (toEnum i)
  fromEnum (Intn x) = fromEnum x
  enumFrom                                  = boundedEnumFrom
  enumFromThen                              = boundedEnumFromThen
  enumFromTo     (Intn x) (Intn y)          = map Intn (enumFromTo x y)
  enumFromThenTo (Intn x) (Intn y) (Intn z) = map Intn (enumFromThenTo x y z)

instance (KnownNat n) => Num (Wordn n) where
  Wordn x + Wordn y = wordn (x + y)
  Wordn x * Wordn y = wordn (x * y)
  Wordn x - Wordn y = wordn (x - y)
  negate (Wordn x)  = wordn (negate x)
  abs (Wordn x)     = Wordn x
  signum (Wordn x)  = Wordn (if x == 0 then 0 else 1)
  fromInteger n     = wordn (fromInteger n)
instance (KnownNat n) => Num (Intn n) where
  Intn x + Intn y = intn (x + y)
  Intn x * Intn y = intn (x * y)
  Intn x - Intn y = intn (x - y)
  negate (Intn x)  = intn (negate x)
  abs (Intn x)     = Intn x
  signum (Intn x)
    | x == 0 = 0
    | x > 0 = 1
    | x < 0 = -1
  fromInteger n     = intn (fromInteger n)

instance (KnownNat n) => Real (Wordn n) where
  toRational (Wordn x) = toRational x
instance (KnownNat n) => Real (Intn n) where
  toRational (Intn x) = toRational x

instance (KnownNat n) => Integral (Wordn n) where
  quotRem (Wordn x) (Wordn y) = (Wordn q, Wordn r)
    where (q, r) = quotRem x y
  toInteger (Wordn x) = toInteger x
instance (KnownNat n) => Integral (Intn n) where
  quotRem (Intn x) (Intn y) = (Intn q, Intn r)
    where (q, r) = quotRem x y
  toInteger (Intn x) = toInteger x

instance (KnownNat n) => Bits (Wordn n) where
  Wordn x  .&.  Wordn y = wordn (x  .&.  y)
  Wordn x  .|.  Wordn y = wordn (x  .|.  y)
  Wordn x `xor` Wordn y = wordn (x `xor` y)
  complement (Wordn x)  = wordn (x `xor` maxWordn (Proxy @n))
  Wordn x `shift`  i    = wordn (shift x i)
  Wordn x `shiftL` i    = wordn (shiftL x i)
  Wordn x `shiftR` i    = wordn (shiftR x i)
  Wordn x `rotate` i    = wordn (x `shiftL` i .|. x `shiftR` (bs-i))
    where bs = natInt (Proxy @n)
  bitSize _             = natInt (Proxy @n)
  bitSizeMaybe _        = Just $ natInt (Proxy @n)
  isSigned _            = False
  testBit (Wordn x)     = testBit x
  bit i                 = wordn (bit i)
  popCount (Wordn x)    = popCount x
instance (KnownNat n) => Bits (Intn n) where
  Intn x  .&.  Intn y = intn (x  .&.  y)
  Intn x  .|.  Intn y = intn (x  .|.  y)
  Intn x `xor` Intn y = intn (x `xor` y)
  complement (Intn x) = intn (x `xor` maxIntn (Proxy @n))
  Intn x `shift`  i   = intn (shift x i)
  Intn x `shiftL` i   = intn (shiftL x i)
  Intn x `shiftR` i   = intn (shiftR x i)
  Intn x `rotate` i   = intn (x `shiftL` i .|. x `shiftR` (bs-i))
    where bs = natInt (Proxy @n)
  bitSize _           = natInt (Proxy @n)
  bitSizeMaybe _      = Just $ natInt (Proxy @n)
  isSigned _          = False
  testBit (Intn x)    = testBit x
  bit i               = intn (bit i)
  popCount (Intn x)   = popCount x

type SWordn n = SBV (Wordn n)
type SIntn n = SBV (Intn n)

instance (KnownNat n) => SymWord (Wordn n) where
  mkSymWord  = genMkSymVar (KBounded False (natInt (Proxy @n)))
  literal    = genLiteral  (KBounded False (natInt (Proxy @n)))
  fromCW     = genFromCW
instance (KnownNat n) => SymWord (Intn n) where
  mkSymWord  = genMkSymVar (KBounded True (natInt (Proxy @n)))
  literal    = genLiteral  (KBounded True (natInt (Proxy @n)))
  fromCW     = genFromCW

instance (KnownNat n) => HasKind (Wordn n) where
  kindOf _ = KBounded False (natInt (Proxy @n))
instance (KnownNat n) => HasKind (Intn n) where
  kindOf _ = KBounded False (natInt (Proxy @n))

instance (KnownNat n) => SatModel (Wordn n) where
  parseCWs = genParse (KBounded False (natInt (Proxy @n)))
instance (KnownNat n) => SatModel (Intn n) where
  parseCWs = genParse (KBounded True (natInt (Proxy @n)))

-- | SDvisible instance, using 0-extension
instance (KnownNat n) => SDivisible (Wordn n) where
  sQuotRem x 0 = (0, x)
  sQuotRem x y = x `quotRem` y
  sDivMod  x 0 = (0, x)
  sDivMod  x y = x `divMod` y
instance (KnownNat n) => SDivisible (Intn n) where
  sQuotRem x 0 = (0, x)
  sQuotRem x y = x `quotRem` y
  sDivMod  x 0 = (0, x)
  sDivMod  x y = x `divMod` y

-- | SDvisible instance, using default methods
instance (KnownNat n) => SDivisible (SWordn n) where
  sQuotRem = liftQRem
  sDivMod  = liftDMod
instance (KnownNat n) => SDivisible (SIntn n) where
  sQuotRem = liftQRem
  sDivMod  = liftDMod

-- | SIntegral instance, using default methods
instance (KnownNat n) => SIntegral (Wordn n)
instance (KnownNat n) => SIntegral (Intn n)

instance (KnownNat n) => Binary (Wordn n) where
  put (Wordn x) = put x
  get = Wordn <$> get
instance (KnownNat n) => Binary (Intn n) where
  put (Intn x) = put x
  get = Intn <$> get

instance (KnownNat n) => SFiniteBits (Wordn n) where sFiniteBitSize _ = natInt (Proxy @n)
instance (KnownNat n) => SFiniteBits (Intn n) where sFiniteBitSize _ = natInt (Proxy @n)
