-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Core.Model
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Instance declarations for our symbolic world
-----------------------------------------------------------------------------

{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards         #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}

{-# OPTIONS_GHC -fno-warn-orphans  #-}

module Data.SBV.Core.Model (
    Mergeable(..), EqSymbolic(..), OrdSymbolic(..), SDivisible(..), Uninterpreted(..), Metric(..), assertWithPenalty, SIntegral, SFiniteBits(..)
  , ite, iteLazy, sFromIntegral, sShiftLeft, sShiftRight, sRotateLeft, sRotateRight, sSignedShiftArithRight, (.^)
  , oneIf, genVar, genVar_, forall, forall_, exists, exists_
  , pbAtMost, pbAtLeast, pbExactly, pbLe, pbGe, pbEq, pbMutexed, pbStronglyMutexed
  , sBool, sBools, sWord8, sWord8s, sWord16, sWord16s, sWord32
  , sWord32s, sWord64, sWord64s, sInt8, sInt8s, sInt16, sInt16s, sInt32, sInt32s, sInt64
  , sInt64s, sInteger, sIntegers, sReal, sReals, sFloat, sFloats, sDouble, sDoubles, sChar, sChars, sString, sStrings, sList, sLists
  , slet
  , sRealToSInteger, label, observe
  , sAssert
  , liftQRem, liftDMod, symbolicMergeWithKind
  , genLiteral, genFromCW, genMkSymVar
  , sbvQuickCheck
  )
  where

import Control.Applicative  (ZipList(ZipList))
import Control.Monad        (when, unless, mplus)
import Control.Monad.Trans  (liftIO)
import Control.Monad.Reader (ask)

import GHC.Generics (U1(..), M1(..), (:*:)(..), K1(..))
import qualified GHC.Generics as G

import GHC.Stack

import Data.Array  (Array, Ix, listArray, elems, bounds, rangeSize)
import Data.Bits   (Bits(..))
import Data.Char   (toLower, isDigit)
import Data.Int    (Int8, Int16, Int32, Int64)
import Data.List   (genericLength, genericIndex, genericTake, unzip4, unzip5, unzip6, unzip7, intercalate, isPrefixOf)
import Data.Maybe  (fromMaybe)
import Data.String (IsString(..))
import Data.Word   (Word8, Word16, Word32, Word64)

import Data.Dynamic (fromDynamic, toDyn)

import Test.QuickCheck                         (Testable(..), Arbitrary(..))
import qualified Test.QuickCheck.Test    as QC (isSuccess)
import qualified Test.QuickCheck         as QC (quickCheckResult, counterexample)
import qualified Test.QuickCheck.Monadic as QC (monadicIO, run, assert, pre, monitor)

import Data.SBV.Core.AlgReals
import Data.SBV.Core.Data
import Data.SBV.Core.Symbolic
import Data.SBV.Core.Operations

import Data.SBV.Provers.Prover (defaultSMTCfg, SafeResult(..))
import Data.SBV.SMT.SMT        (showModel)

import Data.SBV.Utils.Boolean
import Data.SBV.Utils.Lib      (isKString)

-- Symbolic-Word class instances

-- | Generate a finite symbolic bitvector, named
genVar :: Maybe Quantifier -> Kind -> String -> Symbolic (SBV a)
genVar q k = mkSymSBV q k . Just

-- | Generate a finite symbolic bitvector, unnamed
genVar_ :: Maybe Quantifier -> Kind -> Symbolic (SBV a)
genVar_ q k = mkSymSBV q k Nothing

-- | Generate a finite constant bitvector
genLiteral :: Integral a => Kind -> a -> SBV b
genLiteral k = SBV . SVal k . Left . mkConstCW k

-- | Convert a constant to an integral value
genFromCW :: Integral a => CW -> a
genFromCW (CW _ (CWInteger x)) = fromInteger x
genFromCW c                    = error $ "genFromCW: Unsupported non-integral value: " ++ show c

-- | Generically make a symbolic var
genMkSymVar :: Kind -> Maybe Quantifier -> Maybe String -> Symbolic (SBV a)
genMkSymVar k mbq Nothing  = genVar_ mbq k
genMkSymVar k mbq (Just s) = genVar  mbq k s

-- | Base type of () allows simple construction for uninterpreted types.
instance SymWord ()
instance HasKind ()

instance SymWord Bool where
  mkSymWord  = genMkSymVar KBool
  literal x  = SBV (svBool x)
  fromCW     = cwToBool

instance SymWord Word8 where
  mkSymWord  = genMkSymVar (KBounded False 8)
  literal    = genLiteral  (KBounded False 8)
  fromCW     = genFromCW

instance SymWord Int8 where
  mkSymWord  = genMkSymVar (KBounded True 8)
  literal    = genLiteral  (KBounded True 8)
  fromCW     = genFromCW

instance SymWord Word16 where
  mkSymWord  = genMkSymVar (KBounded False 16)
  literal    = genLiteral  (KBounded False 16)
  fromCW     = genFromCW

instance SymWord Int16 where
  mkSymWord  = genMkSymVar (KBounded True 16)
  literal    = genLiteral  (KBounded True 16)
  fromCW     = genFromCW

instance SymWord Word32 where
  mkSymWord  = genMkSymVar (KBounded False 32)
  literal    = genLiteral  (KBounded False 32)
  fromCW     = genFromCW

instance SymWord Int32 where
  mkSymWord  = genMkSymVar (KBounded True 32)
  literal    = genLiteral  (KBounded True 32)
  fromCW     = genFromCW

instance SymWord Word64 where
  mkSymWord  = genMkSymVar (KBounded False 64)
  literal    = genLiteral  (KBounded False 64)
  fromCW     = genFromCW

instance SymWord Int64 where
  mkSymWord  = genMkSymVar (KBounded True 64)
  literal    = genLiteral  (KBounded True 64)
  fromCW     = genFromCW

instance SymWord Integer where
  mkSymWord  = genMkSymVar KUnbounded
  literal    = SBV . SVal KUnbounded . Left . mkConstCW KUnbounded
  fromCW     = genFromCW

instance SymWord AlgReal where
  mkSymWord  = genMkSymVar KReal
  literal    = SBV . SVal KReal . Left . CW KReal . CWAlgReal
  fromCW (CW _ (CWAlgReal a)) = a
  fromCW c                    = error $ "SymWord.AlgReal: Unexpected non-real value: " ++ show c
  -- AlgReal needs its own definition of isConcretely
  -- to make sure we avoid using unimplementable Haskell functions
  isConcretely (SBV (SVal KReal (Left (CW KReal (CWAlgReal v))))) p
     | isExactRational v = p v
  isConcretely _ _       = False

instance SymWord Float where
  mkSymWord  = genMkSymVar KFloat
  literal    = SBV . SVal KFloat . Left . CW KFloat . CWFloat
  fromCW (CW _ (CWFloat a)) = a
  fromCW c                  = error $ "SymWord.Float: Unexpected non-float value: " ++ show c
  -- For Float, we conservatively return 'False' for isConcretely. The reason is that
  -- this function is used for optimizations when only one of the argument is concrete,
  -- and in the presence of NaN's it would be incorrect to do any optimization
  isConcretely _ _ = False

instance SymWord Double where
  mkSymWord  = genMkSymVar KDouble
  literal    = SBV . SVal KDouble . Left . CW KDouble . CWDouble
  fromCW (CW _ (CWDouble a)) = a
  fromCW c                   = error $ "SymWord.Double: Unexpected non-double value: " ++ show c
  -- For Double, we conservatively return 'False' for isConcretely. The reason is that
  -- this function is used for optimizations when only one of the argument is concrete,
  -- and in the presence of NaN's it would be incorrect to do any optimization
  isConcretely _ _ = False

instance SymWord Char where
  mkSymWord = genMkSymVar KChar
  literal c = SBV . SVal KChar . Left . CW KChar $ CWChar c
  fromCW (CW _ (CWChar a)) = a
  fromCW c                 = error $ "SymWord.String: Unexpected non-char value: " ++ show c

instance SymWord a => SymWord [a] where
  mkSymWord
    | isKString (undefined :: [a]) = genMkSymVar KString
    | True                         = genMkSymVar (KList (kindOf (undefined :: a)))

  literal as
    | isKString (undefined :: [a]) = case fromDynamic (toDyn as) of
                                       Just s  -> SBV . SVal KString . Left . CW KString . CWString $ s
                                       Nothing -> error "SString: Cannot construct literal string!"
    | True                         = let k = KList (kindOf (undefined :: a))
                                         toCWVal a = case literal a of
                                                       SBV (SVal _ (Left (CW _ cwval))) -> cwval
                                                       _                                -> error "SymWord.Sequence: could not produce a concrete word for value"
                                     in SBV $ SVal k $ Left $ CW k $ CWList $ map toCWVal as

  fromCW (CW _ (CWString a)) = fromMaybe (error "SString: Cannot extract a literal string!")
                                         (fromDynamic (toDyn a))
  fromCW (CW _ (CWList a))   = fromCW . CW (kindOf (undefined :: a)) <$> a
  fromCW c                   = error $ "SymWord.fromCW: Unexpected non-list value: " ++ show c

instance IsString SString where
  fromString = literal

------------------------------------------------------------------------------------
-- * Smart constructors for creating symbolic values. These are not strictly
-- necessary, as they are mere aliases for 'symbolic' and 'symbolics', but
-- they nonetheless make programming easier.
------------------------------------------------------------------------------------
-- | Declare an 'SBool'
sBool :: String -> Symbolic SBool
sBool = symbolic

-- | Declare a list of 'SBool's
sBools :: [String] -> Symbolic [SBool]
sBools = symbolics

-- | Declare an 'SWord8'
sWord8 :: String -> Symbolic SWord8
sWord8 = symbolic

-- | Declare a list of 'SWord8's
sWord8s :: [String] -> Symbolic [SWord8]
sWord8s = symbolics

-- | Declare an 'SWord16'
sWord16 :: String -> Symbolic SWord16
sWord16 = symbolic

-- | Declare a list of 'SWord16's
sWord16s :: [String] -> Symbolic [SWord16]
sWord16s = symbolics

-- | Declare an 'SWord32'
sWord32 :: String -> Symbolic SWord32
sWord32 = symbolic

-- | Declare a list of 'SWord32's
sWord32s :: [String] -> Symbolic [SWord32]
sWord32s = symbolics

-- | Declare an 'SWord64'
sWord64 :: String -> Symbolic SWord64
sWord64 = symbolic

-- | Declare a list of 'SWord64's
sWord64s :: [String] -> Symbolic [SWord64]
sWord64s = symbolics

-- | Declare an 'SInt8'
sInt8 :: String -> Symbolic SInt8
sInt8 = symbolic

-- | Declare a list of 'SInt8's
sInt8s :: [String] -> Symbolic [SInt8]
sInt8s = symbolics

-- | Declare an 'SInt16'
sInt16 :: String -> Symbolic SInt16
sInt16 = symbolic

-- | Declare a list of 'SInt16's
sInt16s :: [String] -> Symbolic [SInt16]
sInt16s = symbolics

-- | Declare an 'SInt32'
sInt32 :: String -> Symbolic SInt32
sInt32 = symbolic

-- | Declare a list of 'SInt32's
sInt32s :: [String] -> Symbolic [SInt32]
sInt32s = symbolics

-- | Declare an 'SInt64'
sInt64 :: String -> Symbolic SInt64
sInt64 = symbolic

-- | Declare a list of 'SInt64's
sInt64s :: [String] -> Symbolic [SInt64]
sInt64s = symbolics

-- | Declare an 'SInteger'
sInteger:: String -> Symbolic SInteger
sInteger = symbolic

-- | Declare a list of 'SInteger's
sIntegers :: [String] -> Symbolic [SInteger]
sIntegers = symbolics

-- | Declare an 'SReal'
sReal:: String -> Symbolic SReal
sReal = symbolic

-- | Declare a list of 'SReal's
sReals :: [String] -> Symbolic [SReal]
sReals = symbolics

-- | Declare an 'SFloat'
sFloat :: String -> Symbolic SFloat
sFloat = symbolic

-- | Declare a list of 'SFloat's
sFloats :: [String] -> Symbolic [SFloat]
sFloats = symbolics

-- | Declare an 'SDouble'
sDouble :: String -> Symbolic SDouble
sDouble = symbolic

-- | Declare a list of 'SDouble's
sDoubles :: [String] -> Symbolic [SDouble]
sDoubles = symbolics

-- | Declare an 'SChar'
sChar :: String -> Symbolic SChar
sChar = symbolic

-- | Declare an 'SString'
sString :: String -> Symbolic SString
sString = symbolic

-- | Declare a list of 'SChar's
sChars :: [String] -> Symbolic [SChar]
sChars = symbolics

-- | Declare a list of 'SString's
sStrings :: [String] -> Symbolic [SString]
sStrings = symbolics

-- | Declare an 'SList'
sList :: forall a. SymWord a => String -> Symbolic (SList a)
sList = symbolic

-- | Declare a list of 'SList's
sLists :: forall a. SymWord a => [String] -> Symbolic [SList a]
sLists = symbolics

-- | Convert an SReal to an SInteger. That is, it computes the
-- largest integer @n@ that satisfies @sIntegerToSReal n <= r@
-- essentially giving us the @floor@.
--
-- For instance, @1.3@ will be @1@, but @-1.3@ will be @-2@.
sRealToSInteger :: SReal -> SInteger
sRealToSInteger x
  | Just i <- unliteral x, isExactRational i
  = literal $ floor (toRational i)
  | True
  = SBV (SVal KUnbounded (Right (cache y)))
  where y st = do xsw <- sbvToSW st x
                  newExpr st KUnbounded (SBVApp (KindCast KReal KUnbounded) [xsw])

-- | label: Label the result of an expression. This is essentially a no-op, but useful as it generates a comment in the generated C/SMT-Lib code.
-- Note that if the argument is a constant, then the label is dropped completely, per the usual constant folding strategy.
label :: SymWord a => String -> SBV a -> SBV a
label m x
   | Just _ <- unliteral x = x
   | True                  = SBV $ SVal k $ Right $ cache r
  where k    = kindOf x
        r st = do xsw <- sbvToSW st x
                  newExpr st k (SBVApp (Label m) [xsw])

-- | Observe the value of an expression.  Such values are useful in model construction, as they are printed part of a satisfying model, or a
-- counter-example. The same works for quick-check as well. Useful when we want to see intermediate values, or expected/obtained
-- pairs in a particular run.
observe :: SymWord a => String -> SBV a -> Symbolic ()
observe m x
  | null m
  = error "SBV.observe: Bad empty name!"
  | map toLower m `elem` smtLibReservedNames
  = error $ "SBV.observe: The name chosen is reserved, please change it!: " ++ show m
  | "s" `isPrefixOf` m && all isDigit (drop 1 m)
  = error $ "SBV.observe: Names of the form sXXX are internal to SBV, please use a different name: " ++ show m
  | True
  = do st <- ask
       liftIO $ do xsw <- sbvToSW st x
                   recordObservable st m xsw

-- | Symbolic Equality. Note that we can't use Haskell's 'Eq' class since Haskell insists on returning Bool
-- Comparing symbolic values will necessarily return a symbolic value.
infix 4 .==, ./=
class EqSymbolic a where
  -- | Symbolic equality.
  (.==) :: a -> a -> SBool
  -- | Symbolic inequality.
  (./=) :: a -> a -> SBool

  -- | Returns (symbolic) true if all the elements of the given list are different.
  distinct :: [a] -> SBool

  -- | Returns (symbolic) true if all the elements of the given list are the same.
  allEqual :: [a] -> SBool

  -- | Symbolic membership test.
  sElem    :: a -> [a] -> SBool
  {-# MINIMAL (.==) #-}

  x ./= y = bnot (x .== y)

  allEqual []     = true
  allEqual (x:xs) = bAll (x .==) xs

  -- Default implementation of distinct. Note that we override
  -- this method for the base types to generate better code.
  distinct []     = true
  distinct (x:xs) = bAll (x ./=) xs &&& distinct xs

  sElem x xs = bAny (.== x) xs

-- | Symbolic Comparisons. Similar to 'Eq', we cannot implement Haskell's 'Ord' class
-- since there is no way to return an 'Ordering' value from a symbolic comparison.
-- Furthermore, 'OrdSymbolic' requires 'Mergeable' to implement if-then-else, for the
-- benefit of implementing symbolic versions of 'max' and 'min' functions.
infix 4 .<, .<=, .>, .>=
class (Mergeable a, EqSymbolic a) => OrdSymbolic a where
  -- | Symbolic less than.
  (.<)  :: a -> a -> SBool
  -- | Symbolic less than or equal to.
  (.<=) :: a -> a -> SBool
  -- | Symbolic greater than.
  (.>)  :: a -> a -> SBool
  -- | Symbolic greater than or equal to.
  (.>=) :: a -> a -> SBool
  -- | Symbolic minimum.
  smin  :: a -> a -> a
  -- | Symbolic maximum.
  smax  :: a -> a -> a
  -- | Is the value withing the allowed /inclusive/ range?
  inRange    :: a -> (a, a) -> SBool

  {-# MINIMAL (.<) #-}

  a .<= b    = a .< b ||| a .== b
  a .>  b    = b .<  a
  a .>= b    = b .<= a

  a `smin` b = ite (a .<= b) a b
  a `smax` b = ite (a .<= b) b a

  inRange x (y, z) = x .>= y &&& x .<= z


{- We can't have a generic instance of the form:

instance Eq a => EqSymbolic a where
  x .== y = if x == y then true else false

even if we're willing to allow Flexible/undecidable instances..
This is because if we allow this it would imply EqSymbolic (SBV a);
since (SBV a) has to be Eq as it must be a Num. But this wouldn't be
the right choice obviously; as the Eq instance is bogus for SBV
for natural reasons..
-}

instance EqSymbolic (SBV a) where
  SBV x .== SBV y = SBV (svEqual x y)
  SBV x ./= SBV y = SBV (svNotEqual x y)

  -- Custom version of distinct that generates better code for base types
  distinct []  = true
  distinct [_] = true
  distinct xs
    | all isConc xs
    = checkDiff xs
    | True
    = SBV (SVal KBool (Right (cache r)))
    where r st = do xsw <- mapM (sbvToSW st) xs
                    newExpr st KBool (SBVApp NotEqual xsw)

          -- We call this in case all are concrete, which will
          -- reduce to a constant and generate no code at all!
          -- Note that this is essentially the same as the default
          -- definition, which unfortunately we can no longer call!
          checkDiff []     = true
          checkDiff (a:as) = bAll (a ./=) as &&& checkDiff as

          -- Sigh, we can't use isConcrete since that requires SymWord
          -- constraint that we don't have here. (To support SBools.)
          isConc (SBV (SVal _ (Left _))) = True
          isConc _                       = False

instance SymWord a => OrdSymbolic (SBV a) where
  SBV x .<  SBV y = SBV (svLessThan x y)
  SBV x .<= SBV y = SBV (svLessEq x y)
  SBV x .>  SBV y = SBV (svGreaterThan x y)
  SBV x .>= SBV y = SBV (svGreaterEq x y)

-- Bool
instance EqSymbolic Bool where
  x .== y = if x == y then true else false

-- Lists
instance EqSymbolic a => EqSymbolic [a] where
  []     .== []     = true
  (x:xs) .== (y:ys) = x .== y &&& xs .== ys
  _      .== _      = false

instance OrdSymbolic a => OrdSymbolic [a] where
  []     .< []     = false
  []     .< _      = true
  _      .< []     = false
  (x:xs) .< (y:ys) = x .< y ||| (x .== y &&& xs .< ys)

-- Maybe
instance EqSymbolic a => EqSymbolic (Maybe a) where
  Nothing .== Nothing = true
  Just a  .== Just b  = a .== b
  _       .== _       = false

instance (OrdSymbolic a) => OrdSymbolic (Maybe a) where
  Nothing .<  Nothing = false
  Nothing .<  _       = true
  Just _  .<  Nothing = false
  Just a  .<  Just b  = a .< b

-- Either
instance (EqSymbolic a, EqSymbolic b) => EqSymbolic (Either a b) where
  Left a  .== Left b  = a .== b
  Right a .== Right b = a .== b
  _       .== _       = false

instance (OrdSymbolic a, OrdSymbolic b) => OrdSymbolic (Either a b) where
  Left a  .< Left b  = a .< b
  Left _  .< Right _ = true
  Right _ .< Left _  = false
  Right a .< Right b = a .< b

-- 2-Tuple
instance (EqSymbolic a, EqSymbolic b) => EqSymbolic (a, b) where
  (a0, b0) .== (a1, b1) = a0 .== a1 &&& b0 .== b1

instance (OrdSymbolic a, OrdSymbolic b) => OrdSymbolic (a, b) where
  (a0, b0) .< (a1, b1) = a0 .< a1 ||| (a0 .== a1 &&& b0 .< b1)

-- 3-Tuple
instance (EqSymbolic a, EqSymbolic b, EqSymbolic c) => EqSymbolic (a, b, c) where
  (a0, b0, c0) .== (a1, b1, c1) = (a0, b0) .== (a1, b1) &&& c0 .== c1

instance (OrdSymbolic a, OrdSymbolic b, OrdSymbolic c) => OrdSymbolic (a, b, c) where
  (a0, b0, c0) .< (a1, b1, c1) = (a0, b0) .< (a1, b1) ||| ((a0, b0) .== (a1, b1) &&& c0 .< c1)

-- 4-Tuple
instance (EqSymbolic a, EqSymbolic b, EqSymbolic c, EqSymbolic d) => EqSymbolic (a, b, c, d) where
  (a0, b0, c0, d0) .== (a1, b1, c1, d1) = (a0, b0, c0) .== (a1, b1, c1) &&& d0 .== d1

instance (OrdSymbolic a, OrdSymbolic b, OrdSymbolic c, OrdSymbolic d) => OrdSymbolic (a, b, c, d) where
  (a0, b0, c0, d0) .< (a1, b1, c1, d1) = (a0, b0, c0) .< (a1, b1, c1) ||| ((a0, b0, c0) .== (a1, b1, c1) &&& d0 .< d1)

-- 5-Tuple
instance (EqSymbolic a, EqSymbolic b, EqSymbolic c, EqSymbolic d, EqSymbolic e) => EqSymbolic (a, b, c, d, e) where
  (a0, b0, c0, d0, e0) .== (a1, b1, c1, d1, e1) = (a0, b0, c0, d0) .== (a1, b1, c1, d1) &&& e0 .== e1

instance (OrdSymbolic a, OrdSymbolic b, OrdSymbolic c, OrdSymbolic d, OrdSymbolic e) => OrdSymbolic (a, b, c, d, e) where
  (a0, b0, c0, d0, e0) .< (a1, b1, c1, d1, e1) = (a0, b0, c0, d0) .< (a1, b1, c1, d1) ||| ((a0, b0, c0, d0) .== (a1, b1, c1, d1) &&& e0 .< e1)

-- 6-Tuple
instance (EqSymbolic a, EqSymbolic b, EqSymbolic c, EqSymbolic d, EqSymbolic e, EqSymbolic f) => EqSymbolic (a, b, c, d, e, f) where
  (a0, b0, c0, d0, e0, f0) .== (a1, b1, c1, d1, e1, f1) = (a0, b0, c0, d0, e0) .== (a1, b1, c1, d1, e1) &&& f0 .== f1

instance (OrdSymbolic a, OrdSymbolic b, OrdSymbolic c, OrdSymbolic d, OrdSymbolic e, OrdSymbolic f) => OrdSymbolic (a, b, c, d, e, f) where
  (a0, b0, c0, d0, e0, f0) .< (a1, b1, c1, d1, e1, f1) =    (a0, b0, c0, d0, e0) .<  (a1, b1, c1, d1, e1)
                                                       ||| ((a0, b0, c0, d0, e0) .== (a1, b1, c1, d1, e1) &&& f0 .< f1)

-- 7-Tuple
instance (EqSymbolic a, EqSymbolic b, EqSymbolic c, EqSymbolic d, EqSymbolic e, EqSymbolic f, EqSymbolic g) => EqSymbolic (a, b, c, d, e, f, g) where
  (a0, b0, c0, d0, e0, f0, g0) .== (a1, b1, c1, d1, e1, f1, g1) = (a0, b0, c0, d0, e0, f0) .== (a1, b1, c1, d1, e1, f1) &&& g0 .== g1

instance (OrdSymbolic a, OrdSymbolic b, OrdSymbolic c, OrdSymbolic d, OrdSymbolic e, OrdSymbolic f, OrdSymbolic g) => OrdSymbolic (a, b, c, d, e, f, g) where
  (a0, b0, c0, d0, e0, f0, g0) .< (a1, b1, c1, d1, e1, f1, g1) =    (a0, b0, c0, d0, e0, f0) .<  (a1, b1, c1, d1, e1, f1)
                                                               ||| ((a0, b0, c0, d0, e0, f0) .== (a1, b1, c1, d1, e1, f1) &&& g0 .< g1)

-- | Symbolic Numbers. This is a simple class that simply incorporates all number like
-- base types together, simplifying writing polymorphic type-signatures that work for all
-- symbolic numbers, such as 'SWord8', 'SInt8' etc. For instance, we can write a generic
-- list-minimum function as follows:
--
-- @
--    mm :: SIntegral a => [SBV a] -> SBV a
--    mm = foldr1 (\a b -> ite (a .<= b) a b)
-- @
--
-- It is similar to the standard 'Integral' class, except ranging over symbolic instances.
class (SymWord a, Num a, Bits a, Integral a) => SIntegral a

-- 'SIntegral' Instances, skips Real/Float/Bool
instance SIntegral Word8
instance SIntegral Word16
instance SIntegral Word32
instance SIntegral Word64
instance SIntegral Int8
instance SIntegral Int16
instance SIntegral Int32
instance SIntegral Int64
instance SIntegral Integer

-- | Finite bit-length symbolic values. Essentially the same as 'SIntegral', but further leaves out 'Integer'. Loosely
-- based on Haskell's 'FiniteBits' class, but with more methods defined and structured differently to fit into the
-- symbolic world view. Minimal complete definition: 'sFiniteBitSize'.
class (SymWord a, Num a, Bits a) => SFiniteBits a where
    -- | Bit size.
    sFiniteBitSize      :: SBV a -> Int
    -- | Least significant bit of a word, always stored at index 0.
    lsb                 :: SBV a -> SBool
    -- | Most significant bit of a word, always stored at the last position.
    msb                 :: SBV a -> SBool
    -- | Big-endian blasting of a word into its bits.
    blastBE             :: SBV a -> [SBool]
    -- | Little-endian blasting of a word into its bits.
    blastLE             :: SBV a -> [SBool]
    -- | Reconstruct from given bits, given in little-endian.
    fromBitsBE          :: [SBool] -> SBV a
    -- | Reconstruct from given bits, given in little-endian.
    fromBitsLE          :: [SBool] -> SBV a
    -- | Replacement for 'testBit', returning 'SBool' instead of 'Bool'.
    sTestBit            :: SBV a -> Int -> SBool
    -- | Variant of 'sTestBit', where we want to extract multiple bit positions.
    sExtractBits        :: SBV a -> [Int] -> [SBool]
    -- | Variant of 'popCount', returning a symbolic value.
    sPopCount           :: SBV a -> SWord8
    -- | A combo of 'setBit' and 'clearBit', when the bit to be set is symbolic.
    setBitTo            :: SBV a -> Int -> SBool -> SBV a
    -- | Full adder, returns carry-out from the addition. Only for unsigned quantities.
    fullAdder           :: SBV a -> SBV a -> (SBool, SBV a)
    -- | Full multipler, returns both high and low-order bits. Only for unsigned quantities.
    fullMultiplier      :: SBV a -> SBV a -> (SBV a, SBV a)
    -- | Count leading zeros in a word, big-endian interpretation.
    sCountLeadingZeros  :: SBV a -> SWord8
    -- | Count trailing zeros in a word, big-endian interpretation.
    sCountTrailingZeros :: SBV a -> SWord8

    -- Default implementations
    lsb (SBV v) = SBV (svTestBit v 0)
    msb x       = sTestBit x (sFiniteBitSize x - 1)

    blastBE   = reverse . blastLE
    blastLE x = map (sTestBit x) [0 .. intSizeOf x - 1]

    fromBitsBE = fromBitsLE . reverse
    fromBitsLE bs
       | length bs /= w
       = error $ "SBV.SFiniteBits.fromBitsLE/BE: Expected: " ++ show w ++ " bits, received: " ++ show (length bs)
       | True
       = result
       where w = sFiniteBitSize result
             result = go 0 0 bs

             go !acc _  []     = acc
             go !acc !i (x:xs) = go (ite x (setBit acc i) acc) (i+1) xs

    sTestBit (SBV x) i = SBV (svTestBit x i)
    sExtractBits x     = map (sTestBit x)

    -- NB. 'sPopCount' returns an 'SWord8', which can overflow when used on quantities that have
    -- more than 255 bits. For the regular interface, this suffices for all types we support.
    -- For the Dynamic interface, if we ever implement this, this will fail for bit-vectors
    -- larger than that many bits. The alternative would be to return SInteger here, but that
    -- seems a total overkill for most use cases. If such is required, users are encouraged
    -- to define their own variants, which is rather easy.
    sPopCount x
      | isConcrete x  = go 0 x
      | True          = sum [ite b 1 0 | b <- blastLE x]
      where -- concrete case
            go !c 0 = c
            go !c w = go (c+1) (w .&. (w-1))

    setBitTo x i b = ite b (setBit x i) (clearBit x i)

    fullAdder a b
      | isSigned a = error "fullAdder: only works on unsigned numbers"
      | True       = (a .> s ||| b .> s, s)
      where s = a + b

    -- N.B. The higher-order bits are determined using a simple shift-add multiplier,
    -- thus involving bit-blasting. It'd be naive to expect SMT solvers to deal efficiently
    -- with properties involving this function, at least with the current state of the art.
    fullMultiplier a b
      | isSigned a = error "fullMultiplier: only works on unsigned numbers"
      | True       = (go (sFiniteBitSize a) 0 a, a*b)
      where go 0 p _ = p
            go n p x = let (c, p')  = ite (lsb x) (fullAdder p b) (false, p)
                           (o, p'') = shiftIn c p'
                           (_, x')  = shiftIn o x
                       in go (n-1) p'' x'
            shiftIn k v = (lsb v, mask .|. (v `shiftR` 1))
               where mask = ite k (bit (sFiniteBitSize v - 1)) 0

    -- See the note for 'sPopCount' for a comment on why we return 'SWord8'
    sCountLeadingZeros x = fromIntegral m - go m
      where m = sFiniteBitSize x - 1

            -- NB. When i is 0 below, which happens when x is 0 as we count all the way down,
            -- we return -1, which is equal to 2^n-1, giving us: n-1-(2^n-1) = n-2^n = n, as required, i.e., the bit-size.
            go :: Int -> SWord8
            go i | i < 0 = i8
                 | True  = ite (sTestBit x i) i8 (go (i-1))
               where i8 = literal (fromIntegral i :: Word8)

    -- See the note for 'sPopCount' for a comment on why we return 'SWord8'
    sCountTrailingZeros x = go 0
       where m = sFiniteBitSize x

             go :: Int -> SWord8
             go i | i >= m = i8
                  | True   = ite (sTestBit x i) i8 (go (i+1))
                where i8 = literal (fromIntegral i :: Word8)

-- 'SIntegral' Instances, skips Real/Float/Bool/Integer
instance SFiniteBits Word8  where sFiniteBitSize _ =  8
instance SFiniteBits Word16 where sFiniteBitSize _ = 16
instance SFiniteBits Word32 where sFiniteBitSize _ = 32
instance SFiniteBits Word64 where sFiniteBitSize _ = 64
instance SFiniteBits Int8   where sFiniteBitSize _ =  8
instance SFiniteBits Int16  where sFiniteBitSize _ = 16
instance SFiniteBits Int32  where sFiniteBitSize _ = 32
instance SFiniteBits Int64  where sFiniteBitSize _ = 64

-- | Returns 1 if the boolean is true, otherwise 0.
oneIf :: (Num a, SymWord a) => SBool -> SBV a
oneIf t = ite t 1 0

-- | Lift a pseudo-boolean op, performing checks
liftPB :: String -> PBOp -> [SBool] -> SBool
liftPB w o xs
  | Just e <- check o
  = error $ "SBV." ++ w ++ ": " ++ e
  | True
  = result
  where check (PB_AtMost  k) = pos k
        check (PB_AtLeast k) = pos k
        check (PB_Exactly k) = pos k
        check (PB_Le cs   k) = pos k `mplus` match cs
        check (PB_Ge cs   k) = pos k `mplus` match cs
        check (PB_Eq cs   k) = pos k `mplus` match cs

        pos k
          | k < 0 = Just $ "comparison value must be positive, received: " ++ show k
          | True  = Nothing

        match cs
          | any (< 0) cs = Just $ "coefficients must be non-negative. Received: " ++ show cs
          | lxs /= lcs   = Just $ "coefficient length must match number of arguments. Received: " ++ show (lcs, lxs)
          | True         = Nothing
          where lxs = length xs
                lcs = length cs

        result = SBV (SVal KBool (Right (cache r)))
        r st   = do xsw <- mapM (sbvToSW st) xs
                    -- PseudoBoolean's implicitly require support for integers, so make sure to register that kind!
                    registerKind st KUnbounded
                    newExpr st KBool (SBVApp (PseudoBoolean o) xsw)

-- | 'true' if at most `k` of the input arguments are 'true'
pbAtMost :: [SBool] -> Int -> SBool
pbAtMost xs k
 | k < 0             = error $ "SBV.pbAtMost: Non-negative value required, received: " ++ show k
 | all isConcrete xs = literal $ sum (map (pbToInteger "pbAtMost" 1) xs) <= fromIntegral k
 | True              = liftPB "pbAtMost" (PB_AtMost k) xs

-- | 'true' if at least `k` of the input arguments are 'true'
pbAtLeast :: [SBool] -> Int -> SBool
pbAtLeast xs k
 | k < 0             = error $ "SBV.pbAtLeast: Non-negative value required, received: " ++ show k
 | all isConcrete xs = literal $ sum (map (pbToInteger "pbAtLeast" 1) xs) >= fromIntegral k
 | True              = liftPB "pbAtLeast" (PB_AtLeast k) xs

-- | 'true' if exactly `k` of the input arguments are 'true'
pbExactly :: [SBool] -> Int -> SBool
pbExactly xs k
 | k < 0             = error $ "SBV.pbExactly: Non-negative value required, received: " ++ show k
 | all isConcrete xs = literal $ sum (map (pbToInteger "pbExactly" 1) xs) == fromIntegral k
 | True              = liftPB "pbExactly" (PB_Exactly k) xs

-- | 'true' if the sum of coefficients for 'true' elements is at most 'k'. Generalizes 'pbAtMost'.
pbLe :: [(Int, SBool)] -> Int -> SBool
pbLe xs k
 | k < 0                       = error $ "SBV.pbLe: Non-negative value required, received: " ++ show k
 | all isConcrete (map snd xs) = literal $ sum [pbToInteger "pbLe" c b | (c, b) <- xs] <= fromIntegral k
 | True                        = liftPB "pbLe" (PB_Le (map fst xs) k) (map snd xs)

-- | 'true' if the sum of coefficients for 'true' elements is at least 'k'. Generalizes 'pbAtLeast'.
pbGe :: [(Int, SBool)] -> Int -> SBool
pbGe xs k
 | k < 0                       = error $ "SBV.pbGe: Non-negative value required, received: " ++ show k
 | all isConcrete (map snd xs) = literal $ sum [pbToInteger "pbGe" c b | (c, b) <- xs] >= fromIntegral k
 | True                        = liftPB "pbGe" (PB_Ge (map fst xs) k) (map snd xs)

-- | 'true' if the sum of coefficients for 'true' elements is exactly least 'k'. Useful for coding
-- /exactly K-of-N/ constraints, and in particular mutex constraints.
pbEq :: [(Int, SBool)] -> Int -> SBool
pbEq xs k
 | k < 0                       = error $ "SBV.pbEq: Non-negative value required, received: " ++ show k
 | all isConcrete (map snd xs) = literal $ sum [pbToInteger "pbEq" c b | (c, b) <- xs] == fromIntegral k
 | True                        = liftPB "pbEq" (PB_Eq (map fst xs) k) (map snd xs)

-- | 'true' if there is at most one set bit
pbMutexed :: [SBool] -> SBool
pbMutexed xs = pbAtMost xs 1

-- | 'true' if there is exactly one set bit
pbStronglyMutexed :: [SBool] -> SBool
pbStronglyMutexed xs = pbExactly xs 1

-- | Convert a concrete pseudo-boolean to given int; converting to integer
pbToInteger :: String -> Int -> SBool -> Integer
pbToInteger w c b
 | c < 0                 = error $ "SBV." ++ w ++ ": Non-negative coefficient required, received: " ++ show c
 | Just v <- unliteral b = if v then fromIntegral c else 0
 | True                  = error $ "SBV.pbToInteger: Received a symbolic boolean: " ++ show (c, b)

-- | Predicate for optimizing word operations like (+) and (*).
isConcreteZero :: SBV a -> Bool
isConcreteZero (SBV (SVal _     (Left (CW _     (CWInteger n))))) = n == 0
isConcreteZero (SBV (SVal KReal (Left (CW KReal (CWAlgReal v))))) = isExactRational v && v == 0
isConcreteZero _                                                  = False

-- | Predicate for optimizing word operations like (+) and (*).
isConcreteOne :: SBV a -> Bool
isConcreteOne (SBV (SVal _     (Left (CW _     (CWInteger 1))))) = True
isConcreteOne (SBV (SVal KReal (Left (CW KReal (CWAlgReal v))))) = isExactRational v && v == 1
isConcreteOne _                                                  = False

-- Num instance for symbolic words.
instance (Ord a, Num a, SymWord a) => Num (SBV a) where
  fromInteger = literal . fromIntegral
  SBV x + SBV y = SBV (svPlus x y)
  SBV x * SBV y = SBV (svTimes x y)
  SBV x - SBV y = SBV (svMinus x y)
  -- Abs is problematic for floating point, due to -0; case, so we carefully shuttle it down
  -- to the solver to avoid the can of worms. (Alternative would be to do an if-then-else here.)
  abs (SBV x) = SBV (svAbs x)
  signum a
    -- NB. The following "carefully" tests the number for == 0, as Float/Double's NaN and +/-0
    -- cases would cause trouble with explicit equality tests.
    | hasSign a = ite (a .> z) i
                $ ite (a .< z) (negate i) a
    | True      = ite (a .> z) i a
    where z = genLiteral (kindOf a) (0::Integer)
          i = genLiteral (kindOf a) (1::Integer)
  -- negate is tricky because on double/float -0 is different than 0; so we cannot
  -- just rely on the default definition; which would be 0-0, which is not -0!
  negate (SBV x) = SBV (svUNeg x)

-- | Symbolic exponentiation using bit blasting and repeated squaring.
--
-- N.B. The exponent must be unsigned/bounded if symbolic. Signed exponents will be rejected.
(.^) :: (Mergeable b, Num b, SIntegral e) => b -> SBV e -> b
b .^ e
  | isConcrete e, Just (x :: Integer) <- unliteral (sFromIntegral e)
  = if x >= 0 then let go n v
                        | n == 0 = 1
                        | even n =     go (n `div` 2) (v * v)
                        | True   = v * go (n `div` 2) (v * v)
                   in  go x b
              else error $ "(.^): exponentiation: negative exponent: " ++ show x
  | not (isBounded e) || isSigned e
  = error $ "(.^): exponentiation only works with unsigned bounded symbolic exponents, kind: " ++ show (kindOf e)
  | True
  =  -- NB. We can't simply use sTestBit and blastLE since they have SFiniteBit requirement
     -- but we want to have SIntegral here only.
     let SBV expt = e
         expBit i = SBV (svTestBit expt i)
         blasted  = map expBit [0 .. intSizeOf e - 1]
     in product $ zipWith (\use n -> ite use n 1)
                          blasted
                          (iterate (\x -> x*x) b)

instance (SymWord a, Fractional a) => Fractional (SBV a) where
  fromRational  = literal . fromRational
  SBV x / sy@(SBV y) | div0 = ite (sy .== 0) 0 res
                     | True = res
       where res  = SBV (svDivide x y)
             -- Identify those kinds where we have a div-0 equals 0 exception
             div0 = case kindOf sy of
                      KFloat        -> False
                      KDouble       -> False
                      KReal         -> True
                      -- Following two cases should not happen since these types should *not* be instances of Fractional
                      k@KBounded{}  -> error $ "Unexpected Fractional case for: " ++ show k
                      k@KUnbounded  -> error $ "Unexpected Fractional case for: " ++ show k
                      k@KBool       -> error $ "Unexpected Fractional case for: " ++ show k
                      k@KString     -> error $ "Unexpected Fractional case for: " ++ show k
                      k@KChar       -> error $ "Unexpected Fractional case for: " ++ show k
                      k@KList{}     -> error $ "Unexpected Fractional case for: " ++ show k
                      k@KUserSort{} -> error $ "Unexpected Fractional case for: " ++ show k

-- | Define Floating instance on SBV's; only for base types that are already floating; i.e., SFloat and SDouble
-- Note that most of the fields are "undefined" for symbolic values, we add methods as they are supported by SMTLib.
-- Currently, the only symbolicly available function in this class is sqrt.
instance (SymWord a, Fractional a, Floating a) => Floating (SBV a) where
    pi      = literal pi
    exp     = lift1FNS "exp"     exp
    log     = lift1FNS "log"     log
    sqrt    = lift1F   FP_Sqrt   sqrt
    sin     = lift1FNS "sin"     sin
    cos     = lift1FNS "cos"     cos
    tan     = lift1FNS "tan"     tan
    asin    = lift1FNS "asin"    asin
    acos    = lift1FNS "acos"    acos
    atan    = lift1FNS "atan"    atan
    sinh    = lift1FNS "sinh"    sinh
    cosh    = lift1FNS "cosh"    cosh
    tanh    = lift1FNS "tanh"    tanh
    asinh   = lift1FNS "asinh"   asinh
    acosh   = lift1FNS "acosh"   acosh
    atanh   = lift1FNS "atanh"   atanh
    (**)    = lift2FNS "**"      (**)
    logBase = lift2FNS "logBase" logBase

-- | Lift a 1 arg FP-op, using sRNE default
lift1F :: SymWord a => FPOp -> (a -> a) -> SBV a -> SBV a
lift1F w op a
  | Just v <- unliteral a
  = literal $ op v
  | True
  = SBV $ SVal k $ Right $ cache r
  where k    = kindOf a
        r st = do swa  <- sbvToSW st a
                  swm  <- sbvToSW st sRNE
                  newExpr st k (SBVApp (IEEEFP w) [swm, swa])

-- | Lift a float/double unary function, only over constants
lift1FNS :: (SymWord a, Floating a) => String -> (a -> a) -> SBV a -> SBV a
lift1FNS nm f sv
  | Just v <- unliteral sv = literal $ f v
  | True                   = error $ "SBV." ++ nm ++ ": not supported for symbolic values of type " ++ show (kindOf sv)

-- | Lift a float/double binary function, only over constants
lift2FNS :: (SymWord a, Floating a) => String -> (a -> a -> a) -> SBV a -> SBV a -> SBV a
lift2FNS nm f sv1 sv2
  | Just v1 <- unliteral sv1
  , Just v2 <- unliteral sv2 = literal $ f v1 v2
  | True                     = error $ "SBV." ++ nm ++ ": not supported for symbolic values of type " ++ show (kindOf sv1)

-- NB. In the optimizations below, use of -1 is valid as
-- -1 has all bits set to True for both signed and unsigned values
instance (Num a, Bits a, SymWord a) => Bits (SBV a) where
  SBV x .&. SBV y    = SBV (svAnd x y)
  SBV x .|. SBV y    = SBV (svOr x y)
  SBV x `xor` SBV y  = SBV (svXOr x y)
  complement (SBV x) = SBV (svNot x)
  bitSize  x         = intSizeOf x
  bitSizeMaybe x     = Just $ intSizeOf x
  isSigned x         = hasSign x
  bit i              = 1 `shiftL` i
  setBit        x i  = x .|. genLiteral (kindOf x) (bit i :: Integer)
  clearBit      x i  = x .&. genLiteral (kindOf x) (complement (bit i) :: Integer)
  complementBit x i  = x `xor` genLiteral (kindOf x) (bit i :: Integer)
  shiftL  (SBV x) i  = SBV (svShl x i)
  shiftR  (SBV x) i  = SBV (svShr x i)
  rotateL (SBV x) i  = SBV (svRol x i)
  rotateR (SBV x) i  = SBV (svRor x i)
  -- NB. testBit is *not* implementable on non-concrete symbolic words
  x `testBit` i
    | SBV (SVal _ (Left (CW _ (CWInteger n)))) <- x
    = testBit n i
    | True
    = error $ "SBV.testBit: Called on symbolic value: " ++ show x ++ ". Use sTestBit instead."
  -- NB. popCount is *not* implementable on non-concrete symbolic words
  popCount x
    | SBV (SVal _ (Left (CW (KBounded _ w) (CWInteger n)))) <- x
    = popCount (n .&. (bit w - 1))
    | True
    = error $ "SBV.popCount: Called on symbolic value: " ++ show x ++ ". Use sPopCount instead."

-- | Conversion between integral-symbolic values, akin to Haskell's `fromIntegral`
sFromIntegral :: forall a b. (Integral a, HasKind a, Num a, SymWord a, HasKind b, Num b, SymWord b) => SBV a -> SBV b
sFromIntegral x
  | isReal x
  = error "SBV.sFromIntegral: Called on a real value" -- can't really happen due to types, but being overcautious
  | Just v <- unliteral x
  = literal (fromIntegral v)
  | True
  = result
  where result = SBV (SVal kTo (Right (cache y)))
        kFrom  = kindOf x
        kTo    = kindOf (undefined :: b)
        y st   = do xsw <- sbvToSW st x
                    newExpr st kTo (SBVApp (KindCast kFrom kTo) [xsw])

-- | Lift a binary operation thru it's dynamic counterpart. Note that
-- we still want the actual functions here as differ in their type
-- compared to their dynamic counterparts, but the implementations
-- are the same.
liftViaSVal :: (SVal -> SVal -> SVal) -> SBV a -> SBV b -> SBV c
liftViaSVal f (SBV a) (SBV b) = SBV $ f a b

-- | Generalization of 'shiftL', when the shift-amount is symbolic. Since Haskell's
-- 'shiftL' only takes an 'Int' as the shift amount, it cannot be used when we have
-- a symbolic amount to shift with.
sShiftLeft :: (SIntegral a, SIntegral b) => SBV a -> SBV b -> SBV a
sShiftLeft = liftViaSVal svShiftLeft

-- | Generalization of 'shiftR', when the shift-amount is symbolic. Since Haskell's
-- 'shiftR' only takes an 'Int' as the shift amount, it cannot be used when we have
-- a symbolic amount to shift with.
--
-- NB. If the shiftee is signed, then this is an arithmetic shift; otherwise it's logical,
-- following the usual Haskell convention. See 'sSignedShiftArithRight' for a variant
-- that explicitly uses the msb as the sign bit, even for unsigned underlying types.
sShiftRight :: (SIntegral a, SIntegral b) => SBV a -> SBV b -> SBV a
sShiftRight = liftViaSVal svShiftRight

-- | Arithmetic shift-right with a symbolic unsigned shift amount. This is equivalent
-- to 'sShiftRight' when the argument is signed. However, if the argument is unsigned,
-- then it explicitly treats its msb as a sign-bit, and uses it as the bit that
-- gets shifted in. Useful when using the underlying unsigned bit representation to implement
-- custom signed operations. Note that there is no direct Haskell analogue of this function.
sSignedShiftArithRight:: (SFiniteBits a, SIntegral b) => SBV a -> SBV b -> SBV a
sSignedShiftArithRight x i
  | isSigned i = error "sSignedShiftArithRight: shift amount should be unsigned"
  | isSigned x = ssa x i
  | True       = ite (msb x)
                     (complement (ssa (complement x) i))
                     (ssa x i)
  where ssa = liftViaSVal svShiftRight

-- | Generalization of 'rotateL', when the shift-amount is symbolic. Since Haskell's
-- 'rotateL' only takes an 'Int' as the shift amount, it cannot be used when we have
-- a symbolic amount to shift with. The first argument should be a bounded quantity.
sRotateLeft :: (SIntegral a, SIntegral b, SDivisible (SBV b)) => SBV a -> SBV b -> SBV a
sRotateLeft = liftViaSVal svRotateLeft

-- | Generalization of 'rotateR', when the shift-amount is symbolic. Since Haskell's
-- 'rotateR' only takes an 'Int' as the shift amount, it cannot be used when we have
-- a symbolic amount to shift with. The first argument should be a bounded quantity.
sRotateRight :: (SIntegral a, SIntegral b, SDivisible (SBV b)) => SBV a -> SBV b -> SBV a
sRotateRight = liftViaSVal svRotateRight

-- Enum instance. These instances are suitable for use with concrete values,
-- and will be less useful for symbolic values around. Note that `fromEnum` requires
-- a concrete argument for obvious reasons. Other variants (succ, pred, [x..]) etc are similarly
-- limited. While symbolic variants can be defined for many of these, they will just diverge
-- as final sizes cannot be determined statically.
instance (Show a, Bounded a, Integral a, Num a, SymWord a) => Enum (SBV a) where
  succ x
    | v == (maxBound :: a) = error $ "Enum.succ{" ++ showType x ++ "}: tried to take `succ' of maxBound"
    | True                 = fromIntegral $ v + 1
    where v = enumCvt "succ" x
  pred x
    | v == (minBound :: a) = error $ "Enum.pred{" ++ showType x ++ "}: tried to take `pred' of minBound"
    | True                 = fromIntegral $ v - 1
    where v = enumCvt "pred" x
  toEnum x
    | xi < fromIntegral (minBound :: a) || xi > fromIntegral (maxBound :: a)
    = error $ "Enum.toEnum{" ++ showType r ++ "}: " ++ show x ++ " is out-of-bounds " ++ show (minBound :: a, maxBound :: a)
    | True
    = r
    where xi :: Integer
          xi = fromIntegral x
          r  :: SBV a
          r  = fromIntegral x
  fromEnum x
     | r < fromIntegral (minBound :: Int) || r > fromIntegral (maxBound :: Int)
     = error $ "Enum.fromEnum{" ++ showType x ++ "}:  value " ++ show r ++ " is outside of Int's bounds " ++ show (minBound :: Int, maxBound :: Int)
     | True
     = fromIntegral r
    where r :: Integer
          r = enumCvt "fromEnum" x
  enumFrom x = map fromIntegral [xi .. fromIntegral (maxBound :: a)]
     where xi :: Integer
           xi = enumCvt "enumFrom" x
  enumFromThen x y
     | yi >= xi  = map fromIntegral [xi, yi .. fromIntegral (maxBound :: a)]
     | True      = map fromIntegral [xi, yi .. fromIntegral (minBound :: a)]
       where xi, yi :: Integer
             xi = enumCvt "enumFromThen.x" x
             yi = enumCvt "enumFromThen.y" y
  enumFromThenTo x y z = map fromIntegral [xi, yi .. zi]
       where xi, yi, zi :: Integer
             xi = enumCvt "enumFromThenTo.x" x
             yi = enumCvt "enumFromThenTo.y" y
             zi = enumCvt "enumFromThenTo.z" z

-- | Helper function for use in enum operations
enumCvt :: (SymWord a, Integral a, Num b) => String -> SBV a -> b
enumCvt w x = case unliteral x of
                Nothing -> error $ "Enum." ++ w ++ "{" ++ showType x ++ "}: Called on symbolic value " ++ show x
                Just v  -> fromIntegral v

-- | The 'SDivisible' class captures the essence of division.
-- Unfortunately we cannot use Haskell's 'Integral' class since the 'Real'
-- and 'Enum' superclasses are not implementable for symbolic bit-vectors.
-- However, 'quotRem' and 'divMod' both make perfect sense, and the 'SDivisible' class captures
-- this operation. One issue is how division by 0 behaves. The verification
-- technology requires total functions, and there are several design choices
-- here. We follow Isabelle/HOL approach of assigning the value 0 for division
-- by 0. Therefore, we impose the following pair of laws:
--
-- @
--      x `sQuotRem` 0 = (0, x)
--      x `sDivMod`  0 = (0, x)
-- @
--
-- Note that our instances implement this law even when @x@ is @0@ itself.
--
-- NB. 'quot' truncates toward zero, while 'div' truncates toward negative infinity.
--
-- Minimal complete definition: 'sQuotRem', 'sDivMod'
class SDivisible a where
  sQuotRem :: a -> a -> (a, a)
  sDivMod  :: a -> a -> (a, a)
  sQuot    :: a -> a -> a
  sRem     :: a -> a -> a
  sDiv     :: a -> a -> a
  sMod     :: a -> a -> a

  x `sQuot` y = fst $ x `sQuotRem` y
  x `sRem`  y = snd $ x `sQuotRem` y
  x `sDiv`  y = fst $ x `sDivMod`  y
  x `sMod`  y = snd $ x `sDivMod`  y

instance SDivisible Word64 where
  sQuotRem x 0 = (0, x)
  sQuotRem x y = x `quotRem` y
  sDivMod  x 0 = (0, x)
  sDivMod  x y = x `divMod` y

instance SDivisible Int64 where
  sQuotRem x 0 = (0, x)
  sQuotRem x y = x `quotRem` y
  sDivMod  x 0 = (0, x)
  sDivMod  x y = x `divMod` y

instance SDivisible Word32 where
  sQuotRem x 0 = (0, x)
  sQuotRem x y = x `quotRem` y
  sDivMod  x 0 = (0, x)
  sDivMod  x y = x `divMod` y

instance SDivisible Int32 where
  sQuotRem x 0 = (0, x)
  sQuotRem x y = x `quotRem` y
  sDivMod  x 0 = (0, x)
  sDivMod  x y = x `divMod` y

instance SDivisible Word16 where
  sQuotRem x 0 = (0, x)
  sQuotRem x y = x `quotRem` y
  sDivMod  x 0 = (0, x)
  sDivMod  x y = x `divMod` y

instance SDivisible Int16 where
  sQuotRem x 0 = (0, x)
  sQuotRem x y = x `quotRem` y
  sDivMod  x 0 = (0, x)
  sDivMod  x y = x `divMod` y

instance SDivisible Word8 where
  sQuotRem x 0 = (0, x)
  sQuotRem x y = x `quotRem` y
  sDivMod  x 0 = (0, x)
  sDivMod  x y = x `divMod` y

instance SDivisible Int8 where
  sQuotRem x 0 = (0, x)
  sQuotRem x y = x `quotRem` y
  sDivMod  x 0 = (0, x)
  sDivMod  x y = x `divMod` y

instance SDivisible Integer where
  sQuotRem x 0 = (0, x)
  sQuotRem x y = x `quotRem` y
  sDivMod  x 0 = (0, x)
  sDivMod  x y = x `divMod` y

instance SDivisible CW where
  sQuotRem a b
    | CWInteger x <- cwVal a, CWInteger y <- cwVal b
    = let (r1, r2) = sQuotRem x y in (normCW a{ cwVal = CWInteger r1 }, normCW b{ cwVal = CWInteger r2 })
  sQuotRem a b = error $ "SBV.sQuotRem: impossible, unexpected args received: " ++ show (a, b)
  sDivMod a b
    | CWInteger x <- cwVal a, CWInteger y <- cwVal b
    = let (r1, r2) = sDivMod x y in (normCW a { cwVal = CWInteger r1 }, normCW b { cwVal = CWInteger r2 })
  sDivMod a b = error $ "SBV.sDivMod: impossible, unexpected args received: " ++ show (a, b)

instance SDivisible SWord64 where
  sQuotRem = liftQRem
  sDivMod  = liftDMod

instance SDivisible SInt64 where
  sQuotRem = liftQRem
  sDivMod  = liftDMod

instance SDivisible SWord32 where
  sQuotRem = liftQRem
  sDivMod  = liftDMod

instance SDivisible SInt32 where
  sQuotRem = liftQRem
  sDivMod  = liftDMod

instance SDivisible SWord16 where
  sQuotRem = liftQRem
  sDivMod  = liftDMod

instance SDivisible SInt16 where
  sQuotRem = liftQRem
  sDivMod  = liftDMod

instance SDivisible SWord8 where
  sQuotRem = liftQRem
  sDivMod  = liftDMod

instance SDivisible SInt8 where
  sQuotRem = liftQRem
  sDivMod  = liftDMod

-- | Lift 'quotRem' to symbolic words. Division by 0 is defined s.t. @x/0 = 0@; which
-- holds even when @x@ is @0@ itself.
liftQRem :: SymWord a => SBV a -> SBV a -> (SBV a, SBV a)
liftQRem x y
  | isConcreteZero x
  = (x, x)
  | isConcreteOne y
  = (x, z)
{-------------------------------
 - N.B. The seemingly innocuous variant when y == -1 only holds if the type is signed;
 - and also is problematic around the minBound.. So, we refrain from that optimization
  | isConcreteOnes y
  = (-x, z)
--------------------------------}
  | True
  = ite (y .== z) (z, x) (qr x y)
  where qr (SBV (SVal sgnsz (Left a))) (SBV (SVal _ (Left b))) = let (q, r) = sQuotRem a b in (SBV (SVal sgnsz (Left q)), SBV (SVal sgnsz (Left r)))
        qr a@(SBV (SVal sgnsz _))      b                       = (SBV (SVal sgnsz (Right (cache (mk Quot)))), SBV (SVal sgnsz (Right (cache (mk Rem)))))
                where mk o st = do sw1 <- sbvToSW st a
                                   sw2 <- sbvToSW st b
                                   mkSymOp o st sgnsz sw1 sw2
        z = genLiteral (kindOf x) (0::Integer)

-- | Lift 'divMod' to symbolic words. Division by 0 is defined s.t. @x/0 = 0@; which
-- holds even when @x@ is @0@ itself. Essentially, this is conversion from quotRem
-- (truncate to 0) to divMod (truncate towards negative infinity)
liftDMod :: (SymWord a, Num a, SDivisible (SBV a)) => SBV a -> SBV a -> (SBV a, SBV a)
liftDMod x y
  | isConcreteZero x
  = (x, x)
  | isConcreteOne y
  = (x, z)
{-------------------------------
 - N.B. The seemingly innocuous variant when y == -1 only holds if the type is signed;
 - and also is problematic around the minBound.. So, we refrain from that optimization
  | isConcreteOnes y
  = (-x, z)
--------------------------------}
  | True
  = ite (y .== z) (z, x) $ ite (signum r .== negate (signum y)) (q-i, r+y) qr
 where qr@(q, r) = x `sQuotRem` y
       z = genLiteral (kindOf x) (0::Integer)
       i = genLiteral (kindOf x) (1::Integer)

-- SInteger instance for quotRem/divMod are tricky!
-- SMT-Lib only has Euclidean operations, but Haskell
-- uses "truncate to 0" for quotRem, and "truncate to negative infinity" for divMod.
-- So, we cannot just use the above liftings directly.
instance SDivisible SInteger where
  sDivMod = liftDMod
  sQuotRem x y
    | not (isSymbolic x || isSymbolic y)
    = liftQRem x y
    | True
    = ite (y .== 0) (0, x) (qE+i, rE-i*y)
    where (qE, rE) = liftQRem x y   -- for integers, this is euclidean due to SMTLib semantics
          i = ite (x .>= 0 ||| rE .== 0) 0
            $ ite (y .>  0)              1 (-1)

-- Quickcheck interface
instance (SymWord a, Arbitrary a) => Arbitrary (SBV a) where
  arbitrary = literal `fmap` arbitrary

-- |  Symbolic conditionals are modeled by the 'Mergeable' class, describing
-- how to merge the results of an if-then-else call with a symbolic test. SBV
-- provides all basic types as instances of this class, so users only need
-- to declare instances for custom data-types of their programs as needed.
--
-- A 'Mergeable' instance may be automatically derived for a custom data-type
-- with a single constructor where the type of each field is an instance of
-- 'Mergeable', such as a record of symbolic values. Users only need to add
-- 'G.Generic' and 'Mergeable' to the @deriving@ clause for the data-type. See
-- 'Documentation.SBV.Examples.Puzzles.U2Bridge.Status' for an example and an
-- illustration of what the instance would look like if written by hand.
--
-- The function 'select' is a total-indexing function out of a list of choices
-- with a default value, simulating array/list indexing. It's an n-way generalization
-- of the 'ite' function.
--
-- Minimal complete definition: None, if the type is instance of @Generic@. Otherwise
-- 'symbolicMerge'. Note that most types subject to merging are likely to be
-- trivial instances of @Generic@.
class Mergeable a where
   -- | Merge two values based on the condition. The first argument states
   -- whether we force the then-and-else branches before the merging, at the
   -- word level. This is an efficiency concern; one that we'd rather not
   -- make but unfortunately necessary for getting symbolic simulation
   -- working efficiently.
   symbolicMerge :: Bool -> SBool -> a -> a -> a
   -- | Total indexing operation. @select xs default index@ is intuitively
   -- the same as @xs !! index@, except it evaluates to @default@ if @index@
   -- underflows/overflows.
   select :: (SymWord b, Num b) => [a] -> a -> SBV b -> a
   -- NB. Earlier implementation of select used the binary-search trick
   -- on the index to chop down the search space. While that is a good trick
   -- in general, it doesn't work for SBV since we do not have any notion of
   -- "concrete" subwords: If an index is symbolic, then all its bits are
   -- symbolic as well. So, the binary search only pays off only if the indexed
   -- list is really humongous, which is not very common in general. (Also,
   -- for the case when the list is bit-vectors, we use SMT tables anyhow.)
   select xs err ind
    | isReal   ind = bad "real"
    | isFloat  ind = bad "float"
    | isDouble ind = bad "double"
    | hasSign  ind = ite (ind .< 0) err (walk xs ind err)
    | True         =                     walk xs ind err
    where bad w = error $ "SBV.select: unsupported " ++ w ++ " valued select/index expression"
          walk []     _ acc = acc
          walk (e:es) i acc = walk es (i-1) (ite (i .== 0) e acc)

   -- Default implementation for 'symbolicMerge' if the type is 'Generic'
   default symbolicMerge :: (G.Generic a, GMergeable (G.Rep a)) => Bool -> SBool -> a -> a -> a
   symbolicMerge = symbolicMergeDefault

-- | If-then-else. This is by definition 'symbolicMerge' with both
-- branches forced. This is typically the desired behavior, but also
-- see 'iteLazy' should you need more laziness.
ite :: Mergeable a => SBool -> a -> a -> a
ite t a b
  | Just r <- unliteral t = if r then a else b
  | True                  = symbolicMerge True t a b

-- | A Lazy version of ite, which does not force its arguments. This might
-- cause issues for symbolic simulation with large thunks around, so use with
-- care.
iteLazy :: Mergeable a => SBool -> a -> a -> a
iteLazy t a b
  | Just r <- unliteral t = if r then a else b
  | True                  = symbolicMerge False t a b

-- | Symbolic assert. Check that the given boolean condition is always true in the given path. The
-- optional first argument can be used to provide call-stack info via GHC's location facilities.
sAssert :: Maybe CallStack -> String -> SBool -> SBV a -> SBV a
sAssert cs msg cond x
   | Just mustHold <- unliteral cond
   = if mustHold
     then x
     else error $ show $ SafeResult ((locInfo . getCallStack) `fmap` cs, msg, Satisfiable defaultSMTCfg (SMTModel [] []))
   | True
   = SBV $ SVal k $ Right $ cache r
  where k     = kindOf x
        r st  = do xsw <- sbvToSW st x
                   let pc = getPathCondition st
                       -- We're checking if there are any cases where the path-condition holds, but not the condition
                       -- Any violations of this, should be signaled, i.e., whenever the following formula is satisfiable
                       mustNeverHappen = pc &&& bnot cond
                   cnd <- sbvToSW st mustNeverHappen
                   addAssertion st cs msg cnd
                   return xsw

        locInfo ps = intercalate ",\n " (map loc ps)
          where loc (f, sl) = concat [srcLocFile sl, ":", show (srcLocStartLine sl), ":", show (srcLocStartCol sl), ":", f]

-- | Merge two symbolic values, at kind @k@, possibly @force@'ing the branches to make
-- sure they do not evaluate to the same result. This should only be used for internal purposes;
-- as default definitions provided should suffice in many cases. (i.e., End users should
-- only need to define 'symbolicMerge' when needed; which should be rare to start with.)
symbolicMergeWithKind :: Kind -> Bool -> SBool -> SBV a -> SBV a -> SBV a
symbolicMergeWithKind k force (SBV t) (SBV a) (SBV b) = SBV (svSymbolicMerge k force t a b)

instance SymWord a => Mergeable (SBV a) where
    symbolicMerge force t x y
    -- Carefully use the kindOf instance to avoid strictness issues.
       | force = symbolicMergeWithKind (kindOf x)                True  t x y
       | True  = symbolicMergeWithKind (kindOf (undefined :: a)) False t x y
    -- Custom version of select that translates to SMT-Lib tables at the base type of words
    select xs err ind
      | SBV (SVal _ (Left c)) <- ind = case cwVal c of
                                         CWInteger i -> if i < 0 || i >= genericLength xs
                                                        then err
                                                        else xs `genericIndex` i
                                         _           -> error $ "SBV.select: unsupported " ++ show (kindOf ind) ++ " valued select/index expression"
    select xsOrig err ind = xs `seq` SBV (SVal kElt (Right (cache r)))
      where kInd = kindOf ind
            kElt = kindOf err
            -- Based on the index size, we need to limit the elements. For instance if the index is 8 bits, but there
            -- are 257 elements, that last element will never be used and we can chop it of..
            xs   = case kindOf ind of
                     KBounded False i -> genericTake ((2::Integer) ^ (fromIntegral i     :: Integer)) xsOrig
                     KBounded True  i -> genericTake ((2::Integer) ^ (fromIntegral (i-1) :: Integer)) xsOrig
                     KUnbounded       -> xsOrig
                     _                -> error $ "SBV.select: unsupported " ++ show (kindOf ind) ++ " valued select/index expression"
            r st  = do sws <- mapM (sbvToSW st) xs
                       swe <- sbvToSW st err
                       if all (== swe) sws  -- off-chance that all elts are the same. Note that this also correctly covers the case when list is empty.
                          then return swe
                          else do idx <- getTableIndex st kInd kElt sws
                                  swi <- sbvToSW st ind
                                  let len = length xs
                                  -- NB. No need to worry here that the index might be < 0; as the SMTLib translation takes care of that automatically
                                  newExpr st kElt (SBVApp (LkUp (idx, kInd, kElt, len) swi swe) [])

-- Unit
instance Mergeable () where
   symbolicMerge _ _ _ _ = ()
   select _ _ _ = ()

-- Mergeable instances for List/Maybe/Either/Array are useful, but can
-- throw exceptions if there is no structural matching of the results
-- It's a question whether we should really keep them..

-- Lists
instance Mergeable a => Mergeable [a] where
  symbolicMerge f t xs ys
    | lxs == lys = zipWith (symbolicMerge f t) xs ys
    | True       = error $ "SBV.Mergeable.List: No least-upper-bound for lists of differing size " ++ show (lxs, lys)
    where (lxs, lys) = (length xs, length ys)

-- ZipList
instance Mergeable a => Mergeable (ZipList a) where
  symbolicMerge force test (ZipList xs) (ZipList ys)
    = ZipList (symbolicMerge force test xs ys)

-- Maybe
instance Mergeable a => Mergeable (Maybe a) where
  symbolicMerge _ _ Nothing  Nothing  = Nothing
  symbolicMerge f t (Just a) (Just b) = Just $ symbolicMerge f t a b
  symbolicMerge _ _ a b = error $ "SBV.Mergeable.Maybe: No least-upper-bound for " ++ show (k a, k b)
      where k Nothing = "Nothing"
            k _       = "Just"

-- Either
instance (Mergeable a, Mergeable b) => Mergeable (Either a b) where
  symbolicMerge f t (Left a)  (Left b)  = Left  $ symbolicMerge f t a b
  symbolicMerge f t (Right a) (Right b) = Right $ symbolicMerge f t a b
  symbolicMerge _ _ a b = error $ "SBV.Mergeable.Either: No least-upper-bound for " ++ show (k a, k b)
     where k (Left _)  = "Left"
           k (Right _) = "Right"

-- Arrays
instance (Ix a, Mergeable b) => Mergeable (Array a b) where
  symbolicMerge f t a b
    | ba == bb = listArray ba (zipWith (symbolicMerge f t) (elems a) (elems b))
    | True     = error $ "SBV.Mergeable.Array: No least-upper-bound for rangeSizes" ++ show (k ba, k bb)
    where [ba, bb] = map bounds [a, b]
          k = rangeSize

-- Functions
instance Mergeable b => Mergeable (a -> b) where
  symbolicMerge f t g h x = symbolicMerge f t (g x) (h x)
  {- Following definition, while correct, is utterly inefficient. Since the
     application is delayed, this hangs on to the inner list and all the
     impending merges, even when ind is concrete. Thus, it's much better to
     simply use the default definition for the function case.
  -}
  -- select xs err ind = \x -> select (map ($ x) xs) (err x) ind

-- 2-Tuple
instance (Mergeable a, Mergeable b) => Mergeable (a, b) where
  symbolicMerge f t (i0, i1) (j0, j1) = (i i0 j0, i i1 j1)
    where i a b = symbolicMerge f t a b
  select xs (err1, err2) ind = (select as err1 ind, select bs err2 ind)
    where (as, bs) = unzip xs

-- 3-Tuple
instance (Mergeable a, Mergeable b, Mergeable c) => Mergeable (a, b, c) where
  symbolicMerge f t (i0, i1, i2) (j0, j1, j2) = (i i0 j0, i i1 j1, i i2 j2)
    where i a b = symbolicMerge f t a b
  select xs (err1, err2, err3) ind = (select as err1 ind, select bs err2 ind, select cs err3 ind)
    where (as, bs, cs) = unzip3 xs

-- 4-Tuple
instance (Mergeable a, Mergeable b, Mergeable c, Mergeable d) => Mergeable (a, b, c, d) where
  symbolicMerge f t (i0, i1, i2, i3) (j0, j1, j2, j3) = (i i0 j0, i i1 j1, i i2 j2, i i3 j3)
    where i a b = symbolicMerge f t a b
  select xs (err1, err2, err3, err4) ind = (select as err1 ind, select bs err2 ind, select cs err3 ind, select ds err4 ind)
    where (as, bs, cs, ds) = unzip4 xs

-- 5-Tuple
instance (Mergeable a, Mergeable b, Mergeable c, Mergeable d, Mergeable e) => Mergeable (a, b, c, d, e) where
  symbolicMerge f t (i0, i1, i2, i3, i4) (j0, j1, j2, j3, j4) = (i i0 j0, i i1 j1, i i2 j2, i i3 j3, i i4 j4)
    where i a b = symbolicMerge f t a b
  select xs (err1, err2, err3, err4, err5) ind = (select as err1 ind, select bs err2 ind, select cs err3 ind, select ds err4 ind, select es err5 ind)
    where (as, bs, cs, ds, es) = unzip5 xs

-- 6-Tuple
instance (Mergeable a, Mergeable b, Mergeable c, Mergeable d, Mergeable e, Mergeable f) => Mergeable (a, b, c, d, e, f) where
  symbolicMerge f t (i0, i1, i2, i3, i4, i5) (j0, j1, j2, j3, j4, j5) = (i i0 j0, i i1 j1, i i2 j2, i i3 j3, i i4 j4, i i5 j5)
    where i a b = symbolicMerge f t a b
  select xs (err1, err2, err3, err4, err5, err6) ind = (select as err1 ind, select bs err2 ind, select cs err3 ind, select ds err4 ind, select es err5 ind, select fs err6 ind)
    where (as, bs, cs, ds, es, fs) = unzip6 xs

-- 7-Tuple
instance (Mergeable a, Mergeable b, Mergeable c, Mergeable d, Mergeable e, Mergeable f, Mergeable g) => Mergeable (a, b, c, d, e, f, g) where
  symbolicMerge f t (i0, i1, i2, i3, i4, i5, i6) (j0, j1, j2, j3, j4, j5, j6) = (i i0 j0, i i1 j1, i i2 j2, i i3 j3, i i4 j4, i i5 j5, i i6 j6)
    where i a b = symbolicMerge f t a b
  select xs (err1, err2, err3, err4, err5, err6, err7) ind = (select as err1 ind, select bs err2 ind, select cs err3 ind, select ds err4 ind, select es err5 ind, select fs err6 ind, select gs err7 ind)
    where (as, bs, cs, ds, es, fs, gs) = unzip7 xs

-- Arbitrary product types, using GHC.Generics
--
-- NB: Because of the way GHC.Generics works, the implementation of
-- symbolicMerge' is recursive. The derived instance for @data T a = T a a a a@
-- resembles that for (a, (a, (a, a))), not the flat 4-tuple (a, a, a, a). This
-- difference should have no effect in practice. Note also that, unlike the
-- hand-rolled tuple instances, the generic instance does not provide a custom
-- 'select' implementation, and so does not benefit from the SMT-table
-- implementation in the 'SBV a' instance.

-- | Not exported. Symbolic merge using the generic representation provided by
-- 'G.Generics'.
symbolicMergeDefault :: (G.Generic a, GMergeable (G.Rep a)) => Bool -> SBool -> a -> a -> a
symbolicMergeDefault force t x y = G.to $ symbolicMerge' force t (G.from x) (G.from y)

-- | Not exported. Used only in 'symbolicMergeDefault'. Instances are provided for
-- the generic representations of product types where each element is Mergeable.
class GMergeable f where
  symbolicMerge' :: Bool -> SBool -> f a -> f a -> f a

instance GMergeable U1 where
  symbolicMerge' _ _ _ _ = U1

instance (Mergeable c) => GMergeable (K1 i c) where
  symbolicMerge' force t (K1 x) (K1 y) = K1 $ symbolicMerge force t x y

instance (GMergeable f) => GMergeable (M1 i c f) where
  symbolicMerge' force t (M1 x) (M1 y) = M1 $ symbolicMerge' force t x y

instance (GMergeable f, GMergeable g) => GMergeable (f :*: g) where
  symbolicMerge' force t (x1 :*: y1) (x2 :*: y2) = symbolicMerge' force t x1 x2 :*: symbolicMerge' force t y1 y2

-- Bounded instances
instance (SymWord a, Bounded a) => Bounded (SBV a) where
  minBound = literal minBound
  maxBound = literal maxBound

-- Arrays

-- SArrays are both "EqSymbolic" and "Mergeable"
instance EqSymbolic (SArray a b) where
  SArray a .== SArray b = SBV (a `eqSArr` b)

-- When merging arrays; we'll ignore the force argument. This is arguably
-- the right thing to do as we've too many things and likely we want to keep it efficient.
instance SymWord b => Mergeable (SArray a b) where
  symbolicMerge _ = mergeArrays

-- When merging arrays; we'll ignore the force argument. This is arguably
-- the right thing to do as we've too many things and likely we want to keep it efficient.
instance SymWord b => Mergeable (SFunArray a b) where
  symbolicMerge _ = mergeArrays

-- | Uninterpreted constants and functions. An uninterpreted constant is
-- a value that is indexed by its name. The only property the prover assumes
-- about these values are that they are equivalent to themselves; i.e., (for
-- functions) they return the same results when applied to same arguments.
-- We support uninterpreted-functions as a general means of black-box'ing
-- operations that are /irrelevant/ for the purposes of the proof; i.e., when
-- the proofs can be performed without any knowledge about the function itself.
--
-- Minimal complete definition: 'sbvUninterpret'. However, most instances in
-- practice are already provided by SBV, so end-users should not need to define their
-- own instances.
class Uninterpreted a where
  -- | Uninterpret a value, receiving an object that can be used instead. Use this version
  -- when you do not need to add an axiom about this value.
  uninterpret :: String -> a
  -- | Uninterpret a value, only for the purposes of code-generation. For execution
  -- and verification the value is used as is. For code-generation, the alternate
  -- definition is used. This is useful when we want to take advantage of native
  -- libraries on the target languages.
  cgUninterpret :: String -> [String] -> a -> a
  -- | Most generalized form of uninterpretation, this function should not be needed
  -- by end-user-code, but is rather useful for the library development.
  sbvUninterpret :: Maybe ([String], a) -> String -> a

  {-# MINIMAL sbvUninterpret #-}

  -- defaults:
  uninterpret             = sbvUninterpret Nothing
  cgUninterpret nm code v = sbvUninterpret (Just (code, v)) nm

-- Plain constants
instance HasKind a => Uninterpreted (SBV a) where
  sbvUninterpret mbCgData nm
     | Just (_, v) <- mbCgData = v
     | True                    = SBV $ SVal ka $ Right $ cache result
    where ka = kindOf (undefined :: a)
          result st = do isSMT <- inSMTMode st
                         case (isSMT, mbCgData) of
                           (True, Just (_, v)) -> sbvToSW st v
                           _                   -> do newUninterpreted st nm (SBVType [ka]) (fst `fmap` mbCgData)
                                                     newExpr st ka $ SBVApp (Uninterpreted nm) []

-- Functions of one argument
instance (SymWord b, HasKind a) => Uninterpreted (SBV b -> SBV a) where
  sbvUninterpret mbCgData nm = f
    where f arg0
           | Just (_, v) <- mbCgData, isConcrete arg0
           = v arg0
           | True
           = SBV $ SVal ka $ Right $ cache result
           where ka = kindOf (undefined :: a)
                 kb = kindOf (undefined :: b)
                 result st = do isSMT <- inSMTMode st
                                case (isSMT, mbCgData) of
                                  (True, Just (_, v)) -> sbvToSW st (v arg0)
                                  _                   -> do newUninterpreted st nm (SBVType [kb, ka]) (fst `fmap` mbCgData)
                                                            sw0 <- sbvToSW st arg0
                                                            mapM_ forceSWArg [sw0]
                                                            newExpr st ka $ SBVApp (Uninterpreted nm) [sw0]

-- Functions of two arguments
instance (SymWord c, SymWord b, HasKind a) => Uninterpreted (SBV c -> SBV b -> SBV a) where
  sbvUninterpret mbCgData nm = f
    where f arg0 arg1
           | Just (_, v) <- mbCgData, isConcrete arg0, isConcrete arg1
           = v arg0 arg1
           | True
           = SBV $ SVal ka $ Right $ cache result
           where ka = kindOf (undefined :: a)
                 kb = kindOf (undefined :: b)
                 kc = kindOf (undefined :: c)
                 result st = do isSMT <- inSMTMode st
                                case (isSMT, mbCgData) of
                                  (True, Just (_, v)) -> sbvToSW st (v arg0 arg1)
                                  _                   -> do newUninterpreted st nm (SBVType [kc, kb, ka]) (fst `fmap` mbCgData)
                                                            sw0 <- sbvToSW st arg0
                                                            sw1 <- sbvToSW st arg1
                                                            mapM_ forceSWArg [sw0, sw1]
                                                            newExpr st ka $ SBVApp (Uninterpreted nm) [sw0, sw1]

-- Functions of three arguments
instance (SymWord d, SymWord c, SymWord b, HasKind a) => Uninterpreted (SBV d -> SBV c -> SBV b -> SBV a) where
  sbvUninterpret mbCgData nm = f
    where f arg0 arg1 arg2
           | Just (_, v) <- mbCgData, isConcrete arg0, isConcrete arg1, isConcrete arg2
           = v arg0 arg1 arg2
           | True
           = SBV $ SVal ka $ Right $ cache result
           where ka = kindOf (undefined :: a)
                 kb = kindOf (undefined :: b)
                 kc = kindOf (undefined :: c)
                 kd = kindOf (undefined :: d)
                 result st = do isSMT <- inSMTMode st
                                case (isSMT, mbCgData) of
                                  (True, Just (_, v)) -> sbvToSW st (v arg0 arg1 arg2)
                                  _                   -> do newUninterpreted st nm (SBVType [kd, kc, kb, ka]) (fst `fmap` mbCgData)
                                                            sw0 <- sbvToSW st arg0
                                                            sw1 <- sbvToSW st arg1
                                                            sw2 <- sbvToSW st arg2
                                                            mapM_ forceSWArg [sw0, sw1, sw2]
                                                            newExpr st ka $ SBVApp (Uninterpreted nm) [sw0, sw1, sw2]

-- Functions of four arguments
instance (SymWord e, SymWord d, SymWord c, SymWord b, HasKind a) => Uninterpreted (SBV e -> SBV d -> SBV c -> SBV b -> SBV a) where
  sbvUninterpret mbCgData nm = f
    where f arg0 arg1 arg2 arg3
           | Just (_, v) <- mbCgData, isConcrete arg0, isConcrete arg1, isConcrete arg2, isConcrete arg3
           = v arg0 arg1 arg2 arg3
           | True
           = SBV $ SVal ka $ Right $ cache result
           where ka = kindOf (undefined :: a)
                 kb = kindOf (undefined :: b)
                 kc = kindOf (undefined :: c)
                 kd = kindOf (undefined :: d)
                 ke = kindOf (undefined :: e)
                 result st = do isSMT <- inSMTMode st
                                case (isSMT, mbCgData) of
                                  (True, Just (_, v)) -> sbvToSW st (v arg0 arg1 arg2 arg3)
                                  _                   -> do newUninterpreted st nm (SBVType [ke, kd, kc, kb, ka]) (fst `fmap` mbCgData)
                                                            sw0 <- sbvToSW st arg0
                                                            sw1 <- sbvToSW st arg1
                                                            sw2 <- sbvToSW st arg2
                                                            sw3 <- sbvToSW st arg3
                                                            mapM_ forceSWArg [sw0, sw1, sw2, sw3]
                                                            newExpr st ka $ SBVApp (Uninterpreted nm) [sw0, sw1, sw2, sw3]

-- Functions of five arguments
instance (SymWord f, SymWord e, SymWord d, SymWord c, SymWord b, HasKind a) => Uninterpreted (SBV f -> SBV e -> SBV d -> SBV c -> SBV b -> SBV a) where
  sbvUninterpret mbCgData nm = f
    where f arg0 arg1 arg2 arg3 arg4
           | Just (_, v) <- mbCgData, isConcrete arg0, isConcrete arg1, isConcrete arg2, isConcrete arg3, isConcrete arg4
           = v arg0 arg1 arg2 arg3 arg4
           | True
           = SBV $ SVal ka $ Right $ cache result
           where ka = kindOf (undefined :: a)
                 kb = kindOf (undefined :: b)
                 kc = kindOf (undefined :: c)
                 kd = kindOf (undefined :: d)
                 ke = kindOf (undefined :: e)
                 kf = kindOf (undefined :: f)
                 result st = do isSMT <- inSMTMode st
                                case (isSMT, mbCgData) of
                                  (True, Just (_, v)) -> sbvToSW st (v arg0 arg1 arg2 arg3 arg4)
                                  _                   -> do newUninterpreted st nm (SBVType [kf, ke, kd, kc, kb, ka]) (fst `fmap` mbCgData)
                                                            sw0 <- sbvToSW st arg0
                                                            sw1 <- sbvToSW st arg1
                                                            sw2 <- sbvToSW st arg2
                                                            sw3 <- sbvToSW st arg3
                                                            sw4 <- sbvToSW st arg4
                                                            mapM_ forceSWArg [sw0, sw1, sw2, sw3, sw4]
                                                            newExpr st ka $ SBVApp (Uninterpreted nm) [sw0, sw1, sw2, sw3, sw4]

-- Functions of six arguments
instance (SymWord g, SymWord f, SymWord e, SymWord d, SymWord c, SymWord b, HasKind a) => Uninterpreted (SBV g -> SBV f -> SBV e -> SBV d -> SBV c -> SBV b -> SBV a) where
  sbvUninterpret mbCgData nm = f
    where f arg0 arg1 arg2 arg3 arg4 arg5
           | Just (_, v) <- mbCgData, isConcrete arg0, isConcrete arg1, isConcrete arg2, isConcrete arg3, isConcrete arg4, isConcrete arg5
           = v arg0 arg1 arg2 arg3 arg4 arg5
           | True
           = SBV $ SVal ka $ Right $ cache result
           where ka = kindOf (undefined :: a)
                 kb = kindOf (undefined :: b)
                 kc = kindOf (undefined :: c)
                 kd = kindOf (undefined :: d)
                 ke = kindOf (undefined :: e)
                 kf = kindOf (undefined :: f)
                 kg = kindOf (undefined :: g)
                 result st = do isSMT <- inSMTMode st
                                case (isSMT, mbCgData) of
                                  (True, Just (_, v)) -> sbvToSW st (v arg0 arg1 arg2 arg3 arg4 arg5)
                                  _                   -> do newUninterpreted st nm (SBVType [kg, kf, ke, kd, kc, kb, ka]) (fst `fmap` mbCgData)
                                                            sw0 <- sbvToSW st arg0
                                                            sw1 <- sbvToSW st arg1
                                                            sw2 <- sbvToSW st arg2
                                                            sw3 <- sbvToSW st arg3
                                                            sw4 <- sbvToSW st arg4
                                                            sw5 <- sbvToSW st arg5
                                                            mapM_ forceSWArg [sw0, sw1, sw2, sw3, sw4, sw5]
                                                            newExpr st ka $ SBVApp (Uninterpreted nm) [sw0, sw1, sw2, sw3, sw4, sw5]

-- Functions of seven arguments
instance (SymWord h, SymWord g, SymWord f, SymWord e, SymWord d, SymWord c, SymWord b, HasKind a)
            => Uninterpreted (SBV h -> SBV g -> SBV f -> SBV e -> SBV d -> SBV c -> SBV b -> SBV a) where
  sbvUninterpret mbCgData nm = f
    where f arg0 arg1 arg2 arg3 arg4 arg5 arg6
           | Just (_, v) <- mbCgData, isConcrete arg0, isConcrete arg1, isConcrete arg2, isConcrete arg3, isConcrete arg4, isConcrete arg5, isConcrete arg6
           = v arg0 arg1 arg2 arg3 arg4 arg5 arg6
           | True
           = SBV $ SVal ka $ Right $ cache result
           where ka = kindOf (undefined :: a)
                 kb = kindOf (undefined :: b)
                 kc = kindOf (undefined :: c)
                 kd = kindOf (undefined :: d)
                 ke = kindOf (undefined :: e)
                 kf = kindOf (undefined :: f)
                 kg = kindOf (undefined :: g)
                 kh = kindOf (undefined :: h)
                 result st = do isSMT <- inSMTMode st
                                case (isSMT, mbCgData) of
                                  (True, Just (_, v)) -> sbvToSW st (v arg0 arg1 arg2 arg3 arg4 arg5 arg6)
                                  _                   -> do newUninterpreted st nm (SBVType [kh, kg, kf, ke, kd, kc, kb, ka]) (fst `fmap` mbCgData)
                                                            sw0 <- sbvToSW st arg0
                                                            sw1 <- sbvToSW st arg1
                                                            sw2 <- sbvToSW st arg2
                                                            sw3 <- sbvToSW st arg3
                                                            sw4 <- sbvToSW st arg4
                                                            sw5 <- sbvToSW st arg5
                                                            sw6 <- sbvToSW st arg6
                                                            mapM_ forceSWArg [sw0, sw1, sw2, sw3, sw4, sw5, sw6]
                                                            newExpr st ka $ SBVApp (Uninterpreted nm) [sw0, sw1, sw2, sw3, sw4, sw5, sw6]

-- Uncurried functions of two arguments
instance (SymWord c, SymWord b, HasKind a) => Uninterpreted ((SBV c, SBV b) -> SBV a) where
  sbvUninterpret mbCgData nm = let f = sbvUninterpret (uc2 `fmap` mbCgData) nm in uncurry f
    where uc2 (cs, fn) = (cs, curry fn)

-- Uncurried functions of three arguments
instance (SymWord d, SymWord c, SymWord b, HasKind a) => Uninterpreted ((SBV d, SBV c, SBV b) -> SBV a) where
  sbvUninterpret mbCgData nm = let f = sbvUninterpret (uc3 `fmap` mbCgData) nm in \(arg0, arg1, arg2) -> f arg0 arg1 arg2
    where uc3 (cs, fn) = (cs, \a b c -> fn (a, b, c))

-- Uncurried functions of four arguments
instance (SymWord e, SymWord d, SymWord c, SymWord b, HasKind a)
            => Uninterpreted ((SBV e, SBV d, SBV c, SBV b) -> SBV a) where
  sbvUninterpret mbCgData nm = let f = sbvUninterpret (uc4 `fmap` mbCgData) nm in \(arg0, arg1, arg2, arg3) -> f arg0 arg1 arg2 arg3
    where uc4 (cs, fn) = (cs, \a b c d -> fn (a, b, c, d))

-- Uncurried functions of five arguments
instance (SymWord f, SymWord e, SymWord d, SymWord c, SymWord b, HasKind a)
            => Uninterpreted ((SBV f, SBV e, SBV d, SBV c, SBV b) -> SBV a) where
  sbvUninterpret mbCgData nm = let f = sbvUninterpret (uc5 `fmap` mbCgData) nm in \(arg0, arg1, arg2, arg3, arg4) -> f arg0 arg1 arg2 arg3 arg4
    where uc5 (cs, fn) = (cs, \a b c d e -> fn (a, b, c, d, e))

-- Uncurried functions of six arguments
instance (SymWord g, SymWord f, SymWord e, SymWord d, SymWord c, SymWord b, HasKind a)
            => Uninterpreted ((SBV g, SBV f, SBV e, SBV d, SBV c, SBV b) -> SBV a) where
  sbvUninterpret mbCgData nm = let f = sbvUninterpret (uc6 `fmap` mbCgData) nm in \(arg0, arg1, arg2, arg3, arg4, arg5) -> f arg0 arg1 arg2 arg3 arg4 arg5
    where uc6 (cs, fn) = (cs, \a b c d e f -> fn (a, b, c, d, e, f))

-- Uncurried functions of seven arguments
instance (SymWord h, SymWord g, SymWord f, SymWord e, SymWord d, SymWord c, SymWord b, HasKind a)
            => Uninterpreted ((SBV h, SBV g, SBV f, SBV e, SBV d, SBV c, SBV b) -> SBV a) where
  sbvUninterpret mbCgData nm = let f = sbvUninterpret (uc7 `fmap` mbCgData) nm in \(arg0, arg1, arg2, arg3, arg4, arg5, arg6) -> f arg0 arg1 arg2 arg3 arg4 arg5 arg6
    where uc7 (cs, fn) = (cs, \a b c d e f g -> fn (a, b, c, d, e, f, g))

-- | Symbolic computations provide a context for writing symbolic programs.
instance SolverContext Symbolic where
   constrain                   (SBV c) = imposeConstraint False []               c
   softConstrain               (SBV c) = imposeConstraint True  []               c
   namedConstraint        nm   (SBV c) = imposeConstraint False [(":named", nm)] c
   constrainWithAttribute atts (SBV c) = imposeConstraint False atts             c

   setOption o = addNewSMTOption  o

-- | Introduce a soft assertion, with an optional penalty
assertWithPenalty :: String -> SBool -> Penalty -> Symbolic ()
assertWithPenalty nm o p = addSValOptGoal $ unSBV `fmap` AssertWithPenalty nm o p

-- | Class of metrics we can optimize for. Currently,
-- bounded signed/unsigned bit-vectors, unbounded integers,
-- and algebraic reals can be optimized. (But not, say, SFloat, SDouble, or SBool.)
-- Minimal complete definition: minimize/maximize.
--
-- A good reference on these features is given in the following paper:
-- <http://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/nbjorner-scss2014.pdf>.
class Metric a where
  -- | Minimize a named metric
  minimize :: String -> a -> Symbolic ()

  -- | Maximize a named metric
  maximize :: String -> a -> Symbolic ()

instance Metric SWord8   where minimize nm o = addSValOptGoal (unSBV `fmap` Minimize nm o); maximize nm o = addSValOptGoal (unSBV `fmap` Maximize nm o)
instance Metric SWord16  where minimize nm o = addSValOptGoal (unSBV `fmap` Minimize nm o); maximize nm o = addSValOptGoal (unSBV `fmap` Maximize nm o)
instance Metric SWord32  where minimize nm o = addSValOptGoal (unSBV `fmap` Minimize nm o); maximize nm o = addSValOptGoal (unSBV `fmap` Maximize nm o)
instance Metric SWord64  where minimize nm o = addSValOptGoal (unSBV `fmap` Minimize nm o); maximize nm o = addSValOptGoal (unSBV `fmap` Maximize nm o)
instance Metric SInt8    where minimize nm o = addSValOptGoal (unSBV `fmap` Minimize nm o); maximize nm o = addSValOptGoal (unSBV `fmap` Maximize nm o)
instance Metric SInt16   where minimize nm o = addSValOptGoal (unSBV `fmap` Minimize nm o); maximize nm o = addSValOptGoal (unSBV `fmap` Maximize nm o)
instance Metric SInt32   where minimize nm o = addSValOptGoal (unSBV `fmap` Minimize nm o); maximize nm o = addSValOptGoal (unSBV `fmap` Maximize nm o)
instance Metric SInt64   where minimize nm o = addSValOptGoal (unSBV `fmap` Minimize nm o); maximize nm o = addSValOptGoal (unSBV `fmap` Maximize nm o)
instance Metric SInteger where minimize nm o = addSValOptGoal (unSBV `fmap` Minimize nm o); maximize nm o = addSValOptGoal (unSBV `fmap` Maximize nm o)
instance Metric SReal    where minimize nm o = addSValOptGoal (unSBV `fmap` Minimize nm o); maximize nm o = addSValOptGoal (unSBV `fmap` Maximize nm o)

-- Quickcheck interface on symbolic-booleans..
instance Testable SBool where
  property (SBV (SVal _ (Left b))) = property (cwToBool b)
  property _                       = error "Quick-check: Constant folding produced a symbolic value! Perhaps used a non-reducible expression? Please report!"

instance Testable (Symbolic SBool) where
   property prop = QC.monadicIO $ do (cond, r, modelVals) <- QC.run test
                                     QC.pre cond
                                     unless (r || null modelVals) $ QC.monitor (QC.counterexample (complain modelVals))
                                     QC.assert r
     where test = do (r, Result{resTraces=tvals, resObservables=ovals, resConsts=cs, resConstraints=cstrs, resUIConsts=unints}) <- runSymbolic Concrete prop

                     let cval = fromMaybe (error "Cannot quick-check in the presence of uninterpeted constants!") . (`lookup` cs)
                         cond = and [cwToBool (cval v) | (False, _, v) <- cstrs] -- Only pick-up "hard" constraints, as indicated by False in the fist component

                         getObservable (nm, v) = case v `lookup` cs of
                                                   Just cw -> (nm, cw)
                                                   Nothing -> error $ "Quick-check: Observable " ++ nm ++ " did not reduce to a constant!"

                     case map fst unints of
                       [] -> case unliteral r of
                               Nothing -> noQC [show r]
                               Just b  -> return (cond, b, tvals ++ map getObservable ovals)
                       us -> noQC us

           complain qcInfo = showModel defaultSMTCfg (SMTModel [] qcInfo)

           noQC us         = error $ "Cannot quick-check in the presence of uninterpreted constants: " ++ intercalate ", " us

-- | Quick check an SBV property. Note that a regular 'quickCheck' call will work just as
-- well. Use this variant if you want to receive the boolean result.
sbvQuickCheck :: Symbolic SBool -> IO Bool
sbvQuickCheck prop = QC.isSuccess `fmap` QC.quickCheckResult prop

-- Quickcheck interface on dynamically-typed values. A run-time check
-- ensures that the value has boolean type.
instance Testable (Symbolic SVal) where
  property m = property $ do s <- m
                             when (kindOf s /= KBool) $ error "Cannot quickcheck non-boolean value"
                             return (SBV s :: SBool)

-- | Explicit sharing combinator. The SBV library has internal caching/hash-consing mechanisms
-- built in, based on Andy Gill's type-safe obervable sharing technique (see: <http://ku-fpg.github.io/files/Gill-09-TypeSafeReification.pdf>).
-- However, there might be times where being explicit on the sharing can help, especially in experimental code. The 'slet' combinator
-- ensures that its first argument is computed once and passed on to its continuation, explicitly indicating the intent of sharing. Most
-- use cases of the SBV library should simply use Haskell's @let@ construct for this purpose.
slet :: forall a b. (HasKind a, HasKind b) => SBV a -> (SBV a -> SBV b) -> SBV b
slet x f = SBV $ SVal k $ Right $ cache r
    where k    = kindOf (undefined :: b)
          r st = do xsw <- sbvToSW st x
                    let xsbv = SBV $ SVal (kindOf x) (Right (cache (const (return xsw))))
                        res  = f xsbv
                    sbvToSW st res

{-# ANN module   ("HLint: ignore Reduce duplication" :: String) #-}
{-# ANN module   ("HLint: ignore Eta reduce" :: String)         #-}
