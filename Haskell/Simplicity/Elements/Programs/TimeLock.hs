-- | This module defines Simplicity expressions that implement timelock functions from "Simplicity.Elements.DataTypes".
module Simplicity.Elements.Programs.TimeLock
 ( txIsFinal
 , txLockHeight, txLockTime
 , brokenTxLockDistance, brokenTxLockDuration
 , checkLockHeight, checkLockTime
 , brokenCheckLockDistance, brokenCheckLockDuration
 , module Simplicity.Programs.TimeLock
 , Bit
 ) where

import Prelude hiding (Word, all, drop, max, not, take)

import Simplicity.Elements.Primitive
import Simplicity.Elements.Term
import Simplicity.Elements.Programs.Transaction.Lib
import Simplicity.Programs.Arith
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic
import Simplicity.Programs.TimeLock
import Simplicity.Programs.Word

-- | Implements 'Simplicity.Elements.DataTypes.txIsFinal'.
txIsFinal :: (Core term, Primitive term) => term () Bit
txIsFinal = (unit &&& unit) >>> forWhile word32 body >>> copair iden true
 where
  body = take (drop (primitive InputSequence)) >>> copair (injl true) (all word32 >>> copair (injl false) (injr unit))

-- | Returns the transaction's LockTime if it is a Height value, otherwise it returns 0.
txLockHeight :: (Core term, Primitive term) => term () Height
txLockHeight = txIsFinal &&& primitive LockTime
           >>> cond z (parseLock >>> (copair iden z))
 where
  z = unit >>> zero word32

-- | Returns the transaction's LockTime if it is a Time value, otherwise it returns 0.
txLockTime :: (Core term, Primitive term) => term () Time
txLockTime = txIsFinal &&& primitive LockTime
         >>> cond z (parseLock >>> (copair z iden))
 where
  z = unit >>> zero word32

bip68VersionCheck :: (Core term, Primitive term) => term () Bit
bip68VersionCheck = scribe (toWord32 2) &&& primitive Version >>> le word32

-- | Computes the current input's relative height timelock, or 0 if it has no such timelock.
brokenTxLockDistance :: (Assert term, Primitive term) => term () Distance
brokenTxLockDistance = bip68VersionCheck &&& (currentSequence >>> parseSequence)
             >>> cond (copair (unit >>> z) (copair iden (unit >>> z))) (unit >>> z)
 where
  z = zero word16

-- | Computes the current input's relative time timelock, or 0 if it has no such timelock.
brokenTxLockDuration :: (Assert term, Primitive term) => term () Duration
brokenTxLockDuration = bip68VersionCheck &&& (currentSequence >>> parseSequence)
             >>> cond (copair (unit >>> z) (copair (unit >>> z) iden)) (unit >>> z)
 where
  z = zero word16

-- | Asserts that the input is less than or equal to the value returned by 'txLockHeight'.
checkLockHeight :: (Assert term, Primitive term) => term Height ()
checkLockHeight = assert (iden &&& (unit >>> txLockHeight) >>> le word32)

-- | Asserts that the input is less than or equal to the value returned by 'txLockTime'.
checkLockTime :: (Assert term, Primitive term) => term Time ()
checkLockTime = assert (iden &&& (unit >>> txLockTime) >>> le word32)

-- | Asserts that the input is less than or equal to the value returned by 'txLockDistance'.
brokenCheckLockDistance :: (Assert term, Primitive term) => term Distance ()
brokenCheckLockDistance = assert (iden &&& (unit >>> brokenTxLockDistance) >>> le word16)

-- | Asserts that the input is less than or equal to the value returned by 'txLockDuration'.
brokenCheckLockDuration :: (Assert term, Primitive term) => term Duration ()
brokenCheckLockDuration = assert (iden &&& (unit >>> brokenTxLockDuration) >>> le word16)
