{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
-- |
-- Heterogeneous vector parametric in its elements
module Data.Vector.HFixed.HVec (
    -- * Generic heterogeneous vector
    HVec
    -- * Mutable heterogeneous vector
  , MutableHVec
  , newMutableHVec
  , unsafeFreezeHVec
    -- ** Indices
  , Idx(..)
  , natIdx
  , peanoIdx
  , readMutableHVec
  , writeMutableHVec
  , modifyMutableHVec
  , modifyMutableHVec'
  ) where

import Control.Monad.ST        (ST,runST)
import Control.Monad.Primitive (PrimMonad(..))
import Data.List               (intercalate)
import Data.Primitive.Array    (Array,MutableArray,newArray,writeArray,readArray,
                                indexArray, unsafeFreezeArray)
import GHC.Prim                (Any)
import GHC.TypeLits
import Unsafe.Coerce           (unsafeCoerce)

import qualified Data.Vector.Fixed.Internal.Arity as F (Arity(..))
import Data.Vector.HFixed        (hfoldr)
import Data.Vector.HFixed.Class



----------------------------------------------------------------
-- Generic HVec
----------------------------------------------------------------

-- | Generic heterogeneous vector
newtype HVec (xs :: [*]) = HVec (Array Any)

instance (HVector (HVec xs), Foldr Show xs) => Show (HVec xs) where
  show v
    = "[" ++ intercalate "," (hfoldr (Proxy :: Proxy Show) (\x xs -> show x : xs) [] v) ++ "]"

instance Arity xs => HVector (HVec xs) where
  type Elems (HVec xs) = xs
  inspect   (HVec arr) = inspectF arr
  construct = constructF
  {-# INLINE inspect #-}
  {-# INLINE construct #-}


inspectF :: forall xs r. Arity xs => Array Any -> Fun xs r -> r
{-# INLINE inspectF #-}
inspectF arr (Fun f)
  = apply (\(T_insp i a) -> ( unsafeCoerce $ indexArray a i
                              , T_insp (i+1) a))
            (T_insp 0 arr :: T_insp xs)
            f

constructF :: forall xs. Arity xs => Fun xs (HVec xs)
{-# INLINE constructF #-}
constructF
  = Fun $ accum (\(T_con i box) a -> T_con (i+1) (writeToBox (unsafeCoerce a) i box))
                  (\(T_con _ box)   -> HVec $ runBox len box :: HVec xs)
                  (T_con 0 (Box $ \_ -> return ()) :: T_con xs)
  where
    len = arity (Proxy :: Proxy xs)

data T_insp (xs :: [*]) = T_insp Int (Array Any)
data T_con  (xs :: [*]) = T_con  Int (Box Any)



-- Helper data type
newtype Box a = Box (forall s. MutableArray s a -> ST s ())

writeToBox :: a -> Int -> Box a -> Box a
writeToBox a i (Box f) = Box $ \arr -> f arr >> writeArray arr i a
{-# INLINE writeToBox #-}

runBox :: Int -> Box a -> Array a
{-# INLINE runBox #-}
runBox size (Box f) = runST $ do arr <- newArray size uninitialised
                                 f arr
                                 unsafeFreezeArray arr

uninitialised :: a
uninitialised = error "Data.Vector.HFixed: uninitialised element"



----------------------------------------------------------------
-- Mutable tuples
----------------------------------------------------------------

-- | Generic mutable heterogeneous vector.
newtype MutableHVec s (xs :: [*]) = MutableHVec (MutableArray s Any)

-- | Index for mutable vector.
data Idx n (nat :: Nat) where
  Idx :: (F.Arity n, NatIso n nat) => Idx n nat

peanoIdx :: (F.Arity n, NatIso n nat) => n -> Idx n nat
peanoIdx _ = Idx
{-# INLINE peanoIdx #-}

natIdx :: (F.Arity n, NatIso n nat) => Sing nat -> Idx n nat
natIdx _ = Idx
{-# INLINE natIdx #-}

index :: forall n nat. Idx n nat -> Int
index Idx = F.arity (undefined :: n)
{-# INLINE index #-}


-- | Create new uninitialized heterogeneous vector.
newMutableHVec :: forall m xs. (PrimMonad m, Arity xs)
               => m (MutableHVec (PrimState m) xs)
{-# INLINE newMutableHVec #-}
newMutableHVec = do
  arr <- newArray n uninitialised
  return $ MutableHVec arr
  where
    n = arity (Proxy :: Proxy xs)

-- | Convert mutable vector to immutable one. Mutable vector must not
--   be modified after that.
unsafeFreezeHVec :: (PrimMonad m) => MutableHVec (PrimState m) xs -> m (HVec xs)
{-# INLINE unsafeFreezeHVec #-}
unsafeFreezeHVec (MutableHVec marr) = do
  arr <- unsafeFreezeArray marr
  return $ HVec arr



readMutableHVec :: (PrimMonad m)
                => MutableHVec (PrimState m) xs
                -> Idx n nat
                -> m (ValueAt n xs)
{-# INLINE readMutableHVec #-}
readMutableHVec (MutableHVec arr) n = do
  a <- readArray arr $ index n
  return $ unsafeCoerce a

writeMutableHVec :: (PrimMonad m)
                 => MutableHVec (PrimState m) xs
                 -> Idx n nat
                 -> ValueAt n xs
                 -> m ()
{-# INLINE writeMutableHVec #-}
writeMutableHVec (MutableHVec arr) n a = do
  writeArray arr (index n) (unsafeCoerce a)

modifyMutableHVec :: (PrimMonad m)
                  => MutableHVec (PrimState m) xs
                  -> Idx n nat
                  -> (ValueAt n xs -> ValueAt n xs)
                  -> m ()
{-# INLINE modifyMutableHVec #-}
modifyMutableHVec hvec n f = do
  a <- readMutableHVec hvec n
  writeMutableHVec hvec n (f a)

modifyMutableHVec' :: (PrimMonad m)
                   => MutableHVec (PrimState m) xs
                   -> Idx n nat
                   -> (ValueAt n xs -> ValueAt n xs)
                   -> m ()
{-# INLINE modifyMutableHVec' #-}
modifyMutableHVec' hvec n f = do
  a <- readMutableHVec hvec n
  writeMutableHVec hvec n $! f a
