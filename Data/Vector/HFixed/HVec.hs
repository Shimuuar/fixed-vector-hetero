{-# LANGUAGE GADTs                #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE FlexibleContexts     #-}
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
  , readMutableHVec
  , writeMutableHVec
  , modifyMutableHVec
  , modifyMutableHVec'
  ) where

import Control.Monad.ST        (ST,runST)
import Control.Monad.Primitive (PrimMonad(..))
import Control.DeepSeq         (NFData(..))
import Data.Monoid             (Monoid(..))
import Data.List               (intercalate)
import Data.Primitive.Array    (Array,MutableArray,newArray,writeArray,readArray,
                                indexArray, unsafeFreezeArray)
import GHC.Prim                (Any)
import Unsafe.Coerce           (unsafeCoerce)

import qualified Data.Vector.Fixed.Cont as F (Arity(..))
import qualified Data.Vector.HFixed     as H
import Data.Vector.HFixed.Class



----------------------------------------------------------------
-- Generic HVec
----------------------------------------------------------------

-- | Generic heterogeneous vector
newtype HVec (xs :: [*]) = HVec (Array Any)

instance (ArityC Show xs) => Show (HVec xs) where
  show v
    = "[" ++ intercalate ", " (H.foldr (Proxy :: Proxy Show) (\x xs -> show x : xs) [] v) ++ "]"

instance (ArityC Eq xs) => Eq (HVec xs) where
  (==) = H.eq
  {-# INLINE (==) #-}

-- NOTE: We need to add `Eq (HVec xs)' since GHC cannot deduce that
--       `ArityC Ord xs => ArityC Eq xs' for all xs
instance (ArityC Ord xs, Eq (HVec xs)) => Ord (HVec xs) where
  compare = H.compare
  {-# INLINE compare #-}

instance (ArityC Monoid xs) => Monoid (HVec xs) where
  mempty  = H.replicate (Proxy :: Proxy Monoid) mempty
  mappend = H.zipMono (Proxy :: Proxy Monoid) mappend
  {-# INLINE mempty  #-}
  {-# INLINE mappend #-}

instance (ArityC NFData xs) => NFData (HVec xs) where
  rnf = H.rnf
  {-# INLINE rnf #-}

instance Arity xs => HVector (HVec xs) where
  type Elems (HVec xs) = xs
  inspect   (HVec arr) = inspectFF arr
  construct = constructFF
  {-# INLINE inspect #-}
  {-# INLINE construct #-}


inspectFF :: forall xs r. Arity xs => Array Any -> Fun xs r -> r
{-# INLINE inspectFF #-}
inspectFF arr
  = runContVec
  $ apply (\(T_insp i a) -> ( unsafeCoerce $ indexArray a i
                            , T_insp (i+1) a))
          (T_insp 0 arr :: T_insp xs)


constructFF :: forall xs. Arity xs => Fun xs (HVec xs)
{-# INLINE constructFF #-}
constructFF
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
writeToBox a i (Box f) = Box $ \arr -> f arr >> (writeArray arr i $! a)
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

-- | Read value at statically known index.
readMutableHVec :: (PrimMonad m, Index n xs, Arity xs)
                => MutableHVec (PrimState m) xs
                -> n
                -> m (ValueAt n xs)
{-# INLINE readMutableHVec #-}
readMutableHVec (MutableHVec arr) n = do
  a <- readArray arr $ F.arity n
  return $ unsafeCoerce a

-- | Write value at statically known index
writeMutableHVec :: (PrimMonad m, Index n xs, Arity xs)
                 => MutableHVec (PrimState m) xs
                 -> n
                 -> ValueAt n xs
                 -> m ()
{-# INLINE writeMutableHVec #-}
writeMutableHVec (MutableHVec arr) n a = do
  writeArray arr (F.arity n) (unsafeCoerce a)

-- | Apply function to value at statically known index.
modifyMutableHVec :: (PrimMonad m, Index n xs, Arity xs)
                  => MutableHVec (PrimState m) xs
                  -> n
                  -> (ValueAt n xs -> ValueAt n xs)
                  -> m ()
{-# INLINE modifyMutableHVec #-}
modifyMutableHVec hvec n f = do
  a <- readMutableHVec hvec n
  writeMutableHVec hvec n (f a)

-- | Strictly apply function to value at statically known index.
modifyMutableHVec' :: (PrimMonad m, Index n xs, Arity xs)
                   => MutableHVec (PrimState m) xs
                   -> n
                   -> (ValueAt n xs -> ValueAt n xs)
                   -> m ()
{-# INLINE modifyMutableHVec' #-}
modifyMutableHVec' hvec n f = do
  a <- readMutableHVec hvec n
  writeMutableHVec hvec n $! f a
