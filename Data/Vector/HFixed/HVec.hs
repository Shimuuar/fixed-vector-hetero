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
    -- ** Mutable heterogeneous vector
  , MutableHVec
  , newMutableHVec
  , unsafeFreezeHVec
  , readMutableHVec
  , writeMutableHVec
  , writeMutableHVecTy
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

import Data.Vector.Fixed.Internal.Arity (Arity(arity))
import Data.Vector.HFixed.Class         (NatIso(..))
import Data.Vector.HFixed             hiding (Arity(..))
import Data.Vector.HFixed.TypeList (Length(..))


----------------------------------------------------------------
-- Generic HVec
----------------------------------------------------------------

-- | Generic heterogeneous vector
newtype HVec (xs :: [*]) = HVec (Array Any)

instance (HVector (HVec xs), Foldr Show xs) => Show (HVec xs) where
  show v
    = "[" ++ intercalate "," (hfoldr (Proxy :: Proxy Show) (\x xs -> show x : xs) [] v) ++ "]"

instance (HVecClass xs, Length xs, Functor (Fun xs)) => HVector (HVec xs) where
  type Elems (HVec xs) = xs
  inspect (HVec arr) f = inspectWorker arr 0 f
  construct = fmap fini (constructWorker 0)
    where
      size = listLen (Proxy :: Proxy xs)
      fini = HVec . runBox size
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

-- Implementation of heterogeneous vector
class HVecClass xs where
  inspectWorker :: Array Any -> Int -> Fun xs r -> r
  constructWorker :: Int -- ^ Offset
                  -> Fun xs (Box Any)


instance HVecClass '[] where
  inspectWorker   _ _ = unFun
  constructWorker _   = Fun $ Box (const $ return ())
  {-# INLINE inspectWorker #-}
  {-# INLINE constructWorker #-}


instance (Functor (Fun xs), HVecClass xs) => HVecClass (x ': xs) where
  inspectWorker arr i (Fun f :: Fun (x ': xs) r)
    = inspectWorker arr (i+1) (Fun (f x) :: Fun xs r)
    where
      x = unsafeCoerce $ indexArray arr i
  --
  constructWorker off = Fun $ \a ->
    unFun (writeToBox (unsafeCoerce a) off `fmap` step)
    where
      step = constructWorker (off + 1) :: Fun xs (Box Any)
  {-# INLINE inspectWorker #-}
  {-# INLINE constructWorker #-}




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

-- | Create new uninitialized heterogeneous vector.
newMutableHVec :: forall m xs. (PrimMonad m, Length xs)
               => m (MutableHVec (PrimState m) xs)
{-# INLINE newMutableHVec #-}
newMutableHVec = do
  arr <- newArray n uninitialised
  return $ MutableHVec arr
  where
    n = listLen (Proxy :: Proxy xs)

unsafeFreezeHVec :: (PrimMonad m) => MutableHVec (PrimState m) xs -> m (HVec xs)
{-# INLINE unsafeFreezeHVec #-}
unsafeFreezeHVec (MutableHVec marr) = do
  arr <- unsafeFreezeArray marr
  return $ HVec arr

readMutableHVec :: (PrimMonad m, Arity n)
                => MutableHVec (PrimState m) xs
                -> n
                -> m (ValueAt n xs)
{-# INLINE readMutableHVec #-}
readMutableHVec (MutableHVec arr) n = do
  a <- readArray arr $ arity n
  return $ unsafeCoerce a

writeMutableHVec :: (PrimMonad m, Arity n)
                 => MutableHVec (PrimState m) xs
                 -> n
                 -> ValueAt n xs
                 -> m ()
{-# INLINE writeMutableHVec #-}
writeMutableHVec (MutableHVec arr) n a = do
  writeArray arr (arity n) (unsafeCoerce a)

writeMutableHVecTy :: forall m n a xs.
                      (PrimMonad m, Arity (ToPeano n), NatIso (ToPeano n) n)
                   => MutableHVec (PrimState m) xs
                   -> Sing n
                   -> ValueAt (ToPeano n) xs
                   -> m ()
{-# INLINE writeMutableHVecTy #-}
writeMutableHVecTy arr _ a = writeMutableHVec arr (undefined :: ToPeano n) a



modifyMutableHVec :: (PrimMonad m, Arity n)
                  => MutableHVec (PrimState m) xs
                  -> n
                  -> (ValueAt n xs -> ValueAt n xs)
                  -> m ()
{-# INLINE modifyMutableHVec #-}
modifyMutableHVec hvec n f = do
  a <- readMutableHVec hvec n
  writeMutableHVec hvec n (f a)

modifyMutableHVec' :: (PrimMonad m, Arity n)
                   => MutableHVec (PrimState m) xs
                   -> n
                   -> (ValueAt n xs -> ValueAt n xs)
                   -> m ()
{-# INLINE modifyMutableHVec' #-}
modifyMutableHVec' hvec n f = do
  a <- readMutableHVec hvec n
  writeMutableHVec hvec n $! f a
