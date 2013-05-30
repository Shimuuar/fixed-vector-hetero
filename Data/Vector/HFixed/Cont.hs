{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE Rank2Types       #-}
-- |
-- CPS encoded heterogeneous vectors.
module Data.Vector.HFixed.Cont (
    -- * CPS-encoded vector
    ContVecT(..)
  , ContVec
    -- ** Runnning ContVecT
  , runContVecM
  , runContVecT
  , runContVec
    -- ** Conversion to/from vector
  , cvec
  , vector
  , vectorM
    -- * Constructors
  , mk0
  , mk1
  , mk2
  , mk3
  , mk4
  , mk5
    -- * Generic functions
  , tail
  , cons
    -- * Finalizers
  , head
  ) where

import Data.Functor.Identity
import Prelude hiding (head,tail)

import Data.Vector.HFixed.Class


----------------------------------------------------------------
-- Data
----------------------------------------------------------------

-- | CPS-encoded heterogeneous vector.
newtype ContVecT m xs = ContVecT (forall r. Fun xs (m r) -> m r)

-- | Vector without monadic context
type ContVec = ContVecT Identity


-- | Apply finalizer to continuation.
runContVecM :: Fun xs (m r) -> ContVecT m xs -> m r
runContVecM f (ContVecT cont) = cont f
{-# INLINE runContVecM #-}

-- | Apply finalizer to continuation.
runContVecT :: (Monad m, Functor (Fun xs)) => Fun xs r -> ContVecT m xs -> m r
runContVecT f (ContVecT cont) = cont (fmap return f)
{-# INLINE runContVecT #-}

-- | Apply finalizer to continuation.
runContVec :: (Functor (Fun xs)) => Fun xs r -> ContVec xs -> r
runContVec f (ContVecT cont) = runIdentity $ cont (fmap return f)
{-# INLINE runContVec #-}



----------------------------------------------------------------
-- Conversions between vectors
----------------------------------------------------------------

-- | Convert heterogeneous vector to CPS form
cvec :: (HVector v, Elems v ~ xs) => v -> ContVecT m xs
cvec v = ContVecT (inspect v)
{-# INLINE cvec #-}

-- | Convert CPS-vector to heterogeneous vector
vector :: (HVector v, Elems v ~ xs, Functor (Fun xs)) => ContVec xs -> v
vector = runContVec construct
{-# INLINE vector #-}

-- | Convert CPS-vector to heterogeneous vector
vectorM :: (HVector v, Elems v ~ xs, Functor (Fun xs), Monad m) => ContVecT m xs -> m v
vectorM = runContVecT construct
{-# INLINE vectorM #-}


----------------------------------------------------------------
-- Constructors
----------------------------------------------------------------

mk0 :: ContVecT m '[]
mk0 = ContVecT $ \(Fun r) -> r
{-# INLINE mk0 #-}

mk1 :: a -> ContVecT m '[a]
mk1 a1 = ContVecT $ \(Fun f) -> f a1
{-# INLINE mk1 #-}

mk2 :: a -> b -> ContVecT m '[a,b]
mk2 a1 a2 = ContVecT $ \(Fun f) -> f a1 a2
{-# INLINE mk2 #-}

mk3 :: a -> b -> c -> ContVecT m '[a,b,c]
mk3 a1 a2 a3 = ContVecT $ \(Fun f) -> f a1 a2 a3
{-# INLINE mk3 #-}

mk4 :: a -> b -> c -> d -> ContVecT m '[a,b,c,d]
mk4 a1 a2 a3 a4 = ContVecT $ \(Fun f) -> f a1 a2 a3 a4
{-# INLINE mk4 #-}

mk5 :: a -> b -> c -> d -> e -> ContVecT m '[a,b,c,d,e]
mk5 a1 a2 a3 a4 a5 = ContVecT $ \(Fun f) -> f a1 a2 a3 a4 a5
{-# INLINE mk5 #-}



----------------------------------------------------------------
-- Transformation
----------------------------------------------------------------

-- | Tail of CPS-encoded vector
tail :: ContVecT m (x ': xs) -> ContVecT m xs
tail (ContVecT cont) = ContVecT $ \(Fun f) -> cont (Fun $ \_ -> f)
{-# INLINE tail #-}

-- | Cons element to the vector
cons :: x -> ContVecT m xs -> ContVecT m (x ': xs)
cons x (ContVecT cont) = ContVecT $ \(Fun f) -> cont $ Fun $ f x
{-# INLINE cons #-}



----------------------------------------------------------------
-- Finalizers
----------------------------------------------------------------

-- | Head of vector
head :: forall x xs. ConstF xs => Fun (x ': xs) x
head = Fun $ \x -> unFun (constF x :: Fun xs x)
