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
    Arity(..)
  , HVector(..)  
  , ContVec(..)
  , ValueAt
  , Index
    -- ** Runnning ContVecT
  , runContVec
    -- ** Conversion to/from vector
  , cvec
  , vector
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
  , consV
  , concat
  , set
    -- * Finalizers
  , head
  , index
  ) where

import Control.Applicative (Applicative(..))
import Prelude hiding (head,tail,concat)

import Data.Vector.HFixed.Class



----------------------------------------------------------------
-- Data
----------------------------------------------------------------

-- | CPS-encoded heterogeneous vector.
newtype ContVec xs = ContVec (forall r. Fun xs r -> r)


-- | Apply finalizer to continuation.
runContVec :: Fun xs r -> ContVec xs -> r
runContVec f (ContVec cont) = cont f
{-# INLINE runContVec #-}



----------------------------------------------------------------
-- Conversions between vectors
----------------------------------------------------------------

-- | Convert heterogeneous vector to CPS form
cvec :: (HVector v, Elems v ~ xs) => v -> ContVec xs
cvec v = ContVec (inspect v)
{-# INLINE cvec #-}

-- | Convert CPS-vector to heterogeneous vector
vector :: (HVector v, Elems v ~ xs) => ContVec xs -> v
vector = runContVec construct
{-# INLINE vector #-}



----------------------------------------------------------------
-- Constructors
----------------------------------------------------------------

mk0 :: ContVec '[]
mk0 = ContVec $ \(Fun r) -> r
{-# INLINE mk0 #-}

mk1 :: a -> ContVec '[a]
mk1 a1 = ContVec $ \(Fun f) -> f a1
{-# INLINE mk1 #-}

mk2 :: a -> b -> ContVec '[a,b]
mk2 a1 a2 = ContVec $ \(Fun f) -> f a1 a2
{-# INLINE mk2 #-}

mk3 :: a -> b -> c -> ContVec '[a,b,c]
mk3 a1 a2 a3 = ContVec $ \(Fun f) -> f a1 a2 a3
{-# INLINE mk3 #-}

mk4 :: a -> b -> c -> d -> ContVec '[a,b,c,d]
mk4 a1 a2 a3 a4 = ContVec $ \(Fun f) -> f a1 a2 a3 a4
{-# INLINE mk4 #-}

mk5 :: a -> b -> c -> d -> e -> ContVec '[a,b,c,d,e]
mk5 a1 a2 a3 a4 a5 = ContVec $ \(Fun f) -> f a1 a2 a3 a4 a5
{-# INLINE mk5 #-}



----------------------------------------------------------------
-- Transformation
----------------------------------------------------------------

-- | Tail of CPS-encoded vector
tail :: ContVec (x ': xs) -> ContVec xs
tail (ContVec cont) = ContVec $ cont . constFun
{-# INLINE tail #-}

-- | Cons element to the vector
cons :: x -> ContVec xs -> ContVec (x ': xs)
cons x (ContVec cont) = ContVec $ \f -> cont $ apFun f x
{-# INLINE cons #-}

-- | Cons singleton vector.
consV :: ContVec '[x] -> ContVec xs -> ContVec (x ': xs)
consV (ContVec cont1) (ContVec cont) = ContVec $ cont . cont1 . curry1

-- | Concatenate two vectors
concat :: Arity xs => ContVec xs -> ContVec ys -> ContVec (xs ++ ys)
concat (ContVec contX) (ContVec contY) = ContVec $ contY . contX . curryF
{-# INLINE concat #-}

-- | Set value on nth position.
set :: Index n xs => n -> ValueAt n xs -> ContVec xs -> ContVec xs
set n x (ContVec cont) = ContVec $ cont . putF n x
{-# INLINE set #-}



----------------------------------------------------------------
-- Finalizers
----------------------------------------------------------------

-- | Head of vector
head :: forall x xs. Arity xs => Fun (x ': xs) x
head = Fun $ \x -> unFun (pure x :: Fun xs x)

-- | Get value at @n@th position.
index :: Index n xs => n -> Fun xs (ValueAt n xs)
index = getF
