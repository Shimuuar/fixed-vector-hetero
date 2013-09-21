{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE Rank2Types       #-}
-- |
-- CPS encoded heterogeneous vectors.
module Data.Vector.HFixed.Cont (
    -- * CPS-encoded vector
    -- ** Type classes
    Fn
  , Fun(..)
  , Arity(..)
  , ArityFun(..)
  , HVector(..)
    -- ** CPS-encoded vector
  , ContVec(..)
  , ValueAt
  , Index
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
  , head
  , tail
  , cons
  , consV
  , concat
  , index
  , set
    -- * Collective operations
  , sequence
  , sequenceA
  , wrap
  , unwrap
  ) where

import Control.Applicative (Applicative(..))
import Prelude hiding (head,tail,concat,sequence,sequence_)

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

instance Arity xs => HVector (ContVec xs) where
  type Elems (ContVec xs) = xs
  construct = Fun $
    accum (\(T_mkN f) x -> T_mkN (f . cons x))
          (\(T_mkN f)   -> f mk0)
          (T_mkN id :: T_mkN xs xs)
  inspect   = flip runContVec
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

newtype T_mkN all xs = T_mkN (ContVec xs -> ContVec all)



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

-- | Head of vector
head :: forall x xs. Arity xs => Fun (x ': xs) x
head = Fun $ \x -> unFun (pure x :: Fun xs x)
{-# INLINE head #-}

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

-- | Get value at @n@th position.
index :: Index n xs => n -> Fun xs (ValueAt n xs)
index = getF
{-# INLINE index #-}

-- | Set value on nth position.
set :: Index n xs => n -> ValueAt n xs -> ContVec xs -> ContVec xs
set n x (ContVec cont) = ContVec $ cont . putF n x
{-# INLINE set #-}



----------------------------------------------------------------
-- Collective operations
----------------------------------------------------------------

-- | Sequence effects for every element in the vector
sequence :: (Monad m, ArityFun xs) => ContVec (Wrap m xs) -> m (ContVec xs)
{-# INLINE sequence #-}
sequence (ContVec cont)
  = cont
  $ sequenceF (return construct)

-- | Sequence effects for every element in the vector
sequenceA :: (Applicative f, ArityFun xs) => ContVec (Wrap f xs) -> f (ContVec xs)
{-# INLINE sequenceA #-}
sequenceA (ContVec cont)
  = cont
  $ sequenceAF (pure construct)

-- | Wrap every value in the vector into type constructor.
wrap :: ArityFun xs => (forall a. a -> f a) -> ContVec xs -> ContVec (Wrap f xs)
{-# INLINE wrap #-}
wrap f (ContVec cont)
  = ContVec $ \fun -> cont $ wrapF f fun

-- | Unwrap every value in the vector from the type constructor.
unwrap :: ArityFun xs => (forall a. f a -> a) -> ContVec (Wrap f xs) -> ContVec xs
{-# INLINE unwrap #-}
unwrap f (ContVec cont)
  = ContVec $ \fun -> cont $ unwrapF f fun
