{-# LANGUAGE GADTs #-}
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
  , HVector(..)
  , ValueAt
  , Index
    -- ** CPS-encoded vector
  , ContVec(..)
  , VecList(..)
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
  , distribute
  ) where

import Control.Applicative (Applicative(..))
import Control.Monad       (liftM,ap)
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


-- | List like heterogeneous vector.
data VecList :: [*] -> * where
  Nil  :: VecList '[]
  Cons :: x -> VecList xs -> VecList (x ': xs)

instance Arity xs => HVector (VecList xs) where
  type Elems (VecList xs) = xs
  construct = Fun $ accum
    (\(T_List f) a -> T_List (f . Cons a))
    (\(T_List f)   -> f Nil)
    (T_List id :: T_List xs xs)
  inspect v (Fun f) = apply step v f
    where
      step :: VecList (a ': as) -> (a, VecList as)
      step (Cons a xs) = (a, xs)
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}


newtype T_List all xs = T_List (VecList xs -> VecList all)


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
head :: forall x xs. Arity xs => ContVec (x ': xs) -> x
head = runContVec $ Fun $ \x -> unFun (pure x :: Fun xs x)
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
index :: Index n xs => ContVec xs -> n -> ValueAt n xs
index (ContVec cont) = cont . getF
{-# INLINE index #-}

-- | Set value on nth position.
set :: Index n xs => n -> ValueAt n xs -> ContVec xs -> ContVec xs
set n x (ContVec cont) = ContVec $ cont . putF n x
{-# INLINE set #-}



----------------------------------------------------------------
-- Collective operations
----------------------------------------------------------------

-- | Sequence effects for every element in the vector
sequence :: (Monad m, Arity xs) => ContVec (Wrap m xs) -> m (ContVec xs)
{-# INLINE sequence #-}
sequence (ContVec cont)
  = cont
  $ castTFun $ sequenceF construct

-- | Sequence effects for every element in the vector
sequenceA :: (Applicative f, Arity xs) => ContVec (Wrap f xs) -> f (ContVec xs)
{-# INLINE sequenceA #-}
sequenceA (ContVec cont)
  = cont
  $ castTFun $ sequenceAF construct

sequenceF :: forall m xs r. (Monad m, Arity xs)
          => Fun xs r -> TFun m xs (m r)
{-# INLINE sequenceF #-}
sequenceF (Fun f) = TFun $ accumTy (\(T_seq m) a -> T_seq $ m `ap` a)
                                   (\(T_seq m)   -> m)
                                   (T_seq (return f) :: T_seq m r xs)

sequenceAF :: forall m xs r. (Applicative m, Arity xs)
          => Fun xs r -> TFun m xs (m r)
{-# INLINE sequenceAF #-}
sequenceAF (Fun f) = TFun $ accumTy (\(T_seq m) a -> T_seq $ m <*> a)
                                    (\(T_seq m)   -> m)
                                    (T_seq (pure f) :: T_seq m r xs)

newtype T_seq f r xs = T_seq (f (Fn xs r))



-- | Wrap every value in the vector into type constructor.
wrap :: Arity xs => (forall a. a -> f a) -> ContVec xs -> ContVec (Wrap f xs)
{-# INLINE wrap #-}
wrap f (ContVec cont)
  = ContVec $ \fun -> cont $ wrapF f fun

wrapF :: forall f xs r. (Arity xs)
       => (forall a. a -> f a) -> Fun (Wrap f xs) r -> Fun xs r
{-# INLINE wrapF #-}
wrapF g (Fun f0) = Fun $ accum (\(T_wrap f) x -> T_wrap $ f (g x))
                                (\(T_wrap r)   -> r)
                                (T_wrap f0 :: T_wrap f r xs)

newtype T_wrap f r xs = T_wrap (Fn (Wrap f xs) r)



-- | Unwrap every value in the vector from the type constructor.
unwrap :: Arity xs => (forall a. f a -> a) -> ContVec (Wrap f xs) -> ContVec xs
{-# INLINE unwrap #-}
unwrap f (ContVec cont)
  = ContVec $ \fun -> cont $ unwrapF f fun

unwrapF :: forall f xs r. (Arity xs)
         => (forall a. f a -> a) -> Fun xs r -> Fun (Wrap f xs) r
{-# INLINE unwrapF #-}
unwrapF g (Fun f0) = Fun $ accumTy (\(T_unwrap f) x -> T_unwrap $ f (g x))
                                    (\(T_unwrap r)   -> r)
                                    (T_unwrap f0 :: T_unwrap r xs)

newtype T_unwrap r xs = T_unwrap (Fn xs r)




-- | Analog of /distribute/ from /Distributive/ type class.
distribute :: forall f xs. (Functor f, Arity xs)
           => f (ContVec xs) -> ContVec (Wrap f xs)
{-# INLINE distribute #-}
distribute f
  = ContVec $ \(Fun fun) -> applyTy
      (\(T_distribute v) -> (fmap (\(Cons x _) -> x) v, T_distribute $ fmap (\(Cons _ x) -> x) v))
      (T_distribute (fmap vector f) :: T_distribute f xs)
      fun

newtype T_distribute f xs = T_distribute (f (VecList xs))
