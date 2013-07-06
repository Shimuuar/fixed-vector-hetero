{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ConstraintKinds       #-}
-- |
-- Heterogeneous vectors.
module Data.Vector.HFixed (
    -- * Basic API
    Fn
  , Fun(..)
  , Arity(..)
  , HVector(..)
    -- ** List length
  , Proxy(..)
    -- * Generic functions
  , convert
    -- ** Head/tail/cons
  , head
  , tail
  , cons
  , consV
    -- ** Indexing
  , ValueAt
  , Index
  , index
  , set
  , element
  , elementTy
    -- * Folds
  , fold
  , Foldr
  , hfoldr
    -- ** Unfold
  , Unfoldr
  , unfoldr
  , unfoldrM
    -- ** Concatenation
  , concat
    -- * Generic constructors
  , mk0
  , mk1
  , mk2
  , mk3
  , mk4
  , mk5
    -- * Interop with vector
  , homConstruct
  , homInspect
  ) where

import GHC.TypeLits
import Prelude hiding (head,tail,concat)

import Data.Vector.HFixed.Class
import qualified Data.Vector.HFixed.Cont as C



----------------------------------------------------------------
-- Generic API
----------------------------------------------------------------

-- | We can convert between any two vector which have same
--   structure but different representations.
convert :: (HVector v, HVector w, Elems v ~ Elems w)
        => v -> w
{-# INLINE convert #-}
convert v = inspect v construct

-- | Tail of the vector
--
-- >>> case tail ('a',"aa",()) of x@(_,_) -> x
-- ("aa",())
tail :: (HVector v, HVector w, (a ': Elems w) ~ Elems v)
     => v -> w
{-# INLINE tail #-}
tail = C.vector . C.tail . C.cvec


-- | Head of the vector
head :: (HVector v, Elems v ~ (a ': as), Arity as)
     => v -> a
{-# INLINE head #-}
head = C.runContVec C.head . C.cvec

-- | Prepend element to the list
cons :: (HVector v, HVector w, Elems w ~ (a ': Elems v))
     => a -> v -> w
{-# INLINE cons #-}
cons a = C.vector . C.cons a . C.cvec

-- | Prepend element to the list
consV :: ( HVector v, HVector u, HVector w
         , Elems u ~ '[a]
         , Elems w ~ (a ': Elems v))
      => u -> v -> w
{-# INLINE consV #-}
consV u = C.vector . C.consV (C.cvec u) . C.cvec

-- | Concatenate two vectors
concat :: ( HVector v, HVector u, HVector w
          , Elems w ~ (Elems v ++ Elems u)
          , Arity (Elems v)
          )
       => v -> u -> w
concat v u = C.vector $ C.concat (C.cvec v) (C.cvec u)
{-# INLINE concat #-}



----------------------------------------------------------------
-- Indexing
----------------------------------------------------------------

-- | Index heterogeneous vector
index :: (Index n (Elems v), HVector v) => v -> n -> ValueAt n (Elems v)
{-# INLINE index #-}
index v n = C.runContVec (C.index n) $ C.cvec v

-- | Set element in the vector
set :: (Index n (Elems v), HVector v)
       => n -> ValueAt n (Elems v) -> v -> v
{-# INLINE set #-}
set n x = C.vector
        . C.set n x
        . C.cvec

-- | Twan van Laarhoven's lens for i'th element.
element :: (Index n (Elems v), ValueAt n (Elems v) ~ a, HVector v, Functor f)
        => n -> (a -> f a) -> (v -> f v)
{-# INLINE element #-}
element n f v = (\a -> set n a v) `fmap` f (index v n)

-- | Twan van Laarhoven's lens for i'th element.
elementTy :: forall n a f v.
             ( Index   (ToPeano n) (Elems v)
             , ValueAt (ToPeano n) (Elems v) ~ a
             , NatIso  (ToPeano n) n
             , HVector v
             , Functor f)
          => Sing n -> (a -> f a) -> (v -> f v)
{-# INLINE elementTy #-}
elementTy _ = element (undefined :: ToPeano n)



----------------------------------------------------------------
-- Folds over vector
----------------------------------------------------------------

-- | Most generic form of fold which doesn't constrain elements id use
-- of 'inspect'. Or in more convenient form below:
fold :: HVector v => v -> Fn (Elems v) r -> r
fold v f = inspect v (Fun f)
{-# INLINE fold #-}


-- | Right fold over heterogeneous vector.
hfoldr :: (Foldr c (Elems v), HVector v)
       => Proxy c                        -- ^ Constraint on polymorphic function.
       -> (forall a. c a => a -> b -> b) -- ^ Function which could be
                                         --   applied to all elements of
                                         --   vector.
       -> b                              -- ^ Initial value
       -> v                              -- ^ Vector
       -> b
hfoldr wit f b0 v
  = (inspect v $ hfoldrF wit f) b0


-- | Unfolding of vector
unfoldr :: (Unfoldr c (Elems v), HVector v)
        => Proxy c
        -> (forall a. c a => b -> (a,b))
        -> b
        -> v
unfoldr wit step b0 = unforldrF wit step construct b0

-- | Unfolding of vector
unfoldrM :: (Unfoldr c (Elems v), Monad m, HVector v)
         => Proxy c
         -> (forall a. c a => b -> m (a,b))
         -> b
         -> m v
unfoldrM wit step b0 = unforldrFM wit step construct b0




----------------------------------------------------------------
-- Constructors
----------------------------------------------------------------

mk0 :: (HVector v, Elems v ~ '[]) => v
mk0 = C.vector C.mk0
{-# INLINE mk0 #-}

mk1 :: (HVector v, Elems v ~ '[a]) => a -> v
mk1 a = C.vector $ C.mk1 a
{-# INLINE mk1 #-}

mk2 :: (HVector v, Elems v ~ '[a,b]) => a -> b -> v
mk2 a b = C.vector $ C.mk2 a b
{-# INLINE mk2 #-}

mk3 :: (HVector v, Elems v ~ '[a,b,c]) => a -> b -> c -> v
mk3 a b c = C.vector $ C.mk3 a b c
{-# INLINE mk3 #-}
            
mk4 :: (HVector v, Elems v ~ '[a,b,c,d]) => a -> b -> c -> d -> v
mk4 a b c d = C.vector $ C.mk4 a b c d
{-# INLINE mk4 #-}

mk5 :: (HVector v, Elems v ~ '[a,b,c,d,e]) => a -> b -> c -> d -> e -> v
mk5 a b c d e = C.vector $ C.mk5 a b c d e
{-# INLINE mk5 #-}
