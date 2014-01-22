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
    -- * HVector type classes
    Arity
  , ArityC
  , HVector(..)
  , HVectorF(..)
  , Wrap
  , Implicit(..)
    -- ** List length
  , Proxy(..)
    -- * Generic functions
  , convert
    -- ** Head/tail/cons
  , head
  , tail
  , cons
    -- ** Indexing
  , ValueAt
  , Index
  , index
  , set
  , element
  , elementTy
    -- * Folds
  , fold
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
    -- * Generic operations
  , mapFunctor
  , sequence
  , sequenceA
  , sequenceF
  , sequenceAF
  , wrap
  , unwrap
  , distribute
  , distributeF
    -- * Type-class based operations
  , replicate
  , replicateM
  , foldr
  , foldl
  , mapM_
  , unfoldr
  , zipMono
  , zipFold
  , eq
  , compare
  ) where

import GHC.TypeLits
import Control.Monad        (liftM)
import Control.Applicative  (Applicative,(<$>))
import Data.Functor.Compose (Compose)
import Data.Monoid          (Monoid,All(..))
import Prelude hiding
  (head,tail,concat,sequence,map,zipWith,replicate,foldr,foldl,mapM_,compare)
import qualified Prelude

import Data.Vector.HFixed.Class hiding (cons,consF)
import qualified Data.Vector.HFixed.Cont    as C


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
head = C.head . C.cvec

-- | Prepend element to the list
cons :: (HVector v, HVector w, Elems w ~ (a ': Elems v))
     => a -> v -> w
{-# INLINE cons #-}
cons a = C.vector . C.cons a . C.cvec

-- | Concatenate two vectors
concat :: ( HVector v, HVector u, HVector w
          , Elems w ~ (Elems v ++ Elems u)
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
index = C.index . C.cvec

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
element n f v = inspect v
              $ lensF n f construct

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

-- | Right fold over heterogeneous vector
foldr :: (HVector v, ArityC c (Elems v))
      => Proxy c -> (forall a. c a => a -> b -> b) -> b -> v -> b
{-# INLINE foldr #-}
foldr c f b0 = C.foldr c f b0 . C.cvec

-- | Left fold over heterogeneous vector
foldl :: (HVector v, ArityC c (Elems v))
      => Proxy c -> (forall a. c a => b -> a -> b) -> b -> v -> b
{-# INLINE foldl #-}
foldl c f b0 = C.foldl c f b0 . C.cvec

-- | Apply monadic action to every element in the vector
mapM_ :: (HVector v, ArityC c (Elems v), Monad m)
      => Proxy c -> (forall a. c a => a -> m ()) -> v -> m ()
{-# INLINE mapM_ #-}
mapM_ c f = foldl c (\m a -> m >> f a) (return ())



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


----------------------------------------------------------------
-- Collective operations
----------------------------------------------------------------

mapFunctor :: (HVectorF v)
           => (forall a. f a -> g a) -> v f -> v g
{-# INLINE mapFunctor #-}
mapFunctor f = C.vectorF . C.mapFunctor f . C.cvecF

-- | Sequence effects for every element in the vector
sequence
  :: ( Monad m, HVectorF v, HVector w, ElemsF v ~ Elems w )
  => v m -> m w
{-# INLINE sequence #-}
sequence v = do w <- C.sequence $ C.cvecF v
                return $ C.vector w

-- | Sequence effects for every element in the vector
sequenceA
  :: ( Applicative f, HVectorF v, HVector w, ElemsF v ~ Elems w )
  => v f -> f w
{-# INLINE sequenceA #-}
sequenceA v = C.vector <$> C.sequenceA (C.cvecF v)

-- | Sequence effects for every element in the vector
sequenceF :: ( Monad m, HVectorF v) => v (m `Compose` f) -> m (v f)
{-# INLINE sequenceF #-}
sequenceF v = do w <- C.sequenceF $ C.cvecF v
                 return $ C.vectorF w

-- | Sequence effects for every element in the vector
sequenceAF :: ( Applicative f, HVectorF v) => v (f `Compose` g) -> f (v g)
{-# INLINE sequenceAF #-}
sequenceAF v = C.vectorF <$> C.sequenceAF (C.cvecF v)

-- | Wrap every value in the vector into type constructor.
wrap :: ( HVector v, HVectorF w, Elems v ~ ElemsF w )
     => (forall a. a -> f a) -> v -> w f
{-# INLINE wrap #-}
wrap f = C.vectorF . C.wrap f . C.cvec

-- | Unwrap every value in the vector from the type constructor.
unwrap :: ( HVectorF v, HVector w, ElemsF v ~ Elems w )
       => (forall a. f a -> a) -> v f -> w
{-# INLINE unwrap #-}
unwrap  f = C.vector . C.unwrap f . C.cvecF

-- | Analog of /distribute/ from /Distributive/ type class.
distribute
  :: ( Functor f, HVector v, HVectorF w,  Elems v ~ ElemsF w )
  => f v -> w f
{-# INLINE distribute #-}
distribute = C.vectorF . C.distribute . fmap C.cvec

-- | Analog of /distribute/ from /Distributive/ type class.
distributeF
  :: ( Functor f, HVectorF v)
  => f (v g) -> v (f `Compose` g)
{-# INLINE distributeF #-}
distributeF = C.vectorF . C.distributeF . fmap C.cvecF



----------------------------------------------------------------
-- Type class based ops
----------------------------------------------------------------

-- | Replicate value n times.
replicate :: (HVector v, ArityC c (Elems v))
          => Proxy c -> (forall x. c x => x) -> v
{-# INLINE replicate #-}
replicate c x = C.vector $ C.replicate c x

-- | Replicate monadic action n times.
replicateM :: (HVector v, Monad m, ArityC c (Elems v))
           => Proxy c -> (forall x. c x => m x) -> m v
{-# INLINE replicateM #-}
replicateM c x = liftM C.vector $ C.replicateM c x

-- | Unfold vector.
unfoldr :: (HVector v, ArityC c (Elems v))
        => Proxy c -> (forall a. c a => b -> (a,b)) -> b -> v
{-# INLINE unfoldr #-}
unfoldr c f b0 = C.vector $ C.unfoldr c f b0

zipMono :: (HVector v, ArityC c (Elems v))
        => Proxy c -> (forall a. c a => a -> a -> a) -> v -> v -> v
{-# INLINE zipMono #-}
zipMono c f v u
  = C.vector $ C.zipMono c f (C.cvec v) (C.cvec u)

zipFold :: (HVector v, ArityC c (Elems v), Monoid m)
        => Proxy c -> (forall a. c a => a -> a -> m) -> v -> v -> m
{-# INLINE zipFold #-}
zipFold c f v u
  = C.zipFold c f (C.cvec v) (C.cvec u)

-- | Generic equality for heterogeneous vectors
eq :: (HVector v, ArityC Eq (Elems v)) => v -> v -> Bool
eq v u = getAll $ zipFold (Proxy :: Proxy Eq) (\x y -> All (x == y)) v u
{-# INLINE eq #-}

-- | Generic comparison for heterogeneous vectors
compare :: (HVector v, ArityC Ord (Elems v)) => v -> v -> Ordering
compare = zipFold (Proxy :: Proxy Ord) Prelude.compare
{-# INLINE compare #-}
