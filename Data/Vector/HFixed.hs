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
  , Proxy(..)
  , ContVec
  , asCVec
    -- * Position based functions
  , convert
  , head
  , tail
  , cons
  , concat
    -- ** Indexing
  , ValueAt
  , Index
  , index
  , set
  , element
  , elementCh
  , elementTy
  , elementChTy
    -- * Generic constructors
  , mk0
  , mk1
  , mk2
  , mk3
  , mk4
  , mk5
    -- * Folds and unfolds
  , fold
  , foldr
  , foldl
  , mapM_
  , unfoldr
    -- * Polymorphic values
  , replicate
  , replicateM
  , replicateF
  , zipMono
  , zipMonoF
  , zipFold
  , monomorphize
  , monomorphizeF
    -- * Vector parametrized with type constructor
  , mapFunctor
  , sequence
  , sequenceA
  , sequenceF
  , sequenceAF
  , wrap
  , unwrap
  , distribute
  , distributeF
    -- * Specialized operations
  , eq
  , compare
  , rnf
  ) where

import Control.Monad        (liftM)
import Control.Applicative  (Applicative,(<$>))
import qualified Control.DeepSeq as NF
                                       
import Data.Functor.Compose (Compose)
import Data.Monoid          (Monoid,All(..))
import Prelude (Functor(..),Monad(..),Eq(..),Ord,Bool,Ordering,
                id,(.),($),undefined,seq)
import qualified Prelude

import Data.Vector.HFixed.Class hiding (cons,consF)
import qualified Data.Vector.Fixed          as F
import qualified Data.Vector.HFixed.Cont    as C


----------------------------------------------------------------
-- Generic API
----------------------------------------------------------------

-- | Restrict type of vector to 'ContVec'. This function is useful for
--   resolving type ambiguity when composing functions. For example
--   following code would not compile because intermediate type is
--   ambiguous:
--
-- > cons 'a' . tail
--
--   GHC cannot guess what type should be produced by @tail@. However
--   we can fix type of intermediate vector with @asCVec@, so code
--   below will work just fine:
--
-- > cons 'a' . asCVec . tail
asCVec :: ContVec xs -> ContVec xs
asCVec = id

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

-- | Prepend element to the list. Note that it changes type of vector
--   so it either must be known from context of specified explicitly
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

-- | Type changing Twan van Laarhoven's lens for i'th element.
elementCh :: ( Index n (Elems v)
             , a ~ ValueAt n (Elems v)
             , HVector v
             , HVector w
             , Elems w ~ NewElems n (Elems v) b
             , Functor f)
          => n -> (a -> f b) -> (v -> f w)
{-# INLINE elementCh #-}
elementCh n f v = inspect v
                $ lensChF n f construct

-- | Twan van Laarhoven's lens for i'th element. GHC >= 7.8
elementTy :: forall n a f v proxy.
             ( Index   (ToPeano n) (Elems v)
             , ValueAt (ToPeano n) (Elems v) ~ a
             , NatIso  (ToPeano n) n
             , HVector v
             , Functor f)
          => proxy n -> (a -> f a) -> (v -> f v)
{-# INLINE elementTy #-}
elementTy _ = element (undefined :: ToPeano n)

-- | Type changing Twan van Laarhoven's lens for i'th element.
elementChTy :: forall a b f n v w proxy.
               ( Index (ToPeano n) (Elems v)
               , a ~ ValueAt (ToPeano n) (Elems v)
               , HVector v
               , HVector w
               , Elems w ~ NewElems (ToPeano n) (Elems v) b
               , Functor f)
            => proxy n -> (a -> f b) -> (v -> f w)
{-# INLINE elementChTy #-}
elementChTy _ = elementCh (undefined :: ToPeano n)



----------------------------------------------------------------
-- Folds over vector
----------------------------------------------------------------

-- | Most generic form of fold which doesn't constrain elements id use
--   of 'inspect'. Or in more convenient form below:
--
-- >>> fold (12::Int,"Str") (\a s -> show a ++ s)
-- "12Str"
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

-- | Replicate polymorphic value n times. Concrete instance for every
--   element is determined by their respective types.
--
-- >>> import Data.Vector.HFixed as H
-- >>> H.replicate (Proxy :: Proxy Monoid) mempty :: ((),String)
-- ((),"")
replicate :: (HVector v, ArityC c (Elems v))
          => Proxy c -> (forall x. c x => x) -> v
{-# INLINE replicate #-}
replicate c x = C.vector $ C.replicate c x

-- | Replicate monadic action n times.
--
-- >>> import Data.Vector.HFixed as H
-- >>> H.replicateM (Proxy :: Proxy Read) (fmap read getLine) :: IO (Int,Char)
-- > 12
-- > 'a'
-- (12,'a')
replicateM :: (HVector v, Monad m, ArityC c (Elems v))
           => Proxy c -> (forall x. c x => m x) -> m v
{-# INLINE replicateM #-}
replicateM c x = liftM C.vector $ C.replicateM c x

replicateF :: (HVectorF v, Arity (ElemsF v))
           => (forall a. f a) -> v f
{-# INLINE replicateF #-}
replicateF x = C.vectorF $ C.replicateF x


-- | Unfold vector.
unfoldr :: (HVector v, ArityC c (Elems v))
        => Proxy c -> (forall a. c a => b -> (a,b)) -> b -> v
{-# INLINE unfoldr #-}
unfoldr c f b0 = C.vector $ C.unfoldr c f b0

-- | Zip two heterogeneous vectors
zipMono :: (HVector v, ArityC c (Elems v))
        => Proxy c -> (forall a. c a => a -> a -> a) -> v -> v -> v
{-# INLINE zipMono #-}
zipMono c f v u
  = C.vector $ C.zipMono c f (C.cvec v) (C.cvec u)

-- | Zip two heterogeneous vectors
zipMonoF :: (HVectorF v, ArityC c (ElemsF v))
         => Proxy c -> (forall a. c a => f a -> g a -> h a) -> v f -> v g -> v h
{-# INLINE zipMonoF #-}
zipMonoF c f v u
  = C.vectorF $ C.zipMonoF c f (C.cvecF v) (C.cvecF u)

zipFold :: (HVector v, ArityC c (Elems v), Monoid m)
        => Proxy c -> (forall a. c a => a -> a -> m) -> v -> v -> m
{-# INLINE zipFold #-}
zipFold c f v u
  = C.zipFold c f (C.cvec v) (C.cvec u)

-- | Convert heterogeneous vector to homogeneous
monomorphize :: (HVector v, ArityC c (Elems v))
             => Proxy c -> (forall a. c a => a -> x)
             -> v -> F.ContVec (Len (Elems v)) x
{-# INLINE monomorphize #-}
monomorphize c f = C.monomorphize c f . C.cvec

-- | Convert heterogeneous vector to homogeneous
monomorphizeF :: (HVectorF v, ArityC c (ElemsF v))
             => Proxy c -> (forall a. c a => f a -> x)
             -> v f -> F.ContVec (Len (ElemsF v)) x
{-# INLINE monomorphizeF #-}
monomorphizeF c f = C.monomorphizeF c f . C.cvecF


-- | Generic equality for heterogeneous vectors
eq :: (HVector v, ArityC Eq (Elems v)) => v -> v -> Bool
eq v u = getAll $ zipFold (Proxy :: Proxy Eq) (\x y -> All (x == y)) v u
{-# INLINE eq #-}

-- | Generic comparison for heterogeneous vectors
compare :: (HVector v, ArityC Ord (Elems v)) => v -> v -> Ordering
compare = zipFold (Proxy :: Proxy Ord) Prelude.compare
{-# INLINE compare #-}

-- | Reduce vector to normal form
rnf :: (HVector v, ArityC NF.NFData (Elems v)) => v -> ()
rnf = foldl (Proxy :: Proxy NF.NFData) (\r a -> NF.rnf a `seq` r) ()
{-# INLINE rnf #-}
