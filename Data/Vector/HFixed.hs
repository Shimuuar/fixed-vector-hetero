{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
-- |
-- Heterogeneous vectors.
module Data.Vector.HFixed (
    -- * HVector type classes
    Arity
  , ArityC
  , HVector(..)
  , tupleSize
  , HVectorF(..)
  , tupleSizeF
  , Proxy(..)
  , ContVec
  , ContVecF(..)
  , asCVec
  , asCVecF
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
  , foldrF
  , foldlF
  , foldrNatF
  , foldlNatF
  , mapM_
  , unfoldr
  , unfoldrF
    -- ** Replicate variants
  , replicate
  , replicateM
  , replicateF
  , replicateNatF
    -- ** Zip variants
  , zipWith
  , zipWithF
  , zipWithNatF
  , zipFold
  , zipFoldF
  , monomorphize
  , monomorphizeF
    -- ** Tuples parametrized with type constructor
  , map
  , mapNat
  , sequence
  , sequence_
  , sequenceF
  , wrap
  , unwrap
  , distribute
  , distributeF
    -- * Specialized operations
  , eq
  , compare
  , rnf
  ) where

import Control.Applicative  (Applicative(..),(<$>))
import qualified Control.DeepSeq as NF

import Data.Coerce           (coerce)
import Data.Functor.Compose  (Compose(..))
import Data.Functor.Identity (Identity(..))
import Data.Monoid           (Monoid,All(..))
import Prelude ( Functor(..),Eq(..),Ord,Bool,Ordering
               , id,(.),($),seq)
import qualified Prelude

import           Data.Vector.HFixed.Class hiding (cons,consF)
import           Data.Vector.Fixed.Cont       (Peano)
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

asCVecF :: ContVecF f xs -> ContVecF f xs
asCVecF = id

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
tail :: (HVector v, HVector w, (a : Elems w) ~ Elems v)
     => v -> w
{-# INLINE tail #-}
tail = C.vector . C.tail . C.cvec


-- | Head of the vector
head :: (HVector v, Elems v ~ (a : as), Arity as)
     => v -> a
{-# INLINE head #-}
head = C.head . C.cvec

-- | Prepend element to the list. Note that it changes type of vector
--   so it either must be known from context of specified explicitly
cons :: (HVector v, HVector w, Elems w ~ (a : Elems v))
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
index :: (Index n (Elems v), HVector v) => v -> proxy n -> ValueAt n (Elems v)
{-# INLINE index #-}
index = C.index . C.cvec

-- | Set element in the vector
set :: (Index n (Elems v), HVector v)
       => proxy n -> ValueAt n (Elems v) -> v -> v
{-# INLINE set #-}
set n x = C.vector
        . C.set n x
        . C.cvec

-- | Twan van Laarhoven's lens for i'th element.
element :: forall n v a f proxy.
           ( Index   (Peano n) (Elems v)
           , ValueAt (Peano n) (Elems v) ~ a
           , HVector v
           , Functor f
           )
        => proxy n -> (a -> f a) -> (v -> f v)
{-# INLINE element #-}
element _ f v = inspect v
              $ lensF (Proxy @ (Peano n)) f construct

-- | Type changing Twan van Laarhoven's lens for i'th element.
elementCh :: forall n v w a b f proxy.
             ( Index   (Peano n) (Elems v)
             , ValueAt (Peano n) (Elems v) ~ a
             , HVector v
             , HVector w
             , Elems w ~ NewElems (Peano n) (Elems v) b
             , Functor f
             )
          => proxy n -> (a -> f b) -> (v -> f w)
{-# INLINE elementCh #-}
elementCh _ f v = inspect v
                $ lensChF (Proxy @ (Peano n)) f construct



----------------------------------------------------------------
-- Folds over vector
----------------------------------------------------------------

-- | Most generic form of fold which doesn't constrain elements id use
--   of 'inspect'. Or in more convenient form below:
--
-- >>> fold (12::Int,"Str") (\a s -> show a ++ s)
-- "12Str"
fold :: HVector v => v -> Fn Identity (Elems v) r -> r
-- FIXME: Not really useable
fold v f = inspect v (TFun f)
{-# INLINE fold #-}

-- | Right fold over heterogeneous vector
foldr :: (HVector v, ArityC c (Elems v))
      => Proxy c -> (forall a. c a => a -> b -> b) -> b -> v -> b
{-# INLINE foldr #-}
foldr c f b0 = C.foldrF c (\(Identity a) b -> f a b) b0 . C.cvec

-- | Left fold over heterogeneous vector
foldl :: (HVector v, ArityC c (Elems v))
      => Proxy c -> (forall a. c a => b -> a -> b) -> b -> v -> b
{-# INLINE foldl #-}
foldl c f b0 = C.foldlF c (\b (Identity a) -> f b a) b0 . C.cvec

-- | Right fold over heterogeneous vector
foldrF :: (HVectorF v, ArityC c (ElemsF v))
       => Proxy c -> (forall a. c a => f a -> b -> b) -> b -> v f -> b
{-# INLINE foldrF #-}
foldrF c f b0 = C.foldrF c f b0 . C.cvecF

-- | Left fold over heterogeneous vector
foldlF :: (HVectorF v, ArityC c (ElemsF v))
       => Proxy c -> (forall a. c a => b -> f a -> b) -> b -> v f -> b
{-# INLINE foldlF #-}
foldlF c f b0 = C.foldlF c f b0 . C.cvecF

-- | Right fold over heterogeneous vector
foldrNatF :: (HVectorF v)
          => (forall a. f a -> b -> b) -> b -> v f -> b
{-# INLINE foldrNatF #-}
foldrNatF f b0 = C.foldrNatF f b0 . C.cvecF

-- | Left fold over heterogeneous vector
foldlNatF :: (HVectorF v)
          => (forall a. b -> f a -> b) -> b -> v f -> b
{-# INLINE foldlNatF #-}
foldlNatF f b0 = C.foldlNatF f b0 . C.cvecF

-- | Apply monadic action to every element in the vector
mapM_ :: (HVector v, ArityC c (Elems v), Applicative f)
      => Proxy c -> (forall a. c a => a -> f ()) -> v -> f ()
{-# INLINE mapM_ #-}
mapM_ c f = foldl c (\m a -> m *> f a) (pure ())

-- | Unfold vector.
unfoldr :: (HVector v, ArityC c (Elems v))
        => Proxy c -> (forall a. c a => b -> (a,b)) -> b -> v
{-# INLINE unfoldr #-}
unfoldr c f = C.vector . C.unfoldrF c (\b -> let (a,b') = f b in (Identity a, b'))

-- | Unfold vector.
unfoldrF :: (HVectorF v, ArityC c (ElemsF v))
        => Proxy c -> (forall a. c a => b -> (f a,b)) -> b -> v f
{-# INLINE unfoldrF #-}
unfoldrF c f = C.vectorF . C.unfoldrF c f



----------------------------------------------------------------
-- Constructors
----------------------------------------------------------------

mk0 :: forall v. (HVector v, Elems v ~ '[]) => v
mk0 = coerce (construct :: Fun '[] v)
{-# INLINE mk0 #-}

mk1 :: forall v a. (HVector v, Elems v ~ '[a])
    => a -> v
mk1 = coerce (construct :: Fun '[a] v)
{-# INLINE mk1 #-}

mk2 :: forall v a b. (HVector v, Elems v ~ '[a,b])
    => a -> b -> v
mk2 = coerce (construct :: Fun '[a,b] v)
{-# INLINE mk2 #-}

mk3 :: forall v a b c. (HVector v, Elems v ~ '[a,b,c])
    => a -> b -> c -> v
mk3 = coerce (construct :: Fun '[a,b,c] v)
{-# INLINE mk3 #-}

mk4 :: forall v a b c d. (HVector v, Elems v ~ '[a,b,c,d])
    => a -> b -> c -> d -> v
mk4 = coerce (construct :: Fun '[a,b,c,d] v)
{-# INLINE mk4 #-}

mk5 :: forall v a b c d e. (HVector v, Elems v ~ '[a,b,c,d,e])
    => a -> b -> c -> d -> e -> v
mk5 = coerce (construct :: Fun '[a,b,c,d,e] v)
{-# INLINE mk5 #-}



----------------------------------------------------------------
-- Collective operations
----------------------------------------------------------------

-- | Apply natural transformation to every element of the tuple.
map :: (HVectorF v, ArityC c (ElemsF v))
    => Proxy c -> (forall a. c a => f a -> g a) -> v f -> v g
{-# INLINE map #-}
map cls f = C.vectorF . C.map cls f . C.cvecF

-- | Apply natural transformation to every element of the tuple.
mapNat :: (HVectorF v)
           => (forall a. f a -> g a) -> v f -> v g
{-# INLINE mapNat #-}
mapNat f = C.vectorF . C.mapNat f . C.cvecF

-- | Sequence effects for every element in the vector
sequence
  :: ( Applicative f, HVectorF v, HVector w, ElemsF v ~ Elems w )
  => v f -> f w
{-# INLINE sequence #-}
sequence
  = fmap C.vector
  . C.sequenceF
  . C.mapNat (Compose . fmap Identity)
  . C.cvecF

-- | Sequence effects for every element in the vector
sequence_ :: (Applicative f, HVectorF v) => v f -> f ()
{-# INLINE sequence_ #-}
sequence_ = foldlNatF (\m a -> m <* a) (pure ())

-- | Sequence effects for every element in the vector
sequenceF :: ( Applicative f, HVectorF v) => v (f `Compose` g) -> f (v g)
{-# INLINE sequenceF #-}
sequenceF v = C.vectorF <$> C.sequenceF (C.cvecF v)

-- | Wrap every value in the vector into type constructor.
wrap :: ( HVector v, HVectorF w, Elems v ~ ElemsF w )
     => (forall a. a -> f a) -> v -> w f
{-# INLINE wrap #-}
wrap f = C.vectorF . C.mapNat (f . runIdentity) . C.cvec

-- | Unwrap every value in the vector from the type constructor.
unwrap :: ( HVectorF v, HVector w, ElemsF v ~ Elems w )
       => (forall a. f a -> a) -> v f -> w
{-# INLINE unwrap #-}
unwrap  f = C.vector . C.mapNat (Identity . f) . C.cvecF

-- | Analog of /distribute/ from /Distributive/ type class.
distribute
  :: ( Functor f, HVector v, HVectorF w,  Elems v ~ ElemsF w )
  => f v -> w f
{-# INLINE distribute #-}
distribute
  = C.vectorF
  . mapNat (fmap runIdentity . getCompose)
  . C.distributeF
  . fmap C.cvec

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
replicate c x = C.vector $ C.replicateF c (Identity x)

-- | Replicate monadic action n times.
--
-- >>> import Data.Vector.HFixed as H
-- >>> H.replicateM (Proxy :: Proxy Read) (fmap read getLine) :: IO (Int,Char)
-- > 12
-- > 'a'
-- (12,'a')
replicateM :: (HVector v, Applicative f, ArityC c (Elems v))
           => Proxy c -> (forall a. c a => f a) -> f v
{-# INLINE replicateM #-}
replicateM c x
  = fmap C.vector
  $ C.sequenceF
  $ C.replicateF c (Compose $ fmap Identity x)

replicateNatF :: (HVectorF v, Arity (ElemsF v))
           => (forall a. f a) -> v f
{-# INLINE replicateNatF #-}
replicateNatF x = C.vectorF $ C.replicateNatF x

replicateF :: (HVectorF v, ArityC c (ElemsF v))
            => Proxy c -> (forall a. c a => f a) -> v f
{-# INLINE replicateF #-}
replicateF c x = C.vectorF $ C.replicateF c x



----------------------------------------------------------------
-- Zipping of vectors
----------------------------------------------------------------

-- | Zip two heterogeneous vectors
zipWith :: (HVector v, ArityC c (Elems v))
        => Proxy c -> (forall a. c a => a -> a -> a) -> v -> v -> v
{-# INLINE zipWith #-}
zipWith c f v u
  = C.vector
  $ C.zipWithF c (\(Identity a) (Identity b) -> Identity (f a b)) (C.cvec v) (C.cvec u)

-- | Zip two heterogeneous vectors
zipWithF :: (HVectorF v, ArityC c (ElemsF v))
         => Proxy c -> (forall a. c a => f a -> g a -> h a) -> v f -> v g -> v h
{-# INLINE zipWithF #-}
zipWithF c f v u
  = C.vectorF $ C.zipWithF c f (C.cvecF v) (C.cvecF u)

-- | Zip two heterogeneous vectors
zipWithNatF :: (HVectorF v)
        => (forall a. f a -> g a -> h a) -> v f -> v g -> v h
{-# INLINE zipWithNatF #-}
zipWithNatF f v u
  = C.vectorF $ C.zipWithNatF f (C.cvecF v) (C.cvecF u)

zipFold :: (HVector v, ArityC c (Elems v), Monoid m)
        => Proxy c -> (forall a. c a => a -> a -> m) -> v -> v -> m
{-# INLINE zipFold #-}
zipFold c f v u
  = C.zipFoldF c (\(Identity a) (Identity b) -> f a b) (C.cvec v) (C.cvec u)

zipFoldF :: (HVectorF v, ArityC c (ElemsF v), Monoid m)
        => Proxy c -> (forall a. c a => f a -> f a -> m) -> v f -> v f -> m
{-# INLINE zipFoldF #-}
zipFoldF c f v u
  = C.zipFoldF c f (C.cvecF v) (C.cvecF u)

-- | Convert heterogeneous vector to homogeneous
monomorphize :: ( HVector v
                , Peano n ~ Len (Elems v)
                , ArityC c (Elems v))
             => Proxy c -> (forall a. c a => a -> x)
             -> v -> F.ContVec n x
{-# INLINE monomorphize #-}
monomorphize c f = C.monomorphizeF c (f . runIdentity) . C.cvec

-- | Convert heterogeneous vector to homogeneous
monomorphizeF :: ( HVectorF v
                 , Peano n ~ Len (ElemsF v)
                 , ArityC c (ElemsF v)
                 )
             => Proxy c -> (forall a. c a => f a -> x)
             -> v f -> F.ContVec n x
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
