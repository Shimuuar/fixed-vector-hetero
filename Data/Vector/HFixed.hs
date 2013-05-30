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
    -- ** Indexing
  , IdxVal
  , Index(..)
  , index
  , set
  , element
    -- * Folds
  , Foldr(..)
  , hfoldr
    -- ** Unfold
  , Unfoldr(..)
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
  , HomElems
  , homConstruct
  , homInspect
  , hvecToVec
  ) where

import Control.Applicative     (Applicative(..))
import GHC.Prim                (Constraint)
import GHC.TypeLits
import Prelude hiding (head,tail,concat)

import qualified Data.Vector.Fixed                as F
import qualified Data.Vector.Fixed.Internal.Arity as F
-- import qualified Data.Vector.Fixed.Unboxed        as U
-- import qualified Data.Vector.Fixed.Primitive      as P
-- import qualified Data.Vector.Fixed.Storable       as S
-- import qualified Data.Vector.Fixed.Boxed          as B

import Data.Vector.HFixed.TypeList
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

-- | Type of element at position @N@
type family IdxVal (n :: Nat) (xs :: [*]) :: *

-- | Indexing of heterogeneous vector.
--
-- It seems that it's not possible define instances recursively with
-- GHC7.6 so they are defined up to some arbitrary limit.
class Index (n :: Nat) (xs :: [*]) where
  indexF :: Sing n -> Fun xs (IdxVal n xs)
  setF   :: Sing n -> IdxVal n xs -> Fun xs r -> Fun xs r


-- | Index heterogeneous vector
index :: (Index n (Elems v), HVector v) => v -> Sing n -> IdxVal n (Elems v)
{-# INLINE index #-}
index v n = inspect v (indexF n)

-- | Set element in the vector
set :: (Index n (Elems v), HVector v)
       => Sing n -> IdxVal n (Elems v) -> v -> v
{-# INLINE set #-}
set n x v = inspect v
          $ setF n x
          $ construct

-- | Twan van Laarhoven's lens for i'th element.
element :: (Index n (Elems v), IdxVal n (Elems v) ~ a, HVector v, Functor f)
        => Sing n -> (a -> f a) -> (v -> f v)
{-# INLINE element #-}
element n f v = (\a -> set n a v) `fmap` f (index v n)


-- GHC 7.6 cannot unify type level arithmetics so instances up to 19
-- are provided explicitly
--
-- Recursion base
type instance IdxVal 0 (x ': xs) = x
instance Arity xs => Index 0 (x ': xs) where
  indexF  _ = Fun $ (\x -> unFun (pure x :: Fun xs x))
  setF _ x (Fun f) = Fun $ \_ -> f x
-- Recursion step. Since GHC 7.6 cannot unify type level arithmetics
-- instances up to 20 are hardcoded
type instance IdxVal 1 (x ': xs) = IdxVal 0 xs
instance Index 0 xs => Index 1 (x ': xs) where
  indexF  _ = Fun $ (\_ -> unFun (indexF (sing :: Sing 0) :: Fun xs (IdxVal 0 xs)))
  setF _ x (Fun f :: Fun (x ': xs) r)
    = Fun $ \a -> unFun $ setF (sing :: Sing 0) x (Fun (f a) :: Fun xs r)

type instance IdxVal 2 (x ': xs) = IdxVal 1 xs
instance Index 1 xs => Index 2 (x ': xs) where
  indexF  _ = Fun $ (\_ -> unFun (indexF (sing :: Sing 1) :: Fun xs (IdxVal 1 xs)))
  setF _ x (Fun f :: Fun (x ': xs) r)
    = Fun $ \a -> unFun $ setF (sing :: Sing 1) x (Fun (f a) :: Fun xs r)

type instance IdxVal 3 (x ': xs) = IdxVal 2 xs
instance Index 2 xs => Index 3 (x ': xs) where
  indexF  _ = Fun $ (\_ -> unFun (indexF (sing :: Sing 2) :: Fun xs (IdxVal 2 xs)))
  setF _ x (Fun f :: Fun (x ': xs) r)
    = Fun $ \a -> unFun $ setF (sing :: Sing 2) x (Fun (f a) :: Fun xs r)

type instance IdxVal 4 (x ': xs) = IdxVal 3 xs
instance Index 3 xs => Index 4 (x ': xs) where
  indexF  _ = Fun $ (\_ -> unFun (indexF (sing :: Sing 3) :: Fun xs (IdxVal 3 xs)))
  setF _ x (Fun f :: Fun (x ': xs) r)
    = Fun $ \a -> unFun $ setF (sing :: Sing 3) x (Fun (f a) :: Fun xs r)

type instance IdxVal 5 (x ': xs) = IdxVal 4 xs
instance Index 4 xs => Index 5 (x ': xs) where
  indexF  _ = Fun $ (\_ -> unFun (indexF (sing :: Sing 4) :: Fun xs (IdxVal 4 xs)))
  setF _ x (Fun f :: Fun (x ': xs) r)
    = Fun $ \a -> unFun $ setF (sing :: Sing 4) x (Fun (f a) :: Fun xs r)

type instance IdxVal 6 (x ': xs) = IdxVal 5 xs
instance Index 5 xs => Index 6 (x ': xs) where
  indexF  _ = Fun $ (\_ -> unFun (indexF (sing :: Sing 5) :: Fun xs (IdxVal 5 xs)))
  setF _ x (Fun f :: Fun (x ': xs) r)
    = Fun $ \a -> unFun $ setF (sing :: Sing 5) x (Fun (f a) :: Fun xs r)

type instance IdxVal 7 (x ': xs) = IdxVal 6 xs
instance Index 6 xs => Index 7 (x ': xs) where
  indexF  _ = Fun $ (\_ -> unFun (indexF (sing :: Sing 6) :: Fun xs (IdxVal 6 xs)))
  setF _ x (Fun f :: Fun (x ': xs) r)
    = Fun $ \a -> unFun $ setF (sing :: Sing 6) x (Fun (f a) :: Fun xs r)

type instance IdxVal 8 (x ': xs) = IdxVal 7 xs
instance Index 7 xs => Index 8 (x ': xs) where
  indexF  _ = Fun $ (\_ -> unFun (indexF (sing :: Sing 7) :: Fun xs (IdxVal 7 xs)))
  setF _ x (Fun f :: Fun (x ': xs) r)
    = Fun $ \a -> unFun $ setF (sing :: Sing 7) x (Fun (f a) :: Fun xs r)

type instance IdxVal 9 (x ': xs) = IdxVal 8 xs
instance Index 8 xs => Index 9 (x ': xs) where
  indexF  _ = Fun $ (\_ -> unFun (indexF (sing :: Sing 8) :: Fun xs (IdxVal 8 xs)))
  setF _ x (Fun f :: Fun (x ': xs) r)
    = Fun $ \a -> unFun $ setF (sing :: Sing 8) x (Fun (f a) :: Fun xs r)

type instance IdxVal 10 (x ': xs) = IdxVal 9 xs
instance Index 9 xs => Index 10 (x ': xs) where
  indexF  _ = Fun $ (\_ -> unFun (indexF (sing :: Sing 9) :: Fun xs (IdxVal 9 xs)))
  setF _ x (Fun f :: Fun (x ': xs) r)
    = Fun $ \a -> unFun $ setF (sing :: Sing 9) x (Fun (f a) :: Fun xs r)

type instance IdxVal 11 (x ': xs) = IdxVal 10 xs
instance Index 10 xs => Index 11 (x ': xs) where
  indexF  _ = Fun $ (\_ -> unFun (indexF (sing :: Sing 10) :: Fun xs (IdxVal 10 xs)))
  setF _ x (Fun f :: Fun (x ': xs) r)
    = Fun $ \a -> unFun $ setF (sing :: Sing 10) x (Fun (f a) :: Fun xs r)

type instance IdxVal 12 (x ': xs) = IdxVal 11 xs
instance Index 11 xs => Index 12 (x ': xs) where
  indexF  _ = Fun $ (\_ -> unFun (indexF (sing :: Sing 11) :: Fun xs (IdxVal 11 xs)))
  setF _ x (Fun f :: Fun (x ': xs) r)
    = Fun $ \a -> unFun $ setF (sing :: Sing 11) x (Fun (f a) :: Fun xs r)

type instance IdxVal 13 (x ': xs) = IdxVal 12 xs
instance Index 12 xs => Index 13 (x ': xs) where
  indexF  _ = Fun $ (\_ -> unFun (indexF (sing :: Sing 12) :: Fun xs (IdxVal 12 xs)))
  setF _ x (Fun f :: Fun (x ': xs) r)
    = Fun $ \a -> unFun $ setF (sing :: Sing 12) x (Fun (f a) :: Fun xs r)

type instance IdxVal 14 (x ': xs) = IdxVal 13 xs
instance Index 13 xs => Index 14 (x ': xs) where
  indexF  _ = Fun $ (\_ -> unFun (indexF (sing :: Sing 13) :: Fun xs (IdxVal 13 xs)))
  setF _ x (Fun f :: Fun (x ': xs) r)
    = Fun $ \a -> unFun $ setF (sing :: Sing 13) x (Fun (f a) :: Fun xs r)

type instance IdxVal 15 (x ': xs) = IdxVal 14 xs
instance Index 14 xs => Index 15 (x ': xs) where
  indexF  _ = Fun $ (\_ -> unFun (indexF (sing :: Sing 14) :: Fun xs (IdxVal 14 xs)))
  setF _ x (Fun f :: Fun (x ': xs) r)
    = Fun $ \a -> unFun $ setF (sing :: Sing 14) x (Fun (f a) :: Fun xs r)

type instance IdxVal 16 (x ': xs) = IdxVal 15 xs
instance Index 15 xs => Index 16 (x ': xs) where
  indexF  _ = Fun $ (\_ -> unFun (indexF (sing :: Sing 15) :: Fun xs (IdxVal 15 xs)))
  setF _ x (Fun f :: Fun (x ': xs) r)
    = Fun $ \a -> unFun $ setF (sing :: Sing 15) x (Fun (f a) :: Fun xs r)

type instance IdxVal 17 (x ': xs) = IdxVal 16 xs
instance Index 16 xs => Index 17 (x ': xs) where
  indexF  _ = Fun $ (\_ -> unFun (indexF (sing :: Sing 16) :: Fun xs (IdxVal 16 xs)))
  setF _ x (Fun f :: Fun (x ': xs) r)
    = Fun $ \a -> unFun $ setF (sing :: Sing 16) x (Fun (f a) :: Fun xs r)

type instance IdxVal 18 (x ': xs) = IdxVal 17 xs
instance Index 17 xs => Index 18 (x ': xs) where
  indexF  _ = Fun $ (\_ -> unFun (indexF (sing :: Sing 17) :: Fun xs (IdxVal 17 xs)))
  setF _ x (Fun f :: Fun (x ': xs) r)
    = Fun $ \a -> unFun $ setF (sing :: Sing 17) x (Fun (f a) :: Fun xs r)

type instance IdxVal 19 (x ': xs) = IdxVal 18 xs
instance Index 18 xs => Index 19 (x ': xs) where
  indexF  _ = Fun $ (\_ -> unFun (indexF (sing :: Sing 18) :: Fun xs (IdxVal 18 xs)))
  setF _ x (Fun f :: Fun (x ': xs) r)
    = Fun $ \a -> unFun $ setF (sing :: Sing 18) x (Fun (f a) :: Fun xs r)


----------------------------------------------------------------
-- Folds over vector
----------------------------------------------------------------

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

-- | Generic right fold
class Foldr (c :: * -> Constraint) (xs :: [*]) where
  hfoldrF :: Proxy c -> (forall a. c a => a -> b -> b) -> Fun xs (b -> b)

instance Foldr c '[] where
  hfoldrF _ _ = Fun id
instance (Foldr c xs, c x, Arity xs)  => Foldr c (x ': xs) where
  hfoldrF wit f
    = Fun $ \x -> unFun $ fmap ((f x) . ) (hfoldrF wit f `asFunXS` (Proxy :: Proxy xs))

asFunXS :: Fun xs r -> Proxy xs -> Fun xs r
asFunXS f _ = f



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

-- | Type class for unfolding heterogeneous vectors
class Unfoldr (c :: * -> Constraint) (xs :: [*]) where
  unforldrF :: Proxy c
            -> (forall a. c a => b -> (a,b))
            -> Fun xs r
            -> b
            -> r
  unforldrFM :: Monad m
             => Proxy c
             -> (forall a. c a => b -> m (a,b))
             -> Fun xs r
             -> b
             -> m r

instance Unfoldr c '[] where
  unforldrF  _ _ (Fun r) _ = r
  unforldrFM _ _ (Fun r) _ = return r

instance (Unfoldr c xs, c x) => Unfoldr c (x ': xs) where
  -- Simple unfold
  unforldrF wit step (Fun f) b
    = unforldrF wit step (Fun (f x) `asFunXS` (Proxy :: Proxy xs)) b'
    where
      (x,b') = step b
  -- Monadic unfold
  unforldrFM wit step (Fun f) b = do
    (x,b') <- step b
    unforldrFM wit step (Fun (f x) `asFunXS` (Proxy :: Proxy xs)) b'



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
-- Fixed vectors
----------------------------------------------------------------

-- | Elements for homogeneous vector @v a@.
type family   HomElems (v :: * -> *) (a :: *) :: [*]
type instance HomElems v a = HomElemsCase (F.Dim v) a

type family   HomElemsCase n a :: [*]
type instance HomElemsCase F.Z     a = '[]
type instance HomElemsCase (F.S n) a = a ': HomElemsCase n a

-- | Default implementation of 'inspect' for homogeneous vector.
homInspect
  :: forall v a r. ( F.Vector v a
                   , Fn (HomElems v a) r ~ F.Fn (F.Dim v) a r -- Tautology
                   )
  => v a -> Fun (HomElems v a) r -> r
{-# INLINE homInspect #-}
homInspect v (Fun f)
  = F.inspect v (F.Fun f :: F.Fun (F.Dim v) a r)

-- | Default implementation of 'construct' for homogeneous vectors.
homConstruct
  :: forall v a. ( F.Vector v a
                 , Fn (HomElems v a) (v a) ~ F.Fn (F.Dim v) a (v a) -- Tautology
                 )
  => Fun (HomElems v a) (v a)
{-# INLINE homConstruct #-}
homConstruct =
  case F.construct :: F.Fun (F.Dim v) a (v a) of
    F.Fun f -> Fun f

-- | Convert heterogeneous vector to homogeneous when possible.
hvecToVec :: forall v w a. ( HVector v, F.Vector w a
                           , Fn (Elems v) (w a) ~ F.Fn (F.Dim w) a (w a)
                           )
          => v -> w a
{-# INLINE hvecToVec #-}
hvecToVec v
  = inspect v
  $ (case F.construct :: F.Fun (F.Dim w) a (w a) of
       F.Fun f -> (Fun f :: Fun (Elems v) (w a))
    )
