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
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE InstanceSigs          #-}
module Data.Vector.HFixed (
    -- * Basic API
    Fn
  , Fun(..)
  , HVector(..)
    -- ** List length
  , Proxy(..)
  , ListLen(..)
    -- * Generic functions
  , convert
  , head
  , tail
  , cons
  , IdxVal
  , Index(..)
  , index
  , set
  , element
    -- ** Right fold
  , Foldr(..)
  , hfoldr
    -- * Generic constructors
  , mk0
  , mk1
  , mk2
  , mk3
  , mk4
  , mk5
  ) where

import GHC.Prim                (Constraint)
import GHC.TypeLits
import GHC.Generics
import Prelude hiding (head,tail)


----------------------------------------------------------------
-- Type classes
----------------------------------------------------------------

-- | Type family for N-ary function. Types of function parameters are
--   encoded as the list of types.
type family Fn (as ::[*]) b
type instance Fn '[]       b = b
type instance Fn (a ': as) b = a -> Fn as b


-- | Newtype wrapper to work around of type families' lack of
--   injectivity.
newtype Fun (as :: [*]) b = Fun { unFun :: Fn as b }

instance Functor (Fun '[]) where
  fmap f (Fun x) = Fun (f x)

instance Functor (Fun xs) => Functor (Fun (x ': xs)) where
  fmap (f :: a -> b) (Fun g)
    = Fun $ \a -> unFun $ fmap f (Fun (g a) :: Fun xs a)


-- | Type class for heterogeneous vectors. Instance should specify way
-- to construct and deconstruct itself
--
-- Note that this type class is extremely generic. Almost any single
-- constructor data type could be made instance. It could be
-- monomorphic, it could be polymorphic in some or all fields it
-- doesn't matter. Only law instance should obey is:
--
-- > inspect v construct = v
class HVector v where
  type Elems v :: [*]
  type Elems v = GElems (Rep v)
  --
  construct :: Fun (Elems v) v
  default construct :: (Generic v, GHVector (Rep v), GElems (Rep v) ~ Elems v, Functor (Fun (Elems v)))
                    => Fun (Elems v) v
  construct = fmap to gconstruct
  --
  inspect :: v -> Fun (Elems v) a -> a
  default inspect :: (Generic v, GHVector (Rep v), GElems (Rep v) ~ Elems v)
                  => v -> Fun (Elems v) a -> a
  inspect v = ginspect (from v)

data Proxy (a :: α) = Proxy

class ListLen (xs :: [*]) where
  listLen :: Proxy xs -> Int

instance ListLen '[] where
  listLen _ = 0
instance ListLen xs => ListLen (x ': xs) where
  listLen _ = 1 + listLen (Proxy :: Proxy xs)



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
tail :: forall a v w. (HVector v, HVector w, (a ': Elems w) ~ Elems v)
     => v -> w
{-# INLINE tail #-}
tail v = inspect v
       $ Fun $ const $ unFun (construct :: Fun (Elems w) w)

-- | Head of the vector
head :: forall a as v. (HVector v, Elems v ~ (a ': as), ConstF as)
     => v -> a
{-# INLINE head #-}
head v = inspect v
       $ Fun (\a -> unFun (constF a :: Fun as a))

-- | Prepend element to the list
cons :: forall a v w. (HVector v, HVector w, Elems w ~ (a ': Elems v))
     => a -> v -> w
{-# INLINE cons #-}
cons a v = inspect v
       $ Fun $ unFun (construct :: Fun (Elems w) w) a


-- | Type of element at position @N@
type family IdxVal (n :: Nat) (xs :: [*]) :: *

-- | Indexing of heterogeneous vector.
--
-- It seems that it's not possible define instances recursively with
-- GHC7.6 so they are defined up to some arbitrary limit.
class Index (n :: Nat) (xs :: [*]) where
  indexF  :: Sing n -> Fun xs (IdxVal n xs)
  setF :: Sing n -> IdxVal n xs -> Fun xs r -> Fun xs r

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

element :: (Index n (Elems v), IdxVal n (Elems v) ~ a, HVector v, Functor f)
        => Sing n -> (a -> f a) -> (v -> f v)
{-# INLINE element #-}
element n f v = (\a -> set n a v) `fmap` f (index v n)


-- Recursion base
type instance IdxVal 0 (x ': xs) = x
instance ConstF xs => Index 0 (x ': xs) where
  indexF  _ = Fun $ (\x -> unFun (constF x :: Fun xs x))
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
instance (Foldr c xs, c x, Functor (Fun xs))  => Foldr c (x ': xs) where
  hfoldrF wit f
    = Fun $ \x -> unFun $ fmap ((f x) . ) (hfoldrF wit f `asFunXS` (Proxy :: Proxy xs))

asFunXS :: Fun xs r -> Proxy xs -> Fun xs r
asFunXS f _ = f



----------------------------------------------------------------
-- Constructors
----------------------------------------------------------------

mk0 :: forall v. (HVector v, Elems v ~ '[]) => v
mk0 = unFun (construct :: Fun (Elems v) v)

mk1 :: forall v a. (HVector v, Elems v ~ '[a]) => a -> v
mk1 a = unFun (construct :: Fun (Elems v) v) a

mk2 :: forall v a b. (HVector v, Elems v ~ '[a,b]) => a -> b -> v
mk2 a b = unFun (construct :: Fun (Elems v) v) a b

mk3 :: forall v a b c. (HVector v, Elems v ~ '[a,b,c]) => a -> b -> c -> v
mk3 a b c = unFun (construct :: Fun (Elems v) v) a b c

mk4 :: forall v a b c d. (HVector v, Elems v ~ '[a,b,c,d]) => a -> b -> c -> d -> v
mk4 a b c d = unFun (construct :: Fun (Elems v) v) a b c d

mk5 :: forall v a b c d e. (HVector v, Elems v ~ '[a,b,c,d,e]) => a -> b -> c -> d -> e -> v
mk5 a b c d e = unFun (construct :: Fun (Elems v) v) a b c d e



----------------------------------------------------------------
-- Helpers
----------------------------------------------------------------

-- | Generalize 'const' function. This type class is total and have
--   instances for all possible types. It's however is impossible to
--   express so @ConstF@ constraint will pop up from time to time.
class ConstF (xs :: [*]) where
  constF :: a -> Fun xs a

instance ConstF '[] where
  constF = Fun
instance ConstF xs => ConstF (x ': xs) where
  constF (a :: a) = Fun $ \_ -> unFun (constF a :: Fun xs a)



----------------------------------------------------------------
-- * Instances
----------------------------------------------------------------

-- | Unit is empty heterogeneous vector
instance HVector () where
  type Elems () = '[]
  construct = Fun ()
  inspect () (Fun f) = f



instance HVector (a,b) where
  type Elems (a,b) = '[a,b]
  construct = Fun (,)
  inspect (a,b) (Fun f) = f a b
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c) where
  type Elems (a,b,c) = '[a,b,c]
  construct = Fun (,,)
  inspect (a,b,c) (Fun f) = f a b c
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d) where
  type Elems (a,b,c,d) = '[a,b,c,d]
  construct = Fun (,,,)
  inspect (a,b,c,d) (Fun f) = f a b c d
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d,e) where
  type Elems (a,b,c,d,e) = '[a,b,c,d,e]
  construct = Fun (,,,,)
  inspect (a,b,c,d,e) (Fun f) = f a b c d e
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d,e,f) where
  type Elems (a,b,c,d,e,f) = '[a,b,c,d,e,f]
  construct = Fun (,,,,,)
  inspect (a,b,c,d,e,f) (Fun fun) = fun a b c d e f
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

instance HVector (a,b,c,d,e,f,g) where
  type Elems (a,b,c,d,e,f,g) = '[a,b,c,d,e,f,g]
  construct = Fun (,,,,,,)
  inspect (a,b,c,d,e,f,g) (Fun fun) = fun a b c d e f g
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}



----------------------------------------------------------------
-- Generics
----------------------------------------------------------------

class GHVector v where
  type GElems v :: [*]
  gconstruct :: Fun (GElems v) (v p)
  ginspect   :: v p -> Fun (GElems v) r -> r


-- We simply skip metadata
instance (GHVector f, Functor (Fun (GElems f))) => GHVector (M1 i c f) where
  type GElems (M1 i c f) = GElems f
  gconstruct = fmap M1 gconstruct
  ginspect v = ginspect (unM1 v)
  {-# INLINE gconstruct #-}
  {-# INLINE ginspect   #-}


-- Recursion is a bit tricky. We have to assume that :*: is right
-- associative and unpack fields explicitly
instance (GHVector f, Functor (Fun (GElems f))) => GHVector (M1 S c (K1 R x) :*: f) where
  type GElems (M1 S c (K1 R x) :*: f) = x ': GElems f

  gconstruct :: forall p. Fun (GElems (M1 S c (K1 R x) :*: f))
                                     ((M1 S c (K1 R x) :*: f) p)
  gconstruct
    = Fun $ \a -> unFun $ upd a `fmap` gcon
    where
      -- Constructor for rest of the fields
      gcon :: Fun (GElems f) (f p)
      gcon = gconstruct
      -- Prepend field to data type
      upd :: x -> f p -> (M1 S c (K1 R x) :*: f) p
      upd a v = M1 (K1 a) :*: v

  ginspect (M1 (K1 a) :*: v) (Fun f)
    = ginspect v (Fun (f a))
  {-# INLINE gconstruct #-}
  {-# INLINE ginspect   #-}


-- Recursion is terminated by simple field
instance GHVector (K1 R x) where
  type GElems (K1 R x) = '[x]
  gconstruct = Fun K1
  ginspect (K1 x) (Fun f) = f x
  {-# INLINE gconstruct #-}
  {-# INLINE ginspect   #-}


-- Unit types are empty vectors
instance GHVector U1 where
  type GElems U1 = '[]
  gconstruct         = Fun U1
  ginspect _ (Fun f) = f
  {-# INLINE gconstruct #-}
  {-# INLINE ginspect   #-}
