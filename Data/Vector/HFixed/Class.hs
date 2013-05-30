{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE PolyKinds             #-}
module Data.Vector.HFixed.Class (
    -- * Type class
    Fn
  , Fun(..)
  , HVector(..)
    -- * Operations of Fun
  , ConstF(..)
  , Curry(..)
  , Concat(..)
    -- * Isomorphism between types
  , Iso(..)
  ) where

import Data.Complex (Complex(..))
import Data.Vector.Fixed.Internal.Arity (Z)

import GHC.Generics
import GHC.TypeLits

import Data.Vector.HFixed.TypeList (Proxy(..),(++)())



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
--
-- Default implementation which uses 'Generic' is provided.
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
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}


----------------------------------------------------------------
-- Operations on Fun
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

-- | Type class for concatenation of vectors.
class Concat (xs :: [*]) (ys :: [*]) where
  concatF :: (a -> b -> c) -> Fun xs a -> Fun ys b -> Fun (xs ++ ys) c

instance Concat '[] '[] where
  concatF f (Fun a) (Fun b) = Fun (f a b)
instance Concat '[] xs => Concat '[] (x ': xs) where
  concatF f fa (Fun fb) = Fun $ \x -> unFun (concatF f fa (Fun (fb x) `asFunXS` (Proxy :: Proxy xs)))
instance Concat xs ys => Concat (x ': xs) ys where
  concatF f (Fun fa) fb = Fun $ \x -> unFun (concatF f (Fun (fa x) `asFunXS` (Proxy :: Proxy xs)) fb)


-- | Curry first /n/ arguments of N-ary function.
class Curry (xs :: [*]) (ys :: [*]) where
  curryF :: Fun (xs ++ ys) r -> Fun xs (Fun ys r)

instance Curry '[] ys where
  curryF f = Fun f

instance (Curry xs ys) => Curry (x ': xs) ys where
  curryF (Fun f :: Fun (x ': (xs ++ ys)) r)
    = Fun (\x -> unFun (curryF (Fun (f x) :: Fun (xs ++ ys) r) :: Fun xs (Fun ys r)))

asFunXS :: Fun xs r -> Proxy xs -> Fun xs r
asFunXS f _ = f



----------------------------------------------------------------
-- Instances
----------------------------------------------------------------

-- | Unit is empty heterogeneous vector
instance HVector () where
  type Elems () = '[]
  construct = Fun ()
  inspect () (Fun f) = f

instance HVector (Complex a) where
  type Elems (Complex a) = '[a,a]
  construct = Fun (:+)
  inspect (r :+ i) (Fun f) = f r i
  {-# INLINE construct #-}
  {-# INLINE inspect   #-}

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
-- Isomorphism
----------------------------------------------------------------

class (ToIso a ~ b, FromIso b ~ a) => Iso (a :: α) (b :: β) where
  type ToIso   a :: β
  type FromIso b :: α

instance Iso Z (0 :: Nat) where
  type ToIso   Z = 0
  type FromIso 0 = Z

-- Instances for numbers greater than 0 are omitted since there's
-- no induction on Nats in GHC7.6


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


instance ( GHVector f, GHVector g
         , Concat xs ys
         , Curry xs ys
         , GElems f ~ xs
         , GElems g ~ ys
         ) => GHVector (f :*: g) where
  type GElems (f :*: g) = GElems f ++ GElems g

  gconstruct = concatF (:*:) gconstruct gconstruct
  ginspect (f :*: g) fun
    = ginspect g $ ginspect f $ curryF fun
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
