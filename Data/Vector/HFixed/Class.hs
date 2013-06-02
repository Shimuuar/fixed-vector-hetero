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
{-# LANGUAGE RankNTypes            #-}
module Data.Vector.HFixed.Class (
    -- * Type class
    Fn
  , Fun(..)
  , Proxy(..)
  , Arity(..)
  , HVector(..)
  , (++)()
    -- * Operations of Fun
    -- ** Recursion primitives
  , apFun
  , constFun
  , stepFun
    -- ** More complicated functions
  , curryF
  , curry1
  , concatF
  , Uncurry(..)
  , Index(..)
    -- * Isomorphism between types
  , NatIso(..)
  ) where

import Control.Applicative (Applicative(..))
import Data.Complex        (Complex(..))
import Data.Vector.Fixed.Internal.Arity (S,Z)

import GHC.Generics hiding (Arity(..),S)
import GHC.TypeLits



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


-- | Kind polymorphic proxy.
data Proxy (a :: α) = Proxy


-- | Type class for dealing with N-ary function in generic way.
class Arity (xs :: [*]) where
  accum :: (forall a as. t (a ': as) -> a -> t as)
        -> (t '[] -> b)
        -> t xs
        -> Fn xs b
  apply :: (forall a as. t (a ': as) -> (a, t as))
        -> t xs
        -> Fn xs b
        -> b
  arity :: Proxy xs -> Int

instance Arity '[] where
  accum _ f t = f t
  apply _ _ b = b
  arity _     = 0
instance Arity xs => Arity (x ': xs) where
  accum f g t = \a -> accum f g (f t a)
  apply f t h = case f t of (a,u) -> apply f u (h a)
  arity _     = 1 + arity (Proxy :: Proxy xs)



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

-- | Concaternation of type level lists.
type family   (++) (xs :: [*]) (ys :: [*]) :: [*]
type instance (++) '[]       ys = ys
type instance (++) (x ': xs) ys = x ': xs ++ ys


----------------------------------------------------------------
-- Instances of Fun
----------------------------------------------------------------

instance (Arity xs) => Functor (Fun xs) where
  fmap (f :: a -> b) (Fun g0 :: Fun xs a)
    = Fun $ accum (\(T_fmap g) a -> T_fmap (g a))
                  (\(T_fmap r)   -> f r)
                  (T_fmap g0 :: T_fmap a xs)
  {-# INLINE fmap #-}

instance Arity xs => Applicative (Fun xs) where
  pure r = Fun $ accum (\T_pure _ -> T_pure)
                       (\T_pure   -> r)
                       (T_pure :: T_pure xs)
  (Fun f0 :: Fun xs (a -> b)) <*> (Fun g0 :: Fun xs a)
    = Fun $ accum (\(T_ap f g) a -> T_ap (f a) (g a))
                  (\(T_ap f g)   -> f g)
                  ( T_ap f0 g0 :: T_ap (a -> b) a xs)
  {-# INLINE pure  #-}
  {-# INLINE (<*>) #-}

newtype T_fmap a   xs = T_fmap (Fn xs a)
data    T_pure     xs = T_pure
data    T_ap   a b xs = T_ap (Fn xs a) (Fn xs b)



----------------------------------------------------------------
-- Operations on Fun
----------------------------------------------------------------

-- | Apply single parameter to function
apFun :: Fun (x ': xs) r -> x -> Fun xs r
apFun (Fun f) x = Fun (f x)
{-# INLINE apFun #-}

-- | Add one parameter to function which is ignored.
constFun :: Fun xs r -> Fun (x ': xs) r
constFun (Fun f) = Fun $ \_ -> f
{-# INLINE constFun #-}

stepFun :: (Fun xs a -> Fun ys b) -> Fun (x ': xs) a -> Fun (x ': ys) b
stepFun g f = Fun $ unFun . g . apFun f
{-# INLINE stepFun #-}

-- | Type class for concatenation of vectors.
-- class Concat (xs :: [*]) (ys :: [*]) where
concatF :: (Arity xs, Arity ys, Uncurry xs)
        => (a -> b -> c) -> Fun xs a -> Fun ys b -> Fun (xs ++ ys) c
{-# INLINE concatF #-}
concatF f funA funB = uncurryF $ fmap go funA
  where
    go a = fmap (\b -> f a b) funB

-- | Curry first /n/ arguments of N-ary function.
curryF :: forall xs ys r. Arity xs => Fun (xs ++ ys) r -> Fun xs (Fun ys r)
{-# INLINE curryF #-}
curryF (Fun f0)
  = Fun $ accum (\(T_curry f) a -> T_curry (f a))
                (\(T_curry f)   -> Fun f :: Fun ys r)
                (T_curry f0 :: T_curry r ys xs)

newtype T_curry r ys xs = T_curry (Fn (xs ++ ys) r)

-- | Curry single argument
curry1 :: Fun (x ': xs) r -> Fun '[x] (Fun xs r)
curry1 f = Fun $ apFun f



-- | Indexing of vectors
class Index (n :: *) (xs :: [*]) where
  type ValueAt n xs :: *
  -- | Getter function for vectors
  getF :: n -> Fun xs (ValueAt n xs)
  -- | Putter function. It applies value @x@ to @n@th parameter of
  --   function.
  putF :: n -> ValueAt n xs -> Fun xs r -> Fun xs r

instance Arity xs => Index Z (x ': xs) where
  type ValueAt Z (x ': xs) = x
  getF _     = Fun $ \x -> unFun (pure x :: Fun xs x)
  putF _ x f = constFun $ apFun f x

instance Index n xs => Index (S n) (x ': xs) where
  type ValueAt  (S n) (x ': xs) = ValueAt n xs
  getF _   = constFun $ getF (undefined :: n)
  putF _ x = stepFun (putF (undefined :: n) x)



----------------------------------------------------------------

-- | This type class is needed because I couldn't find way to write
--   @uncurryF@ in terms of 'Arity'. Thing boils down to necessity to
--   prove that
--
--  > @Fn (xs++ys) r ~ Fn xs (Fn ys r)@.
--
--  This is true. But there's no way to tell compiler this. If such
--  equality could be proven @uncurryF@ becomes trivial.
--
--  > uncurryF :: forall xs ys r. Fun xs (Fun ys r) -> Fun (xs ++ ys) r
--  > uncurryF f =
--  >   case fmap unFun f :: Fun xs (Fn ys r) of
--  >     Fun g -> Fun g
--
--  Implementation using @accum@ suffers from the same problem.
class Uncurry xs where
  uncurryF :: Fun xs (Fun ys r) -> Fun (xs ++ ys) r

instance Uncurry '[] where
  uncurryF = unFun
instance Uncurry xs => Uncurry (x ': xs) where
  uncurryF f = Fun $ unFun . uncurryF . apFun f







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

-- | Isomorphism between two representations of natural numbers
class (ToNat a ~ b, ToPeano b ~ a) => NatIso (a :: *) (b :: Nat) where
  type ToNat    a :: Nat
  type ToPeano b :: *

instance NatIso (Z) 0 where
  type ToNat (Z) = 0
  type ToPeano 0 = Z

instance NatIso (S (Z)) 1 where
  type ToNat (S (Z)) = 1
  type ToPeano 1 = S (Z)

instance NatIso (S (S (Z))) 2 where
  type ToNat (S (S (Z))) = 2
  type ToPeano 2 = S (S (Z))

instance NatIso (S (S (S (Z)))) 3 where
  type ToNat (S (S (S (Z)))) = 3
  type ToPeano 3 = S (S (S (Z)))

instance NatIso (S (S (S (S (Z))))) 4 where
  type ToNat (S (S (S (S (Z))))) = 4
  type ToPeano 4 = S (S (S (S (Z))))

instance NatIso (S (S (S (S (S (Z)))))) 5 where
  type ToNat (S (S (S (S (S (Z)))))) = 5
  type ToPeano 5 = S (S (S (S (S (Z)))))

instance NatIso (S (S (S (S (S (S (Z))))))) 6 where
  type ToNat (S (S (S (S (S (S (Z))))))) = 6
  type ToPeano 6 = S (S (S (S (S (S (Z))))))

instance NatIso (S (S (S (S (S (S (S (Z)))))))) 7 where
  type ToNat (S (S (S (S (S (S (S (Z)))))))) = 7
  type ToPeano 7 = S (S (S (S (S (S (S (Z)))))))

instance NatIso (S (S (S (S (S (S (S (S (Z))))))))) 8 where
  type ToNat (S (S (S (S (S (S (S (S (Z))))))))) = 8
  type ToPeano 8 = S (S (S (S (S (S (S (S (Z))))))))

instance NatIso (S (S (S (S (S (S (S (S (S (Z)))))))))) 9 where
  type ToNat (S (S (S (S (S (S (S (S (S (Z)))))))))) = 9
  type ToPeano 9 = S (S (S (S (S (S (S (S (S (Z)))))))))

instance NatIso (S (S (S (S (S (S (S (S (S (S (Z))))))))))) 10 where
  type ToNat (S (S (S (S (S (S (S (S (S (S (Z))))))))))) = 10
  type ToPeano 10 = S (S (S (S (S (S (S (S (S (S (Z))))))))))

instance NatIso (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))) 11 where
  type ToNat (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))) = 11
  type ToPeano 11 = S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))

instance NatIso (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))) 12 where
  type ToNat (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))) = 12
  type ToPeano 12 = S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))

instance NatIso (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))) 13 where
  type ToNat (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))) = 13
  type ToPeano 13 = S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))

instance NatIso (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))) 14 where
  type ToNat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))) = 14
  type ToPeano 14 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))

instance NatIso (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))) 15 where
  type ToNat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))) = 15
  type ToPeano 15 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))

instance NatIso (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))) 16 where
  type ToNat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))) = 16
  type ToPeano 16 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))

instance NatIso (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))) 17 where
  type ToNat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))) = 17
  type ToPeano 17 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))

instance NatIso (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))))) 18 where
  type ToNat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))))) = 18
  type ToPeano 18 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))))

instance NatIso (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))))) 19 where
  type ToNat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))))) = 19
  type ToPeano 19 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))))



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
         , Uncurry xs
         , Arity xs
         , Arity ys
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
