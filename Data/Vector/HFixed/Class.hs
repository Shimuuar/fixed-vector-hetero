{-# LANGUAGE GADTs                 #-}
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
{-# LANGUAGE ConstraintKinds       #-}
module Data.Vector.HFixed.Class (
    -- * Types and type classes
    Fn
  , Fun(..)
  , Proxy(..)
    -- ** Type functions
  , (++)()
  , Len
  , HomList
    -- ** Type classes
  , Arity(..)
  , HVector(..)
    -- ** Interop with homogeneous vectors
  , HomArity(..)
    -- * Operations of Fun
    -- ** Recursion primitives
  , apFun
  , constFun
  , stepFun
    -- ** More complicated functions
  , curryF
  , curry1
  , concatF
  , shuffleF
  , lensF
  , Index(..)
    -- * Folds and unfolds
  , Foldr(..)
  , Unfoldr(..)
    -- * Isomorphism between types
  , NatIso(..)
  ) where

import Control.Applicative (Applicative(..))
import Data.Complex        (Complex(..))
import           Data.Vector.Fixed.Internal.Arity   (S,Z)
import qualified Data.Vector.Fixed.Internal.Arity as F

import GHC.Generics hiding (Arity(..),S)
import GHC.TypeLits
import GHC.Prim            (Constraint)



----------------------------------------------------------------
-- Types
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


-- | Concaternation of type level lists.
type family   (++) (xs :: [*]) (ys :: [*]) :: [*]
type instance (++) '[]       ys = ys
type instance (++) (x ': xs) ys = x ': xs ++ ys

                    
-- | Length of type list expressed as type level naturals from
--   @fixed-vector@.
type family   Len (xs :: [α]) :: *
type instance Len '[]       = Z
type instance Len (x ': xs) = S (Len xs)


-- | Homogeneous type list with length @n@ and element type @a@.
type family   HomList n (a :: α) :: [α]
type instance HomList  Z    a = '[]
type instance HomList (S n) a = a ': HomList n a


                   
----------------------------------------------------------------
-- Generic operations
----------------------------------------------------------------

-- | Type class for dealing with N-ary function in generic way. Since
--   we can't say anything about types of elements most functions
--   implemented in terms of 'accum' and 'apply' can't do anything
--   beyond shuffling function parameters.
--
--   This is also somewhat a kitchen sink module. It contains other
--   inductively defined functions which couldn't be defined in terms
--   of 'accum' and 'apply' but still useful.
class Arity (xs :: [*]) where
  -- | Fold over /N/ elements exposed as N-ary function.
  accum :: (forall a as. t (a ': as) -> a -> t as)
           -- ^ Step function. Applies element to accumulator.
        -> (t '[] -> b)
           -- ^ Extract value from accumulator.
        -> t xs
           -- ^ Initial state.
        -> Fn xs b

  -- | Apply values to N-ary function
  apply :: (forall a as. t (a ': as) -> (a, t as))
           -- | Extract value to be applied to function.
        -> t xs
           -- | Initial state.
        -> Fn xs b
           -- | N-ary function.
        -> b

  -- | Size of type list as integer.
  arity :: Proxy xs -> Int

  -- | Conversion function. It could be expressed via accum:
  --
  -- > uncurryF :: forall xs ys r. Fun xs (Fun ys r) -> Fun (xs ++ ys) r
  -- > uncurryF f =
  -- >   case fmap unFun f :: Fun xs (Fn ys r) of
  -- >     Fun g -> Fun g
  --
  -- Alas it requires proving constraint:
  --
  -- > Fn (xs++ys) r ~ Fn xs (Fn ys r)
  --
  -- It is always true but there is no way to tell GHC about it.
  uncurryF :: Fun xs (Fun ys r) -> Fun (xs ++ ys) r

instance Arity '[] where
  accum _ f t = f t
  apply _ _ b = b
  arity _     = 0
  {-# INLINE accum #-}
  {-# INLINE apply #-}
  {-# INLINE arity #-}
  uncurryF = unFun
  {-# INLINE uncurryF #-}

instance Arity xs => Arity (x ': xs) where
  accum f g t = \a -> accum f g (f t a)
  apply f t h = case f t of (a,u) -> apply f u (h a)
  arity _     = 1 + arity (Proxy :: Proxy xs)
  {-# INLINE accum #-}
  {-# INLINE apply #-}
  {-# INLINE arity #-}
  uncurryF f = Fun $ unFun . uncurryF . apFun f
  {-# INLINE uncurryF #-}



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
-- Interop with homogeneous vectors
----------------------------------------------------------------

-- | Type class for homogeneous type functions
class (F.Arity n, Arity (HomList n a)) => HomArity n a where
  toHeterogeneous :: F.Fun n a r -> Fun (HomList n a) r
  toHomogeneous   :: Fun (HomList n a) r -> F.Fun n a r


instance HomArity Z a where
  toHeterogeneous = Fun . F.unFun
  toHomogeneous   = F.Fun . unFun
  {-# INLINE toHeterogeneous #-}
  {-# INLINE toHomogeneous   #-}

instance HomArity n a => HomArity (S n) a where
  toHeterogeneous f
    = Fun $ \a -> unFun $ toHeterogeneous (apHFun f a)
  toHomogeneous (f :: Fun (a ': HomList n a) r)
    = F.Fun $ \a -> F.unFun (toHomogeneous $ apFun f a :: F.Fun n a r)
  {-# INLINE toHeterogeneous #-}
  {-# INLINE toHomogeneous   #-}

-- FIXME: should be implemented in fixed-vector
--        (wait for 0.5)
apHFun :: F.Fun (S n) a b -> a -> F.Fun n a b
apHFun (F.Fun f) x = F.Fun (f x)
{-# INLINE apHFun #-}



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

instance Arity xs => Monad (Fun xs) where
  return  = pure
  f >>= g = shuffleF (Fun $ fmap unFun g) <*> f
  {-# INLINE return #-}
  {-# INLINE (>>=)  #-}

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
concatF :: (Arity xs, Arity ys)
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
{-# INLINE curry1 #-}

-- | Move first argument of function to its result. This function is
--   useful for implementation of lens.
shuffleF :: forall x xs r. Arity xs => Fun (x ': xs) r -> Fun xs (x -> r)
{-# INLINE shuffleF #-}
shuffleF (Fun f0) = Fun $ accum
  (\(T_shuffle f) a -> T_shuffle (\x -> f x a))
  (\(T_shuffle f)   -> f)
  (T_shuffle f0 :: T_shuffle x r xs)

data T_shuffle x r xs = T_shuffle (Fn (x ': xs) r)


-- | Helper for lens implementation.
lensF :: forall f r x y xs. (Functor f, Arity xs)
       => (x -> f y) -> Fun (y ': xs) r -> Fun (x ': xs) (f r)
{-# INLINE lensF #-}
lensF fun f = Fun $ \x -> unFun $ fmap (\r -> fmap (r $) (fun x))
                                $ shuffleF f



----------------------------------------------------------------
-- Indexing
----------------------------------------------------------------

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
-- Folding and unfolding
----------------------------------------------------------------

-- | Generic right fold
class Foldr (c :: * -> Constraint) (xs :: [*]) where
  hfoldrF :: Proxy c -> (forall a. c a => a -> b -> b) -> Fun xs (b -> b)

instance Foldr c '[] where
  hfoldrF _ _ = Fun id
instance (Foldr c xs, c x, Arity xs)  => Foldr c (x ': xs) where
  hfoldrF wit f
    = Fun $ \x -> unFun $ fmap ((f x) . ) (hfoldrF wit f `asFunXS` (Proxy :: Proxy xs))

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
         , Arity xs, GElems f ~ xs
         , Arity ys, GElems g ~ ys
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
