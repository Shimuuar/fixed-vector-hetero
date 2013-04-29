{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- |
-- Operation on type level lists.
module Data.Vector.HFixed.TypeList (
    Proxy(..)
  , Length(..)
  , Concat
  ) where

-- | Kind polymorphic proxy.
data Proxy (a :: α) = Proxy

-- | Legnth of type-level list.
class Length (xs :: [*]) where
  listLen :: Proxy xs -> Int

instance Length '[] where
  listLen _ = 0
instance Length xs => Length (x ': xs) where
  listLen _ = 1 + listLen (Proxy :: Proxy xs)


-- | Concaternation of type level lists.
type family   Concat (xs :: [*]) (ys :: [*]) :: [*]
type instance Concat '[]       ys = ys
type instance Concat (x ': xs) ys = x ': Concat xs ys
