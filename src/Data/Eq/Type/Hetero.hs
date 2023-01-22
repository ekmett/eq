{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

#if __GLASGOW_HASKELL__ < 806
{-# LANGUAGE TypeInType #-}
#endif

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Eq.Type.Hetero
-- Copyright   :  (C) 2011-2014 Edward Kmett, 2018 Ryan Scott
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  GHC
--
-- Leibnizian equality à la "Data.Eq.Type", generalized to be heterogeneous
-- using higher-rank kinds.
--
-- This module is only exposed on GHC 8.2 and later.
----------------------------------------------------------------------------
module Data.Eq.Type.Hetero
  (
  -- * Heterogeneous Leibnizian equality
    (:==)(..)
  -- * Equality as an equivalence relation
  , refl
  , trans
  , symm
  , coerce
  , apply
  -- * Lifting equality
  , lift
  , lift2, lift2'
  , lift3, lift3'
  -- * Lowering equality
  , lower
  , lower2
  , lower3
  -- * 'ET.:=' equivalence
  -- | 'ET.:=' is equivalent in power
  , toHomogeneous
  , fromHomogeneous
  -- * 'Eq.:~:' equivalence
  -- | 'Eq.:~:' is equivalent in power
  , fromLeibniz
  , toLeibniz
  -- * 'Eq.:~~:' equivalence
  -- | 'Eq.:~~:' is equivalent in power
  , heteroFromLeibniz
  , heteroToLeibniz
  -- * 'Co.Coercion' conversion
  -- | Leibnizian equality can be converted to representational equality
  , reprLeibniz
  ) where

import           Control.Category
import           Data.Groupoid
import           Data.Semigroupoid
import qualified Data.Type.Coercion as Co
import qualified Data.Type.Equality as Eq
import           Data.Kind
import qualified Data.Eq.Type as ET
import           Prelude hiding (id, (.))

infixl 4 :==

-- | Heterogeneous Leibnizian equality.
--
-- Leibnizian equality states that two things are equal if you can
-- substitute one for the other in all contexts.
newtype (a :: j) :== (b :: k)
  = HRefl { hsubst :: forall (c :: forall i. i -> Type). c a -> c b }
type role (:==) nominal nominal

-- | Equality is reflexive.
refl :: a :== a
refl = HRefl id

data family Coerce :: forall k. k -> Type
newtype instance Coerce (a :: Type) = Coerce { uncoerce :: a }

-- | If two things are equal, you can convert one to the other.
coerce :: a :== b -> a -> b
coerce f = uncoerce . hsubst f . Coerce

newtype Pair1 :: forall j1 k1 j2.
                 j1 -> k1 -> j2
              -> forall k2. k2 -> Type where
  Pair1 :: { unpair1 :: '(a1, a2) :== '(b1, b2) } -> Pair1 a1 b1 a2 b2

newtype Pair2 :: forall j2 k2 j1.
                 j2 -> k2 -> j1
              -> forall k1. k1 -> Type where
  Pair2 :: { unpair2 :: '(a1, a2) :== '(b1, b2) } -> Pair2 a2 b2 a1 b1

-- | Lift two equalities pairwise.
pair :: a1 :== b1 -> a2 :== b2 -> '(a1, a2) :== '(b1, b2)
pair ab1 ab2 = unpair2 $ hsubst ab1 $ Pair2 $ unpair1 $ hsubst ab2 $ Pair1 refl

data family Apply :: forall j1 j2.
                     (j1 -> j2) -> j1
                  -> forall k. k -> Type
newtype instance Apply (f :: j1 -> j2) (a :: j1) '((g :: k1 -> k2), (b :: k1))
  = Apply { unapply :: f a :== g b }

-- | Apply one equality to another, respectively
apply :: f :== g -> a :== b -> f a :== g b
apply fg ab = unapply $ hsubst (pair fg ab) $ Apply refl

newtype Push :: (forall j k. j -> k -> Type)
             -> forall j. j -> forall k. k -> Type where
  Push :: forall (p :: forall j k. j -> k -> Type)
                 j k (a :: j) (b :: k).
          { unpush :: p a b } -> Push p a b

-- | Equality is compositional.
comp :: b :== c -> a :== b -> a :== c
comp f = unpush . hsubst f . Push

-- | Equality forms a category.
instance Category (:==) where
  id  = refl
  (.) = comp

instance Semigroupoid (:==) where
  o = comp

instance Groupoid (:==) where
  inv = symm

-- | Equality is transitive.
trans :: a :== b -> b :== c -> a :== c
trans = flip comp

newtype Symm :: (forall j. j -> forall k. k -> Type)
             ->  forall j. j -> forall k. k -> Type where
  Symm :: forall (p :: forall j. j -> forall k. k -> Type)
                 j k (a :: j) (b :: k).
          { unsymm :: p b a } -> Symm p a b

-- | Equality is symmetric.
symm :: a :== b -> b :== a
symm ab = unpush $ unsymm $ hsubst ab $ Symm $ Push refl

data family Lift :: forall j r. (j -> r) -> j
                 -> forall k. k
                 -> Type
newtype instance Lift f (a :: j) (b :: j) =
  Lift { unlift :: f a :== f b }

-- | You can lift equality into any type constructor...
lift :: a :== b -> f a :== f b
lift f = unlift $ hsubst f $ Lift refl

data family Lift2 :: forall j1 j2 r.
                     (j1 -> j2 -> r) -> j1 -> j2
                  -> forall k. k
                  -> Type
newtype instance Lift2 f (a :: j1) (c :: j2) (b :: j1) =
  Lift2 { unlift2 :: f a c :== f b c }

-- | ... in any position.
lift2 :: a :== b -> f a c :== f b c
lift2 f = unlift2 $ hsubst f $ Lift2 refl

lift2' :: a :== b -> c :== d -> f a c :== f b d
lift2' ab cd = unpush $ lift2 ab `hsubst` Push (lift cd)

data family Lift3 :: forall j1 j2 j3 r.
                     (j1 -> j2 -> j3 -> r) -> j1 -> j2 -> j3
                  -> forall k. k
                  -> Type
newtype instance Lift3 f (a :: j1) (c :: j2) (d :: j3) (b :: j1) =
  Lift3 { unlift3 :: f a c d :== f b c d }

lift3 :: a :== b -> f a c d :== f b c d
lift3 f = unlift3 $ hsubst f $ Lift3 refl

lift3' :: a :== b -> c :== d -> e :== f -> g a c e :== g b d f
lift3' ab cd ef = unpush $ unpush (lift3 ab `hsubst` Push (lift2 cd)) `hsubst` Push (lift ef)

data family Lower :: forall j. j
                  -> forall k. k
                  -> Type
newtype instance Lower a (f x) = Lower { unlower :: a :== x }

-- | Type constructors are generative and injective, so you can lower equality
-- through any type constructors.
lower :: forall a b f g. f a :== g b -> a :== b
lower f = unlower $ hsubst f (Lower refl :: Lower a (f a))

data family Lower2 :: forall j. j
                   -> forall k. k
                   -> Type
newtype instance Lower2 a (f x c) = Lower2 { unlower2 :: a :== x }

lower2 :: forall a b f g c c'. f a c :== g b c' -> a :== b
lower2 f = unlower2 $ hsubst f (Lower2 refl :: Lower2 a (f a c))

data family Lower3 :: forall j. j
                   -> forall k. k
                   -> Type
newtype instance Lower3 a (f x c d) = Lower3 { unlower3 :: a :== x }

lower3 :: forall a b f g c c' d d'. f a c d :== g b c' d' -> a :== b
lower3 f = unlower3 $ hsubst f (Lower3 refl :: Lower3 a (f a c d))

data family Flay :: forall j.
                    (j -> j -> Type) -> j
                 -> forall k. k
                 -> Type
newtype instance Flay p (a :: j) (b :: j) = Flay { unflay :: p a b }

-- | Convert an appropriately kinded heterogeneous Leibnizian equality into
-- a homogeneous Leibnizian equality '(ET.:=)'.
toHomogeneous :: a :== b -> a ET.:= b
toHomogeneous f = unflay $ hsubst f $ Flay ET.refl

-- | Convert a homogeneous Leibnizian equality '(ET.:=)' to an appropriately kinded
-- heterogeneous Leibizian equality.
fromHomogeneous :: a ET.:= b -> a :== b
fromHomogeneous f = ET.subst f refl

fromLeibniz :: forall a b. a :== b -> a Eq.:~: b
fromLeibniz f = unflay $ hsubst f $ Flay Eq.Refl

toLeibniz :: a Eq.:~: b -> a :== b
toLeibniz Eq.Refl = refl

heteroFromLeibniz :: a :== b -> a Eq.:~~: b
heteroFromLeibniz f = unpush $ hsubst f $ Push Eq.HRefl

heteroToLeibniz :: a Eq.:~~: b -> a :== b
heteroToLeibniz Eq.HRefl = refl

instance Eq.TestEquality ((:==) a) where
  testEquality fa fb = Just (fromLeibniz (trans (symm fa) fb))

reprLeibniz :: a :== b -> Co.Coercion a b
reprLeibniz f = unflay $ hsubst f $ Flay Co.Coercion

instance Co.TestCoercion ((:==) a) where
  testCoercion fa fb = Just (reprLeibniz (trans (symm fa) fb))
