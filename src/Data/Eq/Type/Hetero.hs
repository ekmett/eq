{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}

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
-- Leibnizian equality à la "Data.Eq.Type", generalized to be heterogenous
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
import           GHC.Exts (Any)
import           Prelude hiding (id, (.))

infixl 4 :==

-- | Heterogeneous Leibnizian equality.
--
-- Leibnizian equality states that two things are equal if you can
-- substitute one for the other in all contexts.
newtype (a :: j) :== (b :: k)
  = HRefl { hsubst :: forall (c :: forall (i :: Type). i -> Type). c a -> c b }
type role (:==) nominal nominal

-- | Equality is reflexive.
refl :: a :== a
refl = HRefl id

newtype Coerce (a :: k) = Coerce { uncoerce :: MassageKind Type a }

type family MassageKind (j :: Type) (a :: k) :: j where
  MassageKind j (a :: j) = a
  MassageKind _ _        = Any

-- | If two things are equal, you can convert one to the other.
coerce :: a :== b -> a -> b
coerce f = uncoerce . hsubst f . Coerce

newtype Push :: (forall (j :: Type) (k :: Type). j -> k -> Type)
             -> forall (j :: Type). j -> forall (k :: Type). k -> Type where
  Push :: forall (p :: forall (j :: Type) (k :: Type). j -> k -> Type)
                 (j :: Type) (k :: Type) (a :: j) (b :: k).
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

newtype Symm :: (forall (i1 :: Type). i1 -> forall (i2 :: Type). i2 -> Type)
             -> forall (j :: Type). j
             -> forall (k :: Type). k
             -> Type where
  Symm :: forall (p :: forall (i1 :: Type). i1 -> forall (i2 :: Type). i2 -> Type)
                 (j :: Type) (k :: Type)
                 (a :: j) (b :: k).
          { unsymm :: p b a } -> Symm p a b

-- | Equality is symmetric.
symm :: a :== b -> b :== a
symm ab = unpush $ unsymm $ hsubst ab $ Symm $ Push refl

newtype Lift :: forall (j :: Type) (r :: Type).
                (j -> r) -> j
             -> forall (k :: Type). k
             -> Type where
  Lift :: forall (j :: Type) (k :: Type) (r :: Type)
                 (f :: j -> r) (a :: j) (b :: k).
          { unlift :: f a :== f (MassageKind j b) } -> Lift f a b

-- | You can lift equality into any type constructor...
lift :: a :== b -> f a :== f b
lift f = unlift $ hsubst f $ Lift refl

newtype Lift2 :: forall (j1 :: Type) (j2 :: Type) (r :: Type).
                 (j1 -> j2 -> r) -> j1 -> j2
              -> forall (k :: Type). k
              -> Type where
  Lift2 :: forall (j1 :: Type) (j2 :: Type) (k :: Type) (r :: Type)
                  (f :: j1 -> j2 -> r) (a :: j1) (b :: k) (c :: j2).
           { unlift2 :: f a c :== f (MassageKind j1 b) c } -> Lift2 f a c b

-- | ... in any position.
lift2 :: a :== b -> f a c :== f b c
lift2 f = unlift2 $ hsubst f $ Lift2 refl

lift2' :: a :== b -> c :== d -> f a c :== f b d
lift2' ab cd = unpush $ lift2 ab `hsubst` Push (lift cd)

newtype Lift3 :: forall (j1 :: Type) (j2 :: Type) (j3 :: Type) (r :: Type).
                 (j1 -> j2 -> j3 -> r) -> j1 -> j2 -> j3
              -> forall (k :: Type). k
              -> Type where
  Lift3 :: forall (j1 :: Type) (j2 :: Type) (j3 :: Type) (k :: Type) (r :: Type)
                  (f :: j1 -> j2 -> j3 -> r) (a :: j1) (b :: k) (c :: j2) (d :: j3).
           { unlift3 :: f a c d :== f (MassageKind j1 b) c d } -> Lift3 f a c d b

lift3 :: a :== b -> f a c d :== f b c d
lift3 f = unlift3 $ hsubst f $ Lift3 refl

lift3' :: a :== b -> c :== d -> e :== f -> g a c e :== g b d f
lift3' ab cd ef = unpush $ unpush (lift3 ab `hsubst` Push (lift2 cd)) `hsubst` Push (lift ef)

newtype Lower :: Type
              -> forall (j :: Type). j
              -> forall (k :: Type). k -> Type where
  Lower :: forall (i :: Type) (j :: Type) (k :: Type) (a :: j) (b :: k).
           { unlower :: Inj i a :== Inj i (MassageKind j b) } -> Lower i a b

type family Inj (j :: Type) (a :: k) :: j where
  Inj j (f (a :: j)) = a
  Inj _ _            = Any

-- | Type constructors are injective, so you can lower equality through any type constructor.
lower :: forall (j :: Type) (k :: Type) (f :: j -> k) (a :: j) (b :: j).
         f a :== f b -> a :== b
lower f = unlower $ hsubst f (Lower refl :: Lower j (f a) (f a))

newtype Lower2 :: Type
               -> forall (j :: Type). j
               -> forall (k :: Type). k -> Type where
  Lower2 :: forall (i :: Type) (j :: Type) (k :: Type) (a :: j) (b :: k).
            { unlower2 :: Inj2 i a :== Inj2 i (MassageKind j b) } -> Lower2 i a b

type family Inj2 (j :: Type) (a :: k) :: j where
  Inj2 j (f (a :: j) b) = a
  Inj2 _ _              = Any

lower2 :: forall (i :: Type) (j :: Type) (k :: Type)
                 (f :: i -> j -> k) (a :: i) (b :: i) (c :: j).
          f a c :== f b c -> a :== b
lower2 f = unlower2 $ hsubst f (Lower2 refl :: Lower2 i (f a c) (f a c))

newtype Lower3 :: Type
               -> forall (j :: Type). j
               -> forall (k :: Type). k -> Type where
  Lower3 :: forall (i :: Type) (j :: Type) (k :: Type) (a :: j) (b :: k).
            { unlower3 :: Inj3 i a :== Inj3 i (MassageKind j b) } -> Lower3 i a b

type family Inj3 (j :: Type) (a :: k) :: j where
  Inj3 j (f (a :: j) b c) = a
  Inj3 _ _                = Any

lower3 :: forall (h :: Type) (i :: Type) (j :: Type) (k :: Type)
                 (f :: h -> i -> j -> k) (a :: h) (b :: h) (c :: i) (d :: j).
          f a c d :== f b c d -> a :== b
lower3 f = unlower3 $ hsubst f (Lower3 refl :: Lower3 h (f a c d) (f a c d))

newtype Flay :: forall (j :: Type).
                (j -> j -> Type) -> j
             -> forall (k :: Type). k -> Type where
  Flay :: forall (j :: Type) (k :: Type)
                 (p :: j -> j -> Type) (a :: j) (b :: k).
          { unflay :: p a (MassageKind j b) } -> Flay p a b

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
heteroFromLeibniz f = unpush $ hsubst f $ Push $ Eq.HRefl

heteroToLeibniz :: a Eq.:~~: b -> a :== b
heteroToLeibniz Eq.HRefl = refl

instance Eq.TestEquality ((:==) a) where
  testEquality fa fb = Just (fromLeibniz (trans (symm fa) fb))

reprLeibniz :: a :== b -> Co.Coercion a b
reprLeibniz f = unflay $ hsubst f $ Flay Co.Coercion

instance Co.TestCoercion ((:==) a) where
  testCoercion fa fb = Just (reprLeibniz (trans (symm fa) fb))
