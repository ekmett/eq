{-# LANGUAGE CPP, Rank2Types, ScopedTypeVariables, TypeOperators #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 706
#define LANGUAGE_PolyKinds
{-# LANGUAGE PolyKinds #-}
#endif
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 707
{-# LANGUAGE RoleAnnotations #-}
#endif
#if defined(__GLASGOW_HASKELL__) && MIN_VERSION_base(4,7,0)
#define HAS_DATA_TYPE_EQUALITY 1
{-# LANGUAGE GADTs #-}
#endif

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Eq.Type
-- Copyright   :  (C) 2011-2014 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  rank2 types, type operators, (optional) type families
--
-- Leibnizian equality. Injectivity in the presence of type families
-- is provided by a generalization of a trick by Oleg Kiselyov posted here:
--
-- <http://www.haskell.org/pipermail/haskell-cafe/2010-May/077177.html>
----------------------------------------------------------------------------

module Data.Eq.Type
  (
  -- * Leibnizian equality
    (:=)(..)
  -- * Equality as an equivalence relation
  , refl
  , trans
  , symm
  , coerce
  -- * Lifting equality
  , lift
  , lift2, lift2'
  , lift3, lift3'
#ifdef LANGUAGE_TypeFamilies
  -- * Lowering equality
  , lower
  , lower2
  , lower3
#endif
#ifdef HAS_DATA_TYPE_EQUALITY
  -- * 'Eq.:~:' equivalence
  -- | "Data.Type.Equality" GADT definition is equivalent in power
  , fromLeibniz
  , toLeibniz

  -- * 'Co.Coercion' conversion
  -- | Leibnizian equality can be converted to representational equality
  , reprLeibniz
#endif
  ) where

import Prelude (Maybe(..))
import Control.Category
import Data.Semigroupoid
import Data.Groupoid

#ifdef HAS_DATA_TYPE_EQUALITY
import qualified Data.Type.Coercion as Co
import qualified Data.Type.Equality as Eq
#endif

infixl 4 :=

-- | Leibnizian equality states that two things are equal if you can
-- substitute one for the other in all contexts
newtype a := b = Refl { subst :: forall c. c a -> c b }
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 707
type role (:=) nominal nominal
#endif

-- | Equality is reflexive
refl :: a := a
refl = Refl id

newtype Coerce a = Coerce { uncoerce :: a }
-- | If two things are equal you can convert one to the other
coerce :: a := b -> a -> b
coerce f = uncoerce . subst f . Coerce

-- | Equality forms a category
instance Category (:=) where
  id = Refl id
  bc . ab = subst bc ab

instance Semigroupoid (:=) where
  bc `o` ab = subst bc ab

instance Groupoid (:=) where
  inv = symm

-- | Equality is transitive
trans :: a := b -> b := c -> a := c
trans ab bc = subst bc ab

newtype Symm p a b = Symm { unsymm :: p b a }
-- | Equality is symmetric
symm :: (a := b) -> (b := a)
symm a = unsymm (subst a (Symm refl))

newtype Lift f a b = Lift { unlift :: f a := f b }
-- | You can lift equality into any type constructor
lift :: a := b -> f a := f b
lift a = unlift (subst a (Lift refl))

newtype Lift2 f c a b = Lift2 { unlift2 :: f a c := f b c }
-- | ... in any position
lift2 :: a := b -> f a c := f b c
lift2 a = unlift2 (subst a (Lift2 refl))

lift2' :: a := b -> c := d -> f a c := f b d
lift2' ab cd = subst (lift2 ab) (lift cd)

newtype Lift3 f c d a b = Lift3 { unlift3 :: f a c d := f b c d }
lift3 :: a := b -> f a c d := f b c d
lift3 a = unlift3 (subst a (Lift3 refl))

lift3' :: a := b -> c := d -> e := f -> g a c e := g b d f
lift3' ab cd ef = lift3 ab `subst` lift2 cd `subst` lift ef

#ifdef LANGUAGE_TypeFamilies
# ifdef LANGUAGE_PolyKinds
-- This is all more complicated than it needs to be. Ideally, we would just
-- write:
--
--   data family Lower (a :: j) (b :: k)
--   newtype instance Lower a (f x) = Lower { unlower :: a := x }
--
--   lower :: forall a b f g. f a := g b -> a := b
--   lower eq = unlower (subst eq (Lower refl :: Lower a (f a)))
--
-- And similarly for Lower{2,3}. Unfortunatetly, this won't typecheck on
-- GHC 7.6 through 7.10 due to an old typechecker bug. To work around the
-- issue, we must:
--
-- 1. Pass `f` and `g` as explicit arguments to the GenInj{,2,3} type family,
--    and
--
-- 2. Define overlapping instances for GenInj{,2,3}.
--
-- Part (2) of this workaround prevents us from using a data family here, as
-- GHC will reject overlapping data family instances as conflicting.
type family GenInj  (f :: j -> k)           (g :: j -> k)             (x :: k) :: j
type family GenInj2 (f :: i -> j -> k)      (g :: i -> j' -> k)       (x :: k) :: i
type family GenInj3 (f :: h -> i -> j -> k) (g :: h -> i' -> j' -> k) (x :: k) :: h
# else
type family GenInj  (f :: * -> *)           (g :: * -> *)           (x :: *) :: *
type family GenInj2 (f :: * -> * -> *)      (g :: * -> * -> *)      (x :: *) :: *
type family GenInj3 (f :: * -> * -> * -> *) (g :: * -> * -> * -> *) (x :: *) :: *
# endif

type instance GenInj  f g (f a) = a
type instance GenInj  f g (g b) = b

type instance GenInj2 f g (f a c)  = a
type instance GenInj2 f g (g b c') = b

type instance GenInj3 f g (f a c  d)  = a
type instance GenInj3 f g (g b c' d') = b

newtype Lower  f g a x = Lower  { unlower  :: a := GenInj  f g x }
newtype Lower2 f g a x = Lower2 { unlower2 :: a := GenInj2 f g x }
newtype Lower3 f g a x = Lower3 { unlower3 :: a := GenInj3 f g x }

-- | Type constructors are generative and injective, so you can lower equality
-- through any type constructors ...
lower :: forall a b f g. f a := g b -> a := b
lower eq = unlower (subst eq (Lower refl :: Lower f g a (f a)))

-- | ... in any position ...
lower2 :: forall a b f g c c'. f a c := g b c' -> a := b
lower2 eq = unlower2 (subst eq (Lower2 refl :: Lower2 f g a (f a c)))

-- | ... these definitions are poly-kinded on GHC 7.6 and up.
lower3 :: forall a b f g c c' d d'. f a c d := g b c' d' -> a := b
lower3 eq = unlower3 (subst eq (Lower3 refl :: Lower3 f g a (f a c d)))
#endif

#ifdef HAS_DATA_TYPE_EQUALITY
fromLeibniz :: a := b -> a Eq.:~: b
fromLeibniz a = subst a Eq.Refl

toLeibniz :: a Eq.:~: b -> a := b
toLeibniz Eq.Refl = refl

instance Eq.TestEquality ((:=) a) where
  testEquality fa fb = Just (fromLeibniz (trans (symm fa) fb))

reprLeibniz :: a := b -> Co.Coercion a b
reprLeibniz a = subst a Co.Coercion

instance Co.TestCoercion ((:=) a) where
  testCoercion fa fb = Just (reprLeibniz (trans (symm fa) fb))
#endif
