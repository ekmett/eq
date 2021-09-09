4.3 [????.??.??]
----------------
* Generalize the types of `Data.Eq.Type.lower{,2,3}`:

  ```diff
  -lower :: f a := f b -> a := b
  +lower :: f a := g b -> a := b

  -lower2 :: f a c := f b c  -> a := b
  +lower2 :: f a c := g b c' -> a := b

  -lower3 :: f a c d := f b c  d  -> a := b
  +lower3 :: f a c d := g b c' d' -> a := b
  ```

  The types of `Data.Eq.Type.Hetero.lower{,2,3}` have been generalized
  analogously.
* `Data.Eq.Type.Hetero.lower{,2,3}` now have the same order of type variables
  as their counterparts in `Data.Eq.Type`.
* Add an `apply` function to `Data.Eq.Type` and `Data.Eq.Type.Hetero`.
* Drop support for pre-7.0 versions of GHC.

4.2.1 [2020.10.01]
------------------
* Allow building with GHC 9.0.

4.2 [2018.04.24]
----------------
* Make `lower`, `lower2`, and `lower3` in `Data.Eq.Type` poly-kinded.
* Introduce the `Data.Eq.Type.Hetero` module, which exposes `(:==)`, a
  heterogeneously kinded version of `(:=)`. This module is only available
  on GHC 8.2 and later.

4.1
---
* Add `TestEquality` and `TestCoercion` instances for `(:=)`.
* Add `fromLeibniz` and `toLeibniz` functions for converting between `(:~:)`
  (from `Data.Type.Equality`) and `(:=)`.
* Add a `reprLeibniz` function to convert `(:=)` to a `Coercion`
  (i.e., representational equality).
* Make `(:=)` a newtype.
* We can remove the `Trustworthy` claim and infer as `Safe` on modern GHCs.

4.0.2
-----
* Made := kind polymorphic.

4.0.1
-----
* Provided an explicit nominal `RoleAnnotation`.

4.0
---
* Updated to work with `semigroupoids` 4.0

3.1.1
-----
* Claim to be `Trustworthy`

3.1
---
* Disabled observing injectivity through `TypeFamilies` for GHC >= 7.6

3.0.1
-----
* Updated build system
* Removed my personal intra-package dependency upper bounds
* Added `README` and `CHANGELOG`
