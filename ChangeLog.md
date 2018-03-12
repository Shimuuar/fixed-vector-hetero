Changes in 0.5.0.0

  * GHC8.4 compatibility release. Semigroup instance is added for HVec
  
  * Classes `Arity`, `ArityC`, and `HVectorF` are now polykinded

Changes in 0.4.0.0

  * Major rework of API. `Fun` and `TFun` are unified. `Fun ~ TFun Identity`.
    Type class `ArityC` now contain special variants of `accum` and
    `arity` instead of building data structure containing all necessary dictionaries.

  * `Monad` constraints now relaxed to `Applicative` where appropriate

  * Most functions now have 3 variants: typeclass-based for `HVector`,
    typeclass-based for `HVectorF` and ones that use natural transformations for
    `HVectorF`. Some have been renamed to get consistent naming.

  * Support for GHC 7.10 is dropped

  * `HVecF` definition is moved to `Data.Vector.HFixed.HVec`

Changes in 0.3.1.2

  * Fix build for GHC 8.2

Changes in 0.3.1.0

  * Fix build for GHC 8.0


Changes in 0.3.1.0

  * replicateF added

  * type signature of zipMonoF generalized


Changes in 0.3.0.0

  * HVector instances up to 32-element tuples

  * `asCVec` function added

  * `ContVec` reexported from Data.Vector.HFixed


Changes in 0.2.0.0

  * Type changing lenses added

  * zipMonoF added

  * types of monomorphize and monomorphizeF corrected
