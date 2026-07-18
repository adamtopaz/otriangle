import Otriangle.OTriangle.Core
import Otriangle.MonoAnabelian.Package

/-!
# Full faithfulness for the O-triangle forgetful functor

The shared categorical definitions live in `Otriangle.OTriangle.Core`.  This module is kept after
`Otriangle.LCFT` in the import graph so that the full and faithful instances below can use the
functorial integral reconstruction and canonical Kummer comparison supplied there.

This is the integral case of Hoshi's Theorem 7.6(iv).  A group isomorphism is lifted by conjugating
the reconstructed monoid map with the canonical comparisons.  Naturality of the unique comparison
then says that a pair isomorphism is determined by its group component.
-/

noncomputable section

open CategoryTheory

namespace Anabelian
namespace OTriangle

universe u

namespace LocalGaloisMonoid

open LCFT

/-- Every isomorphism of local absolute Galois groups lifts to an equivariant isomorphism of their
integral monoids. -/
noncomputable instance forgetGaloisGroup_full : forgetGaloisGroup.Full := by
  constructor
  intro X Y f
  exact ⟨LCFT.integralReconstruction.lift f, rfl⟩

/-- An equivariant integral-monoid isomorphism is uniquely determined by its underlying isomorphism
of local absolute Galois groups. -/
instance forgetGaloisGroup_faithful : forgetGaloisGroup.Faithful := by
  constructor
  intro X Y f g h
  exact LCFT.integralReconstruction.hom_ext f g h

/-- The integral Galois pair is categorically equivalent to its absolute Galois group: essential
surjectivity is tautological from the common local-field presentations, while full faithfulness is
the integral mono-anabelian theorem. -/
noncomputable instance forgetGaloisGroup_isEquivalence : forgetGaloisGroup.IsEquivalence where

/-- The equivalence of groupoids induced by forgetting the integral monoid. -/
noncomputable def forgetGaloisGroupEquivalence :
    LocalGaloisMonoid.{u} ≌ LocalGaloisGroup.{u} :=
  forgetGaloisGroup.asEquivalence

end LocalGaloisMonoid
end OTriangle
end Anabelian
