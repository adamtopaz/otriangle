import Otriangle.Comparator.Defs

/-!
# Comparator challenge: the integral O-triangle theorem

The main theorems of this development, restated from `Otriangle.OTriangle`.  Together they are the
integral case of Hoshi's Theorem 7.6(iv): forgetting the integral monoid identifies the category of
integral MLF-pairs with the category of their absolute Galois groups.

Every proof is `sorry`; see `Otriangle.Comparator.Solution`.
-/

noncomputable section

open CategoryTheory

namespace Anabelian
namespace OTriangle

universe u

namespace LocalGaloisMonoid

/-- Every isomorphism of local absolute Galois groups lifts to an equivariant isomorphism of their
integral monoids. -/
theorem forgetGaloisGroup_full : forgetGaloisGroup.{u}.Full := by
  sorry

/-- An equivariant integral-monoid isomorphism is uniquely determined by its underlying isomorphism
of local absolute Galois groups. -/
theorem forgetGaloisGroup_faithful : forgetGaloisGroup.{u}.Faithful := by
  sorry

/-- The integral Galois pair is categorically equivalent to its absolute Galois group: essential
surjectivity is tautological from the common local-field presentations, while full faithfulness is
the integral mono-anabelian theorem. -/
theorem forgetGaloisGroup_isEquivalence : forgetGaloisGroup.{u}.IsEquivalence := by
  sorry

end LocalGaloisMonoid
end OTriangle
end Anabelian
