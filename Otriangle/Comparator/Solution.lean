import Otriangle.Comparator.Defs
import Otriangle.MonoAnabelian.Package

/-!
# Comparator solution: the integral O-triangle theorem

Proofs of the statements in `Otriangle.Comparator.Challenge`, as developed in `Otriangle.OTriangle`.

Unlike the challenge, this module is free to import the rest of the development: it is the
untrusted side of the comparison, and it reaches `Anabelian.LCFT.integralReconstruction` through
`Otriangle.MonoAnabelian.Package`.  Those modules are themselves built on
`Otriangle.Comparator.Defs`, so the statements proved here are the ones the challenge states.

A group isomorphism is lifted by conjugating the reconstructed monoid map with the canonical Kummer
comparisons; naturality of the unique comparison then says that a pair isomorphism is determined by
its group component.
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
theorem forgetGaloisGroup_full : forgetGaloisGroup.{u}.Full := by
  constructor
  intro X Y f
  exact ⟨LCFT.integralReconstruction.lift f, rfl⟩

/-- An equivariant integral-monoid isomorphism is uniquely determined by its underlying isomorphism
of local absolute Galois groups. -/
theorem forgetGaloisGroup_faithful : forgetGaloisGroup.{u}.Faithful := by
  constructor
  intro X Y f g h
  exact LCFT.integralReconstruction.hom_ext f g h

/-- The integral Galois pair is categorically equivalent to its absolute Galois group: essential
surjectivity is tautological from the common local-field presentations, while full faithfulness is
the integral mono-anabelian theorem. -/
theorem forgetGaloisGroup_isEquivalence : forgetGaloisGroup.{u}.IsEquivalence := by
  haveI := forgetGaloisGroup_full.{u}
  haveI := forgetGaloisGroup_faithful.{u}
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end LocalGaloisMonoid
end OTriangle
end Anabelian
