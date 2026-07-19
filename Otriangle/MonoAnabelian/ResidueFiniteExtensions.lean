import Otriangle.MonoAnabelian.OneField

/-!
# Finite extensions inside the residue algebraic closure

This module embeds the standard degree-`n` extension of a finite residue field in the residue
field of the chosen algebraic closure.  Its field range gives a finite Galois intermediate field
of exactly degree `n`.
-/

noncomputable section

namespace Anabelian
namespace LCFT

open OTriangle

universe u

/-- An embedding of the standard degree-`n` finite-field extension into the chosen residue
algebraic closure. -/
noncomputable def residueExtensionEmbedding
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) [NeZero n] :
    FiniteField.Extension (ResidueField K) K.residueChar n →ₐ[ResidueField K]
      AlgebraicClosureResidueField K := by
  letI : IsAlgClosed (AlgebraicClosureResidueField K) :=
    IsAlgClosure.isAlgClosed (ResidueField K)
  exact IsAlgClosed.lift

/-- The degree-`n` finite Galois intermediate field in the chosen residue algebraic closure. -/
noncomputable def residueFiniteGaloisIntermediateField
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) [NeZero n] :
    FiniteGaloisIntermediateField (ResidueField K)
      (AlgebraicClosureResidueField K) := by
  let E := FiniteField.Extension (ResidueField K) K.residueChar n
  let ι : E →ₐ[ResidueField K] AlgebraicClosureResidueField K :=
    residueExtensionEmbedding K n
  let L : IntermediateField (ResidueField K) (AlgebraicClosureResidueField K) :=
    ι.fieldRange
  letI : FiniteDimensional (ResidueField K) L :=
    Module.Finite.equiv ι.equivFieldRange.toLinearEquiv
  letI : IsGalois (ResidueField K) L :=
    IsGalois.of_algEquiv ι.equivFieldRange
  exact { toIntermediateField := L }

/-- The constructed finite residue intermediate field has the prescribed degree. -/
theorem residueFiniteGaloisIntermediateField_finrank
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) [NeZero n] :
    Module.finrank (ResidueField K) (residueFiniteGaloisIntermediateField K n) = n := by
  let E := FiniteField.Extension (ResidueField K) K.residueChar n
  let ι : E →ₐ[ResidueField K] AlgebraicClosureResidueField K :=
    residueExtensionEmbedding K n
  change Module.finrank (ResidueField K) ι.fieldRange = n
  rw [← ι.equivFieldRange.toLinearEquiv.finrank_eq]
  exact FiniteField.finrank_extension (ResidueField K) K.residueChar n

end LCFT
end Anabelian
