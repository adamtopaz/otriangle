import Otriangle.MonoAnabelian.FiniteTameRamification
import Otriangle.MonoAnabelian.FiniteInertiaRestriction

/-!
# Tame characters of normal finite fixed fields

The generic tame-character theorem is applied to the Galois group of a normal finite fixed field.
Mathlib's finite inertia cardinality formula identifies the group order with the relative
ramification index, so Hoshi's prime-to-residue-characteristic neighborhood condition gives
injectivity.
-/

noncomputable section

namespace Anabelian.OTriangle.LocalGaloisGroup

open LCFT ValuativeRel
open FiniteTameRamification

universe u

theorem fixedFieldFiniteTameCharacter_injective
    (G : LocalGaloisGroup.{u}) (U : OpenSubgroup G.toProfiniteGrp)
    (hN : U.toSubgroup.Normal)
    (hcop : Nat.Coprime
      (G.fixedFieldBaseExtension (OrderDual.toDual U)).relativeRamificationIndex
      G.presentation.residueChar) :
    let V : G.OpenSubgroupIndex := OrderDual.toDual U
    let K := G.presentation
    let L := G.fixedField V
    letI := K.nontriviallyNormedField
    letI := K.isUltrametricDist
    letI := K.completeSpace
    letI := G.fixedFieldNontriviallyNormedField V
    letI := G.fixedFieldIsUltrametricDist V
    letI : ValuativeRel L := G.fixedFieldValuativeRel V
    letI : TopologicalSpace L := G.fixedFieldTopologicalSpace V
    letI : IsNonarchimedeanLocalField L := G.fixedFieldIsNonarchimedeanLocalField V
    letI : ValuativeExtension K L := G.fixedFieldValuativeExtensionFromPresentation V
    letI : FiniteDimensional K L := G.fixedField_finiteDimensional V
    letI : Algebra.IsAlgebraic K L := by infer_instance
    letI : IsGalois K L := G.fixedField_isGalois_of_normal U hN
    letI : IsScalarTower K K L := IsScalarTower.of_algebraMap_eq' rfl
    letI : MulSemiringAction (L ≃ₐ[K] L) 𝒪[L] :=
      SpectralLocalField.integerMulSemiringAction K K L
    Function.Injective (tameCharacter 𝒪[L] (L ≃ₐ[K] L)) := by
  let V : G.OpenSubgroupIndex := OrderDual.toDual U
  let K := G.presentation
  let L := G.fixedField V
  letI := K.nontriviallyNormedField
  letI := K.isUltrametricDist
  letI := K.completeSpace
  letI := G.fixedFieldNontriviallyNormedField V
  letI := G.fixedFieldIsUltrametricDist V
  letI : ValuativeRel L := G.fixedFieldValuativeRel V
  letI : TopologicalSpace L := G.fixedFieldTopologicalSpace V
  letI : IsNonarchimedeanLocalField L := G.fixedFieldIsNonarchimedeanLocalField V
  letI : ValuativeExtension K L := G.fixedFieldValuativeExtensionFromPresentation V
  letI : FiniteDimensional K L := G.fixedField_finiteDimensional V
  letI : Algebra.IsAlgebraic K L := by infer_instance
  letI : IsGalois K L := G.fixedField_isGalois_of_normal U hN
  letI : IsScalarTower K K L := IsScalarTower.of_algebraMap_eq' rfl
  letI : MulSemiringAction (L ≃ₐ[K] L) 𝒪[L] :=
    SpectralLocalField.integerMulSemiringAction K K L
  letI : FaithfulSMul (L ≃ₐ[K] L) 𝒪[L] :=
    SpectralLocalField.integerMulSemiringAction_faithful K K L
  letI : CharP (IsLocalRing.ResidueField 𝒪[L]) K.residueChar :=
    (G.fixedFieldPointed V).residueFieldCharP
  apply tameCharacter_injective_of_coprime_card 𝒪[L] (L ≃ₐ[K] L)
    K.residueChar Fact.out
  rw [G.fixedFieldFiniteInertia_card U hN]
  exact hcop

end Anabelian.OTriangle.LocalGaloisGroup
