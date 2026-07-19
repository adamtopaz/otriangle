import Otriangle.MonoAnabelian.SpectralInertiaComparison

/-!
# Restriction of full inertia to finite fixed fields

For a normal open subgroup, restriction maps the full spectral inertia subgroup onto the finite
inertia group of its fixed field.  Combining this with the finite inertia cardinality theorem
characterizes unramified fixed fields by containment of full inertia.
-/

noncomputable section

namespace Anabelian.OTriangle.LocalGaloisGroup

open LCFT ValuativeRel

universe u

set_option maxHeartbeats 800000 in
-- The two residue-lifting directions unfold several spectral valuation structures.
theorem map_spectralInertiaSubgroup_restrictNormalHom
    (G : LocalGaloisGroup.{u}) (U : OpenSubgroup G.toProfiniteGrp)
    (hN : U.toSubgroup.Normal) :
    let V : G.OpenSubgroupIndex := OrderDual.toDual U
    letI := G.presentation.nontriviallyNormedField
    letI := G.presentation.isUltrametricDist
    letI := G.presentation.completeSpace
    letI := G.fixedFieldNontriviallyNormedField V
    letI := G.fixedFieldIsUltrametricDist V
    letI : ValuativeRel (G.fixedField V) := G.fixedFieldValuativeRel V
    letI : FiniteDimensional G.presentation (G.fixedField V) :=
      G.fixedField_finiteDimensional V
    letI : Algebra.IsAlgebraic G.presentation (G.fixedField V) := by infer_instance
    letI : IsGalois G.presentation (G.fixedField V) :=
      G.fixedField_isGalois_of_normal U hN
    letI : IsScalarTower G.presentation G.presentation (G.fixedField V) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : MulSemiringAction ((G.fixedField V) ≃ₐ[G.presentation] (G.fixedField V))
        𝒪[G.fixedField V] :=
      SpectralLocalField.integerMulSemiringAction
        G.presentation G.presentation (G.fixedField V)
    G.spectralInertiaSubgroup.map
        (AlgEquiv.restrictNormalHom (G.fixedField V)) =
      (IsLocalRing.maximalIdeal 𝒪[G.fixedField V]).inertia
        ((G.fixedField V) ≃ₐ[G.presentation] (G.fixedField V)) := by
  let V : G.OpenSubgroupIndex := OrderDual.toDual U
  let K := G.presentation
  let L := G.fixedField V
  let A := K.algebraicClosure
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
  letI := G.spectralAlgebraicClosureNontriviallyNormedField
  letI := G.spectralAlgebraicClosureIsUltrametricDist
  letI : ValuativeRel A := G.spectralAlgebraicClosureValuativeRel
  letI : ValuativeExtension K A := K.spectralValuativeExtension A
  letI : ValuativeExtension L A := G.fixedFieldValuativeExtension V
  letI : IsAlgClosure L A := G.fixedFieldIsAlgClosure V
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    intro x
    change (AlgEquiv.restrictNormalHom L σ) • x - x ∈
      IsLocalRing.maximalIdeal 𝒪[L]
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    apply (algebraMap (IsLocalRing.ResidueField 𝒪[L])
      (IsLocalRing.ResidueField 𝒪[A])).injective
    rw [IsLocalRing.ResidueField.algebraMap_residue,
      IsLocalRing.ResidueField.algebraMap_residue]
    have hker : K.spectralResidueGaloisMap σ = 1 := hσ
    have hx := DFunLike.congr_fun hker
      (IsLocalRing.residue 𝒪[A]
        (algebraMap 𝒪[L] 𝒪[A] x))
    change IsLocalRing.residue 𝒪[A]
        (K.spectralClosureIntegerAlgEquiv σ
          (algebraMap 𝒪[L] 𝒪[A] x)) = _ at hx
    have hcomm : K.spectralClosureIntegerAlgEquiv σ
        (algebraMap 𝒪[L] 𝒪[A] x) =
        algebraMap 𝒪[L] 𝒪[A] ((AlgEquiv.restrictNormalHom L σ) • x) := by
      apply Subtype.ext
      change σ ((x : L) : A) =
        ((AlgEquiv.restrictNormalHom L σ) (x : L) : A)
      exact (AlgEquiv.restrictNormal_commutes σ L (x : L)).symm
    rw [hcomm] at hx
    change IsLocalRing.residue 𝒪[A]
        (algebraMap 𝒪[L] 𝒪[A] ((AlgEquiv.restrictNormalHom L σ) • x)) =
      IsLocalRing.residue 𝒪[A] (algebraMap 𝒪[L] 𝒪[A] x) at hx
    exact hx
  · intro hτ
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective A τ
    let ρ : IsLocalRing.ResidueField 𝒪[A] ≃ₐ[IsLocalRing.ResidueField 𝒪[L]]
        IsLocalRing.ResidueField 𝒪[A] :=
      { toRingEquiv := (K.spectralResidueGaloisMap σ).toRingEquiv
        commutes' := fun y => by
          obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
          rw [IsLocalRing.ResidueField.algebraMap_residue]
          change IsLocalRing.residue 𝒪[A]
              (K.spectralClosureIntegerAlgEquiv σ
                (algebraMap 𝒪[L] 𝒪[A] x)) = _
          have hcomm : K.spectralClosureIntegerAlgEquiv σ
              (algebraMap 𝒪[L] 𝒪[A] x) =
              algebraMap 𝒪[L] 𝒪[A] (τ • x) := by
            apply Subtype.ext
            change σ ((x : L) : A) = ((τ (x : L)) : A)
            rw [← hσ]
            exact (AlgEquiv.restrictNormal_commutes σ L (x : L)).symm
          rw [hcomm]
          change algebraMap (IsLocalRing.ResidueField 𝒪[L])
              (IsLocalRing.ResidueField 𝒪[A])
                (IsLocalRing.residue 𝒪[L] (τ • x)) =
            algebraMap (IsLocalRing.ResidueField 𝒪[L])
              (IsLocalRing.ResidueField 𝒪[A])
                (IsLocalRing.residue 𝒪[L] x)
          congr 1
          rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
          exact hτ x }
    obtain ⟨u, hu⟩ := SpectralLocalField.residueGaloisMap_surjective K L A ρ
    let uK : A ≃ₐ[K] A := u.restrictScalars K
    have hures : K.spectralResidueGaloisMap uK =
        K.spectralResidueGaloisMap σ := by
      apply AlgEquiv.ext
      intro y
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
      have huy := DFunLike.congr_fun hu (IsLocalRing.residue 𝒪[A] x)
      change IsLocalRing.residue 𝒪[A]
          (SpectralLocalField.automorphismIntegerAlgEquiv K L A u x) =
        ρ (IsLocalRing.residue 𝒪[A] x) at huy
      exact huy
    refine ⟨uK⁻¹ * σ, ?_, ?_⟩
    · change K.spectralResidueGaloisMap (uK⁻¹ * σ) = 1
      rw [map_mul, map_inv, hures, inv_mul_cancel]
    · rw [map_mul, map_inv, hσ]
      have huone : AlgEquiv.restrictNormalHom L uK = 1 := by
        apply AlgEquiv.ext
        intro x
        apply (algebraMap L A).injective
        change algebraMap L A ((AlgEquiv.restrictNormalHom L uK) x) =
          algebraMap L A x
        have hc : algebraMap L A ((AlgEquiv.restrictNormalHom L uK) x) =
            uK (algebraMap L A x) :=
          AlgEquiv.restrictNormal_commutes uK L x
        rw [hc]
        change u ((x : L) : A) = ((x : L) : A)
        exact u.commutes x
      rw [huone, inv_one, one_mul]

/-- Spectral inertia is contained in a normal open subgroup exactly when the corresponding
finite fixed field is unramified. -/
theorem spectralInertiaSubgroup_le_iff_relativeRamificationIndex_eq_one
    (G : LocalGaloisGroup.{u}) (U : OpenSubgroup G.toProfiniteGrp)
    (hN : U.toSubgroup.Normal) :
    G.spectralInertiaSubgroup ≤ U.toSubgroup ↔
      (G.fixedFieldBaseExtension
        (OrderDual.toDual U)).relativeRamificationIndex = 1 := by
  let V : G.OpenSubgroupIndex := OrderDual.toDual U
  let E := G.fixedFieldBaseExtension V
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
  let Iₗ : Subgroup (L ≃ₐ[K] L) :=
    (IsLocalRing.maximalIdeal 𝒪[L]).inertia (L ≃ₐ[K] L)
  have hmap : G.spectralInertiaSubgroup.map
      (AlgEquiv.restrictNormalHom L) = Iₗ :=
    map_spectralInertiaSubgroup_restrictNormalHom G U hN
  let C : ClosedSubgroup G.toProfiniteGrp := ⟨U.toSubgroup, U.isClosed⟩
  have hker : (AlgEquiv.restrictNormalHom L).ker = U.toSubgroup := by
    rw [IntermediateField.restrictNormalHom_ker]
    exact InfiniteGalois.fixingSubgroup_fixedField C
  have hbot_card : Iₗ = ⊥ ↔ Nat.card Iₗ = 1 := by
    constructor
    · intro h
      rw [h]
      exact Nat.card_unique
    · intro h
      apply (Subgroup.eq_bot_iff_forall Iₗ).mpr
      intro x hx
      exact congrArg Subtype.val
        ((Nat.card_eq_one_iff_unique.mp h).1.elim ⟨x, hx⟩ 1)
  calc
    G.spectralInertiaSubgroup ≤ U.toSubgroup ↔
        G.spectralInertiaSubgroup.map (AlgEquiv.restrictNormalHom L) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hker]
      rfl
    _ ↔ Iₗ = ⊥ := by rw [hmap]
    _ ↔ Nat.card Iₗ = 1 := hbot_card
    _ ↔ E.relativeRamificationIndex = 1 := by
      rw [G.fixedFieldFiniteInertia_card U hN]

end Anabelian.OTriangle.LocalGaloisGroup
