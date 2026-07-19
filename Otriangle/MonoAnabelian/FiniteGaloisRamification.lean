import Otriangle.MonoAnabelian.FixedFieldRamification
import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Finite Galois inertia at fixed fields

For a normal open subgroup, its fixed field is a finite Galois extension of the presented local
field.  This file identifies the order of its finite inertia group with the relative
ramification index constructed from the two maximal ideals.  It is the finite-level arithmetic
input for Hoshi's description of inertia as an intersection of open normal subgroups.
-/

noncomputable section

namespace Anabelian.OTriangle.LocalGaloisGroup

open LCFT ValuativeRel

universe u

/-- The order of the inertia group of a normal finite fixed field is its relative ramification
index.  The Galois action and both valuation rings here are the canonical spectral ones built
from the presented local field. -/
theorem fixedFieldFiniteInertia_card
    (G : LocalGaloisGroup.{u}) (U : OpenSubgroup G.toProfiniteGrp)
    (hN : U.toSubgroup.Normal) :
    let V : G.OpenSubgroupIndex := OrderDual.toDual U
    let E := G.fixedFieldBaseExtension V
    letI := G.presentation.nontriviallyNormedField
    letI := G.presentation.isUltrametricDist
    letI := G.presentation.completeSpace
    letI := G.fixedFieldNontriviallyNormedField V
    letI := G.fixedFieldIsUltrametricDist V
    letI : ValuativeRel (G.fixedField V) := G.fixedFieldValuativeRel V
    letI : FiniteDimensional G.presentation (G.fixedField V) :=
      G.fixedField_finiteDimensional V
    letI : Algebra.IsAlgebraic G.presentation (G.fixedField V) := by infer_instance
    letI : IsScalarTower G.presentation G.presentation (G.fixedField V) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : MulSemiringAction ((G.fixedField V) ≃ₐ[G.presentation] (G.fixedField V))
        𝒪[G.fixedField V] :=
      SpectralLocalField.integerMulSemiringAction
        G.presentation G.presentation (G.fixedField V)
    Nat.card ((IsLocalRing.maximalIdeal 𝒪[G.fixedField V]).inertia
        ((G.fixedField V) ≃ₐ[G.presentation] (G.fixedField V))) =
      E.relativeRamificationIndex := by
  let V : G.OpenSubgroupIndex := OrderDual.toDual U
  let E := G.fixedFieldBaseExtension V
  letI := G.presentation.nontriviallyNormedField
  letI := G.presentation.isUltrametricDist
  letI := G.presentation.completeSpace
  letI := G.fixedFieldNontriviallyNormedField V
  letI := G.fixedFieldIsUltrametricDist V
  letI : ValuativeRel (G.fixedField V) := G.fixedFieldValuativeRel V
  letI : TopologicalSpace (G.fixedField V) := G.fixedFieldTopologicalSpace V
  letI : IsNonarchimedeanLocalField (G.fixedField V) :=
    G.fixedFieldIsNonarchimedeanLocalField V
  letI : ValuativeExtension G.presentation (G.fixedField V) :=
    G.fixedFieldValuativeExtensionFromPresentation V
  letI : FiniteDimensional G.presentation (G.fixedField V) :=
    G.fixedField_finiteDimensional V
  letI : Algebra.IsAlgebraic G.presentation (G.fixedField V) := by infer_instance
  letI : IsGalois G.presentation (G.fixedField V) := by
    let e : G.toProfiniteGrp ≃* LCFT.AbsoluteGaloisGroup G.presentation :=
      { toFun := fun x => x
        invFun := fun x => x
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl }
    let H : Subgroup (LCFT.AbsoluteGaloisGroup G.presentation) :=
      U.toSubgroup.map e.toMonoidHom
    letI : H.Normal := hN.map e.toMonoidHom e.surjective
    have hfield : IntermediateField.fixedField H = G.fixedField V := by
      ext x
      simp only [IntermediateField.mem_fixedField_iff]
      constructor
      · intro hx f hf
        exact hx f ⟨f, hf, rfl⟩
      · intro hx f hf
        obtain ⟨g, hg, rfl⟩ := hf
        exact hx g hg
    exact hfield ▸
      (inferInstance : IsGalois G.presentation (IntermediateField.fixedField H))
  letI : IsScalarTower G.presentation G.presentation (G.fixedField V) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Fintype ((G.fixedField V) ≃ₐ[G.presentation] (G.fixedField V)) :=
    AlgEquiv.fintype G.presentation (G.fixedField V)
  letI : MulSemiringAction ((G.fixedField V) ≃ₐ[G.presentation] (G.fixedField V))
      𝒪[G.fixedField V] :=
    SpectralLocalField.integerMulSemiringAction
      G.presentation G.presentation (G.fixedField V)
  letI : IsGaloisGroup ((G.fixedField V) ≃ₐ[G.presentation] (G.fixedField V))
      (LocalIntegerRing G.presentation) 𝒪[G.fixedField V] := by
    refine { faithful := ?_, commutes := ?_, isInvariant := ?_ }
    · constructor
      intro σ τ h
      apply (inferInstance : FaithfulSMul
        ((G.fixedField V) ≃ₐ[G.presentation] (G.fixedField V))
        (G.fixedField V)).eq_of_smul_eq_smul
      intro x
      obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective 𝒪[G.fixedField V] x
      change σ x = τ x
      rw [← hx, map_div₀, map_div₀]
      change σ (a : G.fixedField V) / σ (b : G.fixedField V) =
        τ (a : G.fixedField V) / τ (b : G.fixedField V)
      have ha := congrArg Subtype.val (h a)
      have hb' := congrArg Subtype.val (h b)
      change σ (a : G.fixedField V) = τ (a : G.fixedField V) at ha
      change σ (b : G.fixedField V) = τ (b : G.fixedField V) at hb'
      rw [ha, hb']
    · constructor
      intro σ a b
      apply Subtype.ext
      change σ (((a • b : 𝒪[G.fixedField V]) : G.fixedField V)) =
        ((a • (σ • b) : 𝒪[G.fixedField V]) : G.fixedField V)
      simp only [Algebra.smul_def]
      change σ (algebraMap G.presentation (G.fixedField V) (a : G.presentation) *
          (b : G.fixedField V)) =
        algebraMap G.presentation (G.fixedField V) (a : G.presentation) *
          σ (b : G.fixedField V)
      rw [map_mul, σ.commutes]
    · constructor
      intro b hb
      have hbfield : ∀ σ : (G.fixedField V) ≃ₐ[G.presentation] (G.fixedField V),
          σ (b : G.fixedField V) = b := fun σ => congrArg Subtype.val (hb σ)
      obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant
        (A := G.presentation) (B := G.fixedField V) (b : G.fixedField V) hbfield
      have haint : valuation G.presentation a ≤ 1 := by
        rw [← (valuation G.presentation).vle_one_iff]
        rw [← ValuativeExtension.vle_iff_vle
          (A := G.presentation) (B := G.fixedField V), map_one]
        rw [(valuation (G.fixedField V)).vle_one_iff, ha]
        exact b.property
      refine ⟨⟨a, haint⟩, ?_⟩
      apply Subtype.ext
      exact ha
  letI : Algebra.IsIntegral (LocalIntegerRing G.presentation) 𝒪[G.fixedField V] :=
    (inferInstance : Algebra.IsInvariant (LocalIntegerRing G.presentation)
      𝒪[G.fixedField V]
      ((G.fixedField V) ≃ₐ[G.presentation] (G.fixedField V))).isIntegral
  letI : IsScalarTower (LocalIntegerRing G.presentation)
      G.presentation (G.fixedField V) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (LocalIntegerRing G.presentation)
      𝒪[G.fixedField V] (G.fixedField V) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsIntegralClosure 𝒪[G.fixedField V]
      (LocalIntegerRing G.presentation) (G.fixedField V) := by
    refine { algebraMap_injective := ?_, isIntegral_iff := ?_ }
    · intro x y h
      exact Subtype.ext h
    · intro x
      constructor
      · intro hx
        exact ⟨⟨x, Valuation.Integers.mem_of_integral
          (Valuation.integer.integers (valuation (G.fixedField V)))
          hx.tower_top⟩, rfl⟩
      · rintro ⟨y, rfl⟩
        exact (Algebra.IsIntegral.isIntegral y).algebraMap
  letI : Module.Finite (LocalIntegerRing G.presentation) 𝒪[G.fixedField V] :=
    IsIntegralClosure.finite (LocalIntegerRing G.presentation) G.presentation
      (G.fixedField V) 𝒪[G.fixedField V]
  letI : Finite
      (LocalIntegerRing G.presentation ⧸ localMaximalIdeal G.presentation) := by
    change Finite (LocalResidueField G.presentation)
    infer_instance
  letI : Finite (localMaximalIdeal G.presentation).ResidueField := inferInstance
  letI : PerfectField (localMaximalIdeal G.presentation).ResidueField := inferInstance
  calc
    Nat.card ((IsLocalRing.maximalIdeal 𝒪[G.fixedField V]).inertia
        ((G.fixedField V) ≃ₐ[G.presentation] (G.fixedField V))) =
        (localMaximalIdeal G.presentation).ramificationIdxIn
          𝒪[G.fixedField V] :=
      Ideal.card_inertia_eq_ramificationIdxIn
        (localMaximalIdeal G.presentation)
          (IsLocalRing.maximalIdeal 𝒪[G.fixedField V])
    _ = (IsLocalRing.maximalIdeal 𝒪[G.fixedField V]).ramificationIdx
        (LocalIntegerRing G.presentation) :=
      Ideal.ramificationIdxIn_eq_ramificationIdx
        (localMaximalIdeal G.presentation)
          (IsLocalRing.maximalIdeal 𝒪[G.fixedField V])
          ((G.fixedField V) ≃ₐ[G.presentation] (G.fixedField V))
    _ = E.relativeRamificationIndex :=
      E.relativeRamificationIndex_eq_ramificationIdx

end Anabelian.OTriangle.LocalGaloisGroup
