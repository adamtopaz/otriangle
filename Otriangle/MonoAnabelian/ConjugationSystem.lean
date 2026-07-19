import Otriangle.MonoAnabelian.FixedFieldComparison

/-!
# Conjugation on the fixed-field reconstruction system

An element of an absolute Galois group conjugates open subgroups and carries the fixed field of an
open subgroup to the fixed field of its conjugate.  These field equivalences preserve the spectral
valuation, hence act on the integral nodes and on their reconstructed reciprocity images.  The
nodewise maps commute with transfer and induce the intrinsic Galois action on the reconstructed
direct limit.
-/

noncomputable section

open CategoryTheory

namespace Anabelian

namespace OTriangle
namespace SpectralLocalField

/-- Algebra equivalences preserve the spectral norm, even when their source and target fields are
different presentations of the same algebraic extension. -/
theorem spectralNorm_eq_of_algEquiv {K E F : Type*} [NormedField K]
    [Field E] [Field F] [Algebra K E] [Algebra K F]
    (e : E ≃ₐ[K] F) (x : E) :
    spectralNorm K F (e x) = spectralNorm K E x := by
  simp only [spectralNorm, minpoly.algEquiv_eq]

end SpectralLocalField
end OTriangle

namespace LCFT
namespace ReconstructedIntegralMonoid

universe u

/-- The canonical action on the actual integral monoid, with its acting group expressed through
the bundled profinite realization of `G`. -/
@[implicit_reducible]
noncomputable def actualAction (G : OTriangle.LocalGaloisGroup.{u}) :
    MulDistribMulAction G.toProfiniteGrp G.presentation.integerMonoid := by
  change MulDistribMulAction
    (G.presentation.algebraicClosure ≃ₐ[G.presentation]
      G.presentation.algebraicClosure) G.presentation.integerMonoid
  exact OTriangle.PointedMixedCharLocalField.integerMonoidMulDistribMulAction G.presentation

end ReconstructedIntegralMonoid
end LCFT

namespace OTriangle
namespace LocalGaloisGroup

open ValuativeRel

universe u

variable (G : LocalGaloisGroup.{u})

/-- A bundled Galois-group element viewed as the corresponding algebra automorphism. -/
noncomputable def galoisElementAlgEquiv (σ : G.toProfiniteGrp) :
    G.presentation.algebraicClosure ≃ₐ[G.presentation]
      G.presentation.algebraicClosure := by
  change (G.presentation.algebraicClosure ≃ₐ[G.presentation]
    G.presentation.algebraicClosure) at σ
  exact σ

/-- Inner conjugation by a Galois-group element as a continuous group equivalence. -/
noncomputable def conjugationEquiv (σ : G.toProfiniteGrp) :
    G.toProfiniteGrp ≃ₜ* G.toProfiniteGrp where
  toFun τ := σ * τ * σ⁻¹
  invFun τ := σ⁻¹ * τ * σ
  left_inv τ := by simp [mul_assoc]
  right_inv τ := by simp [mul_assoc]
  map_mul' τ υ := by simp [mul_assoc]
  continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const
  continuous_invFun := (continuous_const.mul continuous_id).mul continuous_const

/-- Inner conjugation as a morphism of local Galois-group presentations. -/
noncomputable def conjugationHom (σ : G.toProfiniteGrp) : G ⟶ G :=
  ⟨G.conjugationEquiv σ⟩

/-- Conjugation transports the reverse-inclusion index of open subgroups. -/
noncomputable def conjugationIndex (σ : G.toProfiniteGrp) :
    G.OpenSubgroupIndex ≃o G.OpenSubgroupIndex :=
  G.openSubgroupIndexEquiv (G.conjugationHom σ)

/-- Applying a Galois element carries the fixed field of `U` to the fixed field of the conjugate
subgroup. -/
noncomputable def fixedFieldConjugationEquiv
    (σ : G.toProfiniteGrp) (U : G.OpenSubgroupIndex) :
    G.fixedField U ≃ₐ[G.presentation] G.fixedField (G.conjugationIndex σ U) where
  toFun x := ⟨G.galoisElementAlgEquiv σ x, by
    rw [IntermediateField.mem_fixedField_iff]
    intro τ hτ
    have hmem : (G.conjugationEquiv σ).symm τ ∈ OrderDual.ofDual U := hτ
    let γ := G.galoisElementAlgEquiv ((G.conjugationEquiv σ).symm τ)
    have hfix := (IntermediateField.mem_fixedField_iff
      (H := (OrderDual.ofDual U).toSubgroup)
      (x : G.presentation.algebraicClosure)).mp x.property γ hmem
    change τ (G.galoisElementAlgEquiv σ x) = G.galoisElementAlgEquiv σ x
    have hτeq : τ = G.galoisElementAlgEquiv σ * γ *
        (G.galoisElementAlgEquiv σ)⁻¹ := by
      have h := congrArg (galoisElementAlgEquiv G)
        ((G.conjugationEquiv σ).apply_symm_apply τ)
      change G.galoisElementAlgEquiv σ * γ *
        (G.galoisElementAlgEquiv σ)⁻¹ = τ at h
      exact h.symm
    rw [hτeq]
    simp [hfix]⟩
  invFun y := ⟨(G.galoisElementAlgEquiv σ)⁻¹ y, by
    rw [IntermediateField.mem_fixedField_iff]
    intro τ hτ
    have hmap : G.conjugationEquiv σ τ ∈
        OrderDual.ofDual (G.conjugationIndex σ U) := by
      change (G.conjugationEquiv σ).symm (G.conjugationEquiv σ τ) ∈
        (OrderDual.ofDual U).toSubgroup
      change τ ∈ (OrderDual.ofDual U).toSubgroup at hτ
      simpa only [ContinuousMulEquiv.symm_apply_apply]
    let γ := G.galoisElementAlgEquiv (G.conjugationEquiv σ τ)
    have hfix := (IntermediateField.mem_fixedField_iff
      (H := (OrderDual.ofDual (G.conjugationIndex σ U)).toSubgroup)
      (y : G.presentation.algebraicClosure)).mp y.property γ hmap
    change τ ((G.galoisElementAlgEquiv σ)⁻¹ y) =
      (G.galoisElementAlgEquiv σ)⁻¹ y
    have hτeq : τ = (G.galoisElementAlgEquiv σ)⁻¹ * γ *
        G.galoisElementAlgEquiv σ := by
      have h := congrArg (galoisElementAlgEquiv G)
        ((G.conjugationEquiv σ).symm_apply_apply τ)
      change (G.galoisElementAlgEquiv σ)⁻¹ * γ *
        G.galoisElementAlgEquiv σ = τ at h
      exact h.symm
    rw [hτeq]
    simp [hfix]⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_add' x y := by
    apply Subtype.ext
    exact map_add (G.galoisElementAlgEquiv σ)
      (x : G.presentation.algebraicClosure) y
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (G.galoisElementAlgEquiv σ)
      (x : G.presentation.algebraicClosure) y
  commutes' x := by
    ext
    exact (G.galoisElementAlgEquiv σ).commutes x

/-- Conjugation preserves membership in the spectral integral monoid of a fixed field. -/
theorem mem_fixedFieldBaseIntegerMonoid_conjugation_iff
    (σ : G.toProfiniteGrp) (U : G.OpenSubgroupIndex) (x : (G.fixedField U)ˣ) :
    x ∈ LCFT.baseIntegerMonoid (G.fixedFieldPointed U) ↔
      Units.mapEquiv (G.fixedFieldConjugationEquiv σ U).toMulEquiv x ∈
        LCFT.baseIntegerMonoid (G.fixedFieldPointed (G.conjugationIndex σ U)) := by
  letI := G.presentation.nontriviallyNormedField
  letI := G.presentation.isUltrametricDist
  letI := G.presentation.completeSpace
  letI := G.fixedFieldNontriviallyNormedField U
  letI := G.fixedFieldIsUltrametricDist U
  letI : ValuativeRel (G.fixedField U) := G.fixedFieldValuativeRel U
  letI : (NormedField.valuation (K := G.fixedField U)).Compatible :=
    Valuation.Compatible.ofValuation _
  letI := G.fixedFieldNontriviallyNormedField (G.conjugationIndex σ U)
  letI := G.fixedFieldIsUltrametricDist (G.conjugationIndex σ U)
  letI : ValuativeRel (G.fixedField (G.conjugationIndex σ U)) :=
    G.fixedFieldValuativeRel (G.conjugationIndex σ U)
  letI : (NormedField.valuation
      (K := G.fixedField (G.conjugationIndex σ U))).Compatible :=
    Valuation.Compatible.ofValuation _
  change valuation (G.fixedField U) (x : G.fixedField U) ≤ 1 ↔
    valuation (G.fixedField (G.conjugationIndex σ U))
      (G.fixedFieldConjugationEquiv σ U (x : G.fixedField U)) ≤ 1
  rw [← (valuation (G.fixedField U)).vle_one_iff,
    (NormedField.valuation (K := G.fixedField U)).vle_one_iff]
  rw [← (valuation (G.fixedField (G.conjugationIndex σ U))).vle_one_iff,
    (NormedField.valuation
      (K := G.fixedField (G.conjugationIndex σ U))).vle_one_iff]
  change spectralNorm G.presentation (G.fixedField U) x ≤ 1 ↔
    spectralNorm G.presentation (G.fixedField (G.conjugationIndex σ U))
      (G.fixedFieldConjugationEquiv σ U x) ≤ 1
  rw [SpectralLocalField.spectralNorm_eq_of_algEquiv
    (G.fixedFieldConjugationEquiv σ U) x]

/-- Conjugation restricts to an equivalence of the field-theoretic integral nodes. -/
noncomputable def fixedFieldBaseIntegerMonoidConjugationEquiv
    (σ : G.toProfiniteGrp) (U : G.OpenSubgroupIndex) :
    LCFT.baseIntegerMonoid (G.fixedFieldPointed U) ≃*
      LCFT.baseIntegerMonoid (G.fixedFieldPointed (G.conjugationIndex σ U)) where
  toFun x := ⟨Units.mapEquiv (G.fixedFieldConjugationEquiv σ U).toMulEquiv x, by
    exact (G.mem_fixedFieldBaseIntegerMonoid_conjugation_iff σ U x).mp x.property⟩
  invFun y := ⟨Units.mapEquiv
      (G.fixedFieldConjugationEquiv σ U).symm.toMulEquiv y, by
    apply (G.mem_fixedFieldBaseIntegerMonoid_conjugation_iff σ U
      (Units.mapEquiv (G.fixedFieldConjugationEquiv σ U).symm.toMulEquiv y)).mpr
    have hunit : Units.mapEquiv (G.fixedFieldConjugationEquiv σ U).toMulEquiv
        (Units.mapEquiv (G.fixedFieldConjugationEquiv σ U).symm.toMulEquiv y) = y := by
      ext
      simp
    rw [hunit]
    exact y.property⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by
    apply Subtype.ext
    apply Units.ext
    simp

/-- Conjugation of the field-theoretic nodes commutes with fixed-field inclusion. -/
theorem fixedFieldBaseIntegerMonoidConjugationEquiv_natural
    (σ : G.toProfiniteGrp) (U V : G.OpenSubgroupIndex) (h : U ≤ V) :
    (G.fixedFieldBaseIntegerMonoidConjugationEquiv σ V).toMonoidHom.comp
        ((G.fixedFieldFiniteExtensionSystem).baseTransition U V h) =
      ((G.fixedFieldFiniteExtensionSystem).baseTransition
        (G.conjugationIndex σ U) (G.conjugationIndex σ V)
        ((G.conjugationIndex σ).monotone h)).comp
        (G.fixedFieldBaseIntegerMonoidConjugationEquiv σ U).toMonoidHom := by
  ext x
  apply Subtype.ext
  rfl

/-- Conjugation on a reconstructed node, transported through the one-field reciprocity
equivalences. -/
noncomputable def reconstructedNodeConjugationEquiv
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (σ : G.toProfiniteGrp) (U : G.OpenSubgroupIndex) :
    (G.fixedFieldFiniteExtensionSystem).reconstructedNode reciprocity U ≃*
      (G.fixedFieldFiniteExtensionSystem).reconstructedNode reciprocity
        (G.conjugationIndex σ U) :=
  (reciprocity.baseIntegerMonoidEquiv
    ((G.fixedFieldFiniteExtensionSystem).field U)).symm.trans
    ((G.fixedFieldBaseIntegerMonoidConjugationEquiv σ U).trans
      (reciprocity.baseIntegerMonoidEquiv
        ((G.fixedFieldFiniteExtensionSystem).field (G.conjugationIndex σ U))))

@[simp]
theorem reconstructedNodeConjugationEquiv_apply
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (σ : G.toProfiniteGrp) (U : G.OpenSubgroupIndex)
    (x : (G.fixedFieldFiniteExtensionSystem).reconstructedNode reciprocity U) :
    G.reconstructedNodeConjugationEquiv reciprocity σ U x =
      reciprocity.baseIntegerMonoidEquiv
        ((G.fixedFieldFiniteExtensionSystem).field (G.conjugationIndex σ U))
        (G.fixedFieldBaseIntegerMonoidConjugationEquiv σ U
          ((reciprocity.baseIntegerMonoidEquiv
            ((G.fixedFieldFiniteExtensionSystem).field U)).symm x)) :=
  rfl

@[simp]
theorem reconstructedNodeConjugationEquiv_toMonoidHom_apply
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (σ : G.toProfiniteGrp) (U : G.OpenSubgroupIndex)
    (x : (G.fixedFieldFiniteExtensionSystem).reconstructedNode reciprocity U) :
    (G.reconstructedNodeConjugationEquiv reciprocity σ U).toMonoidHom x =
      reciprocity.baseIntegerMonoidEquiv
        ((G.fixedFieldFiniteExtensionSystem).field (G.conjugationIndex σ U))
        (G.fixedFieldBaseIntegerMonoidConjugationEquiv σ U
          ((reciprocity.baseIntegerMonoidEquiv
            ((G.fixedFieldFiniteExtensionSystem).field U)).symm x)) :=
  rfl

/-- The reconstructed node conjugations commute with the transfer transitions. -/
theorem reconstructedNodeConjugationEquiv_natural
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (σ : G.toProfiniteGrp) (U V : G.OpenSubgroupIndex) (h : U ≤ V) :
    (G.reconstructedNodeConjugationEquiv reciprocity σ V).toMonoidHom.comp
        ((G.fixedFieldFiniteExtensionSystem).reconstructedTransition
          reciprocity U V h) =
      ((G.fixedFieldFiniteExtensionSystem).reconstructedTransition reciprocity
        (G.conjugationIndex σ U) (G.conjugationIndex σ V)
        ((G.conjugationIndex σ).monotone h)).comp
        (G.reconstructedNodeConjugationEquiv reciprocity σ U).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  simp only [MonoidHom.comp_apply]
  rw [(G.fixedFieldFiniteExtensionSystem).reconstructedTransition_apply reciprocity,
    (G.fixedFieldFiniteExtensionSystem).reconstructedTransition_apply reciprocity]
  rw [G.reconstructedNodeConjugationEquiv_toMonoidHom_apply,
    G.reconstructedNodeConjugationEquiv_toMonoidHom_apply,
    MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  change reciprocity.baseIntegerMonoidEquiv _
      (G.fixedFieldBaseIntegerMonoidConjugationEquiv σ V
        ((G.fixedFieldFiniteExtensionSystem).baseTransition U V h
          ((reciprocity.baseIntegerMonoidEquiv _).symm x))) =
    reciprocity.baseIntegerMonoidEquiv _
      ((G.fixedFieldFiniteExtensionSystem).baseTransition _ _ _
        (G.fixedFieldBaseIntegerMonoidConjugationEquiv σ U
          ((reciprocity.baseIntegerMonoidEquiv _).symm x)))
  exact congrArg (reciprocity.baseIntegerMonoidEquiv _)
    (DFunLike.congr_fun
      (G.fixedFieldBaseIntegerMonoidConjugationEquiv_natural σ U V h)
      ((reciprocity.baseIntegerMonoidEquiv _).symm x))

/-- The carrier reconstructed as the transfer colimit over open subgroups. -/
abbrev reconstructedDirectLimit (reciprocity : LCFT.LocalReciprocityFamily.{u}) : Type u :=
  DirectLimit ((G.fixedFieldFiniteExtensionSystem).reconstructedNode reciprocity)
    ((G.fixedFieldFiniteExtensionSystem).reconstructedTransition reciprocity)

/-- A Galois element acts on the reconstructed direct limit through conjugation of the
open-subgroup diagram. -/
noncomputable def reconstructedDirectLimitConjugationEquiv
    (reciprocity : LCFT.LocalReciprocityFamily.{u}) (σ : G.toProfiniteGrp) :
    G.reconstructedDirectLimit reciprocity ≃* G.reconstructedDirectLimit reciprocity :=
  LCFT.FilteredColimit.mulEquivAlongOrderIso
    ((G.fixedFieldFiniteExtensionSystem).reconstructedTransition reciprocity)
    ((G.fixedFieldFiniteExtensionSystem).reconstructedTransition reciprocity)
    (G.conjugationIndex σ) (G.reconstructedNodeConjugationEquiv reciprocity σ)
    (G.reconstructedNodeConjugationEquiv_natural reciprocity σ)

@[simp]
theorem reconstructedDirectLimitConjugationEquiv_mk
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (σ : G.toProfiniteGrp) (U : G.OpenSubgroupIndex)
    (x : (G.fixedFieldFiniteExtensionSystem).reconstructedNode reciprocity U) :
    G.reconstructedDirectLimitConjugationEquiv reciprocity σ
        (⟦⟨U, x⟩⟧ : G.reconstructedDirectLimit reciprocity) =
      (⟦⟨G.conjugationIndex σ U,
        G.reconstructedNodeConjugationEquiv reciprocity σ U x⟩⟧ :
        G.reconstructedDirectLimit reciprocity) :=
  rfl

@[simp]
theorem fixedFieldSystemDirectLimitEquiv_symm_mk
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (U : G.OpenSubgroupIndex)
    (x : (G.fixedFieldFiniteExtensionSystem).reconstructedNode reciprocity U) :
    ((G.fixedFieldFiniteExtensionSystem).directLimitEquiv reciprocity).symm
        (⟦⟨U, x⟩⟧ : G.reconstructedDirectLimit reciprocity) =
      (⟦⟨U, (reciprocity.baseIntegerMonoidEquiv
        ((G.fixedFieldFiniteExtensionSystem).field U)).symm x⟩⟧ :
        DirectLimit (G.fixedFieldFiniteExtensionSystem).baseNode
          (G.fixedFieldFiniteExtensionSystem).baseTransition) := by
  apply ((G.fixedFieldFiniteExtensionSystem).directLimitEquiv reciprocity).injective
  rw [MulEquiv.apply_symm_apply,
    (G.fixedFieldFiniteExtensionSystem).directLimitEquiv_mk,
    MulEquiv.apply_symm_apply]

@[simp]
theorem fixedFieldBaseDirectLimitEquiv_mk (U : G.OpenSubgroupIndex)
    (x : (G.fixedFieldFiniteExtensionSystem).baseNode U) :
    G.fixedFieldBaseDirectLimitEquiv
        (⟦⟨U, x⟩⟧ : DirectLimit (G.fixedFieldFiniteExtensionSystem).baseNode
          (G.fixedFieldFiniteExtensionSystem).baseTransition) =
      (⟦⟨U, G.fixedFieldBaseIntegerMonoidEquiv U x⟩⟧ :
        DirectLimit G.fixedFieldIntegerMonoid G.fixedFieldIntegerTransition) :=
  rfl

@[simp]
theorem fixedFieldReconstructedDirectLimitEquiv_symm_mk
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (U : G.OpenSubgroupIndex)
    (x : (G.fixedFieldFiniteExtensionSystem).reconstructedNode reciprocity U) :
    (G.fixedFieldReconstructedDirectLimitEquiv reciprocity).symm
        (⟦⟨U, x⟩⟧ : G.reconstructedDirectLimit reciprocity) =
      G.fixedFieldToIntegerMonoid U
        (G.fixedFieldBaseIntegerMonoidEquiv U
          ((reciprocity.baseIntegerMonoidEquiv
            ((G.fixedFieldFiniteExtensionSystem).field U)).symm x)) := by
  change G.fixedFieldDirectLimitEquiv
      (G.fixedFieldBaseDirectLimitEquiv
        (((G.fixedFieldFiniteExtensionSystem).directLimitEquiv reciprocity).symm
          (⟦⟨U, x⟩⟧ : G.reconstructedDirectLimit reciprocity))) = _
  rw [G.fixedFieldSystemDirectLimitEquiv_symm_mk,
    G.fixedFieldBaseDirectLimitEquiv_mk, G.fixedFieldDirectLimitEquiv_mk]

/-- Under the fixed-field comparison, the intrinsic conjugation map is the usual Galois action. -/
theorem fixedFieldReconstructedDirectLimitEquiv_symm_conjugation
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (σ : G.toProfiniteGrp) (z : G.reconstructedDirectLimit reciprocity) :
    (G.fixedFieldReconstructedDirectLimitEquiv reciprocity).symm
        (G.reconstructedDirectLimitConjugationEquiv reciprocity σ z) =
      (LCFT.ReconstructedIntegralMonoid.actualAction G).smul σ
        ((G.fixedFieldReconstructedDirectLimitEquiv reciprocity).symm z) := by
  induction z using DirectLimit.induction with
  | _ U x =>
      rw [G.reconstructedDirectLimitConjugationEquiv_mk,
        G.fixedFieldReconstructedDirectLimitEquiv_symm_mk,
        G.fixedFieldReconstructedDirectLimitEquiv_symm_mk]
      simp only [G.reconstructedNodeConjugationEquiv_apply,
        MulEquiv.symm_apply_apply]
      apply Subtype.ext
      apply Subtype.ext
      rfl

/-- The conjugation automorphism associated to the identity element is the identity. -/
theorem reconstructedDirectLimitConjugationEquiv_one
    (reciprocity : LCFT.LocalReciprocityFamily.{u}) :
    G.reconstructedDirectLimitConjugationEquiv reciprocity 1 = MulEquiv.refl _ := by
  apply MulEquiv.ext
  intro z
  apply (G.fixedFieldReconstructedDirectLimitEquiv reciprocity).symm.injective
  rw [G.fixedFieldReconstructedDirectLimitEquiv_symm_conjugation]
  exact (LCFT.ReconstructedIntegralMonoid.actualAction G).one_smul _

/-- Conjugation automorphisms multiply in the order required by a left Galois action. -/
theorem reconstructedDirectLimitConjugationEquiv_mul
    (reciprocity : LCFT.LocalReciprocityFamily.{u}) (σ τ : G.toProfiniteGrp) :
    G.reconstructedDirectLimitConjugationEquiv reciprocity (σ * τ) =
      (G.reconstructedDirectLimitConjugationEquiv reciprocity τ).trans
        (G.reconstructedDirectLimitConjugationEquiv reciprocity σ) := by
  apply MulEquiv.ext
  intro z
  change G.reconstructedDirectLimitConjugationEquiv reciprocity (σ * τ) z =
    G.reconstructedDirectLimitConjugationEquiv reciprocity σ
      (G.reconstructedDirectLimitConjugationEquiv reciprocity τ z)
  apply (G.fixedFieldReconstructedDirectLimitEquiv reciprocity).symm.injective
  rw [G.fixedFieldReconstructedDirectLimitEquiv_symm_conjugation,
    G.fixedFieldReconstructedDirectLimitEquiv_symm_conjugation,
    G.fixedFieldReconstructedDirectLimitEquiv_symm_conjugation]
  exact (LCFT.ReconstructedIntegralMonoid.actualAction G).mul_smul σ τ _

/-- The intrinsic Galois action on the reconstructed transfer colimit. -/
@[implicit_reducible]
noncomputable def reconstructedDirectLimitAction
    (reciprocity : LCFT.LocalReciprocityFamily.{u}) :
    MulDistribMulAction G.toProfiniteGrp (G.reconstructedDirectLimit reciprocity) where
  smul σ x := G.reconstructedDirectLimitConjugationEquiv reciprocity σ x
  one_smul x := by
    change G.reconstructedDirectLimitConjugationEquiv reciprocity 1 x = x
    have h := congrArg (fun e : G.reconstructedDirectLimit reciprocity ≃*
        G.reconstructedDirectLimit reciprocity ↦ e x)
      (G.reconstructedDirectLimitConjugationEquiv_one reciprocity)
    simpa using h
  mul_smul σ τ x := by
    change G.reconstructedDirectLimitConjugationEquiv reciprocity (σ * τ) x =
      G.reconstructedDirectLimitConjugationEquiv reciprocity σ
        (G.reconstructedDirectLimitConjugationEquiv reciprocity τ x)
    have h := congrArg (fun e : G.reconstructedDirectLimit reciprocity ≃*
        G.reconstructedDirectLimit reciprocity ↦ e x)
      (G.reconstructedDirectLimitConjugationEquiv_mul reciprocity σ τ)
    exact h
  smul_one σ := (G.reconstructedDirectLimitConjugationEquiv reciprocity σ).map_one
  smul_mul σ x y :=
    (G.reconstructedDirectLimitConjugationEquiv reciprocity σ).map_mul x y

@[simp]
theorem reconstructedDirectLimitAction_smul
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (σ : G.toProfiniteGrp) (x : G.reconstructedDirectLimit reciprocity) :
    (G.reconstructedDirectLimitAction reciprocity).smul σ x =
      G.reconstructedDirectLimitConjugationEquiv reciprocity σ x :=
  rfl

/-- The fixed-field comparison is equivariant for the canonical and intrinsic actions. -/
theorem fixedFieldReconstructedDirectLimitEquiv_action
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (σ : G.toProfiniteGrp) (x : G.presentation.integerMonoid) :
    G.fixedFieldReconstructedDirectLimitEquiv reciprocity
        ((LCFT.ReconstructedIntegralMonoid.actualAction G).smul σ x) =
      (G.reconstructedDirectLimitAction reciprocity).smul σ
        (G.fixedFieldReconstructedDirectLimitEquiv reciprocity x) := by
  rw [G.reconstructedDirectLimitAction_smul]
  apply (G.fixedFieldReconstructedDirectLimitEquiv reciprocity).symm.injective
  rw [MulEquiv.symm_apply_apply]
  rw [G.fixedFieldReconstructedDirectLimitEquiv_symm_conjugation,
    MulEquiv.symm_apply_apply]

end LocalGaloisGroup
end OTriangle
end Anabelian
