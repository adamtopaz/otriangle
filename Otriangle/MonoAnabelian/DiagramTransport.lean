import Otriangle.MonoAnabelian.RamificationComparison
import Otriangle.MonoAnabelian.FixedFieldSystem

/-!
# Transport of the fixed-field reconstruction diagram

This module proves the naturality squares needed to pass nodewise Hoshi transport to the filtered
fixed-field diagram.  The first step identifies the canonical abelianized restriction map of a
fixed-field extension with literal inclusion of the corresponding open subgroups; the arbitrary
algebraic-closure comparison in its definition disappears by inner-conjugacy in abelianization.
-/

noncomputable section

open scoped commutatorElement

namespace Anabelian
namespace OTriangle

universe u

/-- Inner conjugation acts trivially after passage to the topological abelianization. -/
theorem topologicalAbelianization_mk_autCongr
    {k A : Type*} [Field k] [Field A] [Algebra k A]
    (e σ : A ≃ₐ[k] A) :
    QuotientGroup.mk' (Subgroup.topologicalClosure (commutator (A ≃ₐ[k] A)))
        (AlgEquiv.autCongr e σ) =
      QuotientGroup.mk' (Subgroup.topologicalClosure (commutator (A ≃ₐ[k] A))) σ := by
  have hconj : AlgEquiv.autCongr e σ = e * σ * e⁻¹ := by
    ext x
    rfl
  rw [hconj, map_mul, map_mul, map_inv]
  simp [mul_comm]

namespace LocalGaloisGroup

/-- For a tower of fixed fields, the canonical abelianized Galois map is literal inclusion of the
smaller open subgroup into the larger one under the fixed-field Galois identifications. -/
theorem fixedField_abelianizedGaloisMap_mk
    (G : LocalGaloisGroup.{u}) {U V : G.OpenSubgroupIndex} (h : U ≤ V)
    (σ : (OrderDual.ofDual V).toSubgroup) :
    (G.fixedFieldFiniteExtension h).abelianizedGaloisMap
        (QuotientGroup.mk'
          (Subgroup.topologicalClosure
            (commutator
              (LCFT.AbsoluteGaloisGroup (G.fixedFieldPointed V))))
          (G.fixedFieldGaloisContinuousEquiv V σ)) =
      QuotientGroup.mk'
        (Subgroup.topologicalClosure
          (commutator
            (LCFT.AbsoluteGaloisGroup (G.fixedFieldPointed U))))
        (G.fixedFieldGaloisContinuousEquiv U ⟨σ, h σ.property⟩) := by
  let E := G.fixedFieldFiniteExtension h
  letI : Algebra (G.fixedField U) (G.fixedField V) := E.algebra
  letI : FiniteDimensional (G.fixedField U) (G.fixedField V) :=
    E.finiteDimensional
  letI : IsAlgClosure (G.fixedField U) G.presentation.algebraicClosure :=
    G.fixedFieldIsAlgClosure U
  letI : IsAlgClosure (G.fixedField V) G.presentation.algebraicClosure :=
    G.fixedFieldIsAlgClosure V
  letI : IsScalarTower (G.fixedField U) (G.fixedField V)
      G.presentation.algebraicClosure := IsScalarTower.of_algebraMap_eq' rfl
  rw [LCFT.FiniteExtension.abelianizedGaloisMap_mk]
  let e : G.presentation.algebraicClosure ≃ₐ[G.fixedField U]
      G.presentation.algebraicClosure :=
    IsAlgClosure.equiv (G.fixedField U) G.presentation.algebraicClosure
      G.presentation.algebraicClosure
  change QuotientGroup.mk'
      (Subgroup.topologicalClosure
        (commutator
          (G.presentation.algebraicClosure ≃ₐ[G.fixedField U]
            G.presentation.algebraicClosure)))
      (AlgEquiv.autCongr e
        ((G.fixedFieldGaloisContinuousEquiv V σ).restrictScalars (G.fixedField U))) = _
  rw [topologicalAbelianization_mk_autCongr]
  congr 1

/-- Abelianized restriction along a tower of fixed fields is natural under arbitrary transport of
the ambient profinite group. -/
theorem fixedFieldAbelianizationEquiv_abelianizedGaloisMap
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H)
    {U V : G.OpenSubgroupIndex} (h : U ≤ V) :
    (G.fixedFieldAbelianizationEquiv f U).toMonoidHom.comp
        (G.fixedFieldFiniteExtension h).abelianizedGaloisMap =
      (H.fixedFieldFiniteExtension
          ((G.openSubgroupIndexEquiv f).le_iff_le.mpr h)).abelianizedGaloisMap.comp
        (G.fixedFieldAbelianizationEquiv f V).toMonoidHom := by
  ext σ
  let τ : (OrderDual.ofDual V).toSubgroup :=
    (G.fixedFieldGaloisContinuousEquiv V).symm σ
  let U' := G.openSubgroupIndexEquiv f U
  let V' := G.openSubgroupIndexEquiv f V
  let h' : U' ≤ V' := (G.openSubgroupIndexEquiv f).le_iff_le.mpr h
  let τU : (OrderDual.ofDual U).toSubgroup := ⟨τ, h τ.property⟩
  let τ' : (OrderDual.ofDual V').toSubgroup := G.openSubgroupEquiv f V τ
  let τU' : (OrderDual.ofDual U').toSubgroup := ⟨τ', h' τ'.property⟩
  have hστ : G.fixedFieldGaloisContinuousEquiv V τ = σ :=
    (G.fixedFieldGaloisContinuousEquiv V).apply_symm_apply σ
  have hmapV : (G.fixedFieldGroupHom f V).equiv
      (G.fixedFieldGaloisContinuousEquiv V τ) =
        H.fixedFieldGaloisContinuousEquiv V' τ' := by
    change H.fixedFieldGaloisContinuousEquiv V'
        (G.openSubgroupEquiv f V
          ((G.fixedFieldGaloisContinuousEquiv V).symm
            (G.fixedFieldGaloisContinuousEquiv V τ))) =
      H.fixedFieldGaloisContinuousEquiv V' τ'
    rw [(G.fixedFieldGaloisContinuousEquiv V).symm_apply_apply]
  have hmapU : (G.fixedFieldGroupHom f U).equiv
      (G.fixedFieldGaloisContinuousEquiv U τU) =
        H.fixedFieldGaloisContinuousEquiv U' τU' := by
    change H.fixedFieldGaloisContinuousEquiv U'
        (G.openSubgroupEquiv f U
          ((G.fixedFieldGaloisContinuousEquiv U).symm
            (G.fixedFieldGaloisContinuousEquiv U τU))) =
      H.fixedFieldGaloisContinuousEquiv U' τU'
    rw [(G.fixedFieldGaloisContinuousEquiv U).symm_apply_apply]
    congr 1
  rw [← hστ]
  simp only [MonoidHom.comp_apply]
  change G.fixedFieldAbelianizationEquiv f U
      ((G.fixedFieldFiniteExtension h).abelianizedGaloisMap _) =
    (H.fixedFieldFiniteExtension
      ((G.openSubgroupIndexEquiv f).le_iff_le.mpr h)).abelianizedGaloisMap
        (G.fixedFieldAbelianizationEquiv f V _)
  rw [fixedField_abelianizedGaloisMap_mk,
    fixedFieldAbelianizationEquiv_mk, fixedFieldAbelianizationEquiv_mk]
  rw [hmapU, hmapV, fixedField_abelianizedGaloisMap_mk]

/-- Transfer on the abelianizations of corresponding fixed-field towers is natural under the
restricted group isomorphisms. -/
theorem fixedFieldAbelianizationEquiv_transferMap
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H)
    {U V : G.OpenSubgroupIndex} (h : U ≤ V)
    (reciprocity : LCFT.LocalReciprocityFamily.{u}) :
    (G.fixedFieldAbelianizationEquiv f V).toMonoidHom.comp
        (reciprocity.transferMap (G.fixedFieldPointed U) (G.fixedFieldPointed V)
          (G.fixedFieldFiniteExtension h)) =
      (reciprocity.transferMap
          (H.fixedFieldPointed (G.openSubgroupIndexEquiv f U))
          (H.fixedFieldPointed (G.openSubgroupIndexEquiv f V))
          (H.fixedFieldFiniteExtension
            ((G.openSubgroupIndexEquiv f).le_iff_le.mpr h))).comp
        (G.fixedFieldAbelianizationEquiv f U).toMonoidHom :=
  reciprocity.transfer_equiv_naturality
    (G.fixedFieldPointed U) (G.fixedFieldPointed V)
    (H.fixedFieldPointed (G.openSubgroupIndexEquiv f U))
    (H.fixedFieldPointed (G.openSubgroupIndexEquiv f V))
    (G.fixedFieldFiniteExtension h)
    (H.fixedFieldFiniteExtension ((G.openSubgroupIndexEquiv f).le_iff_le.mpr h))
    (G.fixedFieldAbelianizationEquiv f U)
    (G.fixedFieldAbelianizationEquiv f V)
    (G.fixedFieldAbelianizationEquiv_abelianizedGaloisMap f h)

/-- The Hoshi node equivalences commute with the reconstructed transfer transitions. -/
theorem fixedFieldReconstructedNodeEquiv_natural
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H)
    {U V : G.OpenSubgroupIndex} (h : U ≤ V)
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (hoshi : HoshiRamificationComparisonFamily.{u}) :
    (fixedFieldReconstructedNodeEquiv f V reciprocity hoshi).toMonoidHom.comp
        (reciprocity.reconstructedBaseIntegerMonoidMap
          (G.fixedFieldFiniteExtension h)) =
      (reciprocity.reconstructedBaseIntegerMonoidMap
          (H.fixedFieldFiniteExtension
            ((G.openSubgroupIndexEquiv f).le_iff_le.mpr h))).comp
        (fixedFieldReconstructedNodeEquiv f U reciprocity hoshi).toMonoidHom := by
  ext x
  simp only [MonoidHom.comp_apply]
  change ((fixedFieldReconstructedNodeEquiv f V reciprocity hoshi
      (reciprocity.reconstructedBaseIntegerMonoidMap
        (G.fixedFieldFiniteExtension h) x)).1) =
    (reciprocity.reconstructedBaseIntegerMonoidMap
      (H.fixedFieldFiniteExtension
        ((G.openSubgroupIndexEquiv f).le_iff_le.mpr h))
      (fixedFieldReconstructedNodeEquiv f U reciprocity hoshi x)).1
  rw [fixedFieldReconstructedNodeEquiv_apply_coe,
    reciprocity.reconstructedBaseIntegerMonoidMap_coe,
    reciprocity.reconstructedBaseIntegerMonoidMap_coe,
    fixedFieldReconstructedNodeEquiv_apply_coe]
  exact DFunLike.congr_fun
    (G.fixedFieldAbelianizationEquiv_transferMap f h reciprocity) x.1

end LocalGaloisGroup
end OTriangle
end Anabelian
