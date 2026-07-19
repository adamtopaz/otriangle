import Otriangle.MonoAnabelian.ConjugationSystem

/-!
# Abelianized transport along profinite-group isomorphisms

This module develops the presentation-independent group theory needed for arbitrary transport.
A continuous group equivalence induces an equivalence of topological abelianizations.  For an
open subgroup of a local Galois group, its topological abelianization is then identified with the
abelianized absolute Galois group of the corresponding fixed field.
-/

noncomputable section

open CategoryTheory
open scoped commutatorElement

namespace Anabelian
namespace OTriangle
namespace TopologicalAbelianization

/-- A continuous group homomorphism descends to topological abelianizations. -/
noncomputable def map
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
    (f : G →* H) (hf : Continuous f) :
    _root_.TopologicalAbelianization G →* _root_.TopologicalAbelianization H :=
  QuotientGroup.map (Subgroup.topologicalClosure (commutator G))
    (Subgroup.topologicalClosure (commutator H)) f (by
      apply Subgroup.topologicalClosure_minimal
        (t := Subgroup.comap f (Subgroup.topologicalClosure (commutator H)))
      · change ⁅(⊤ : Subgroup G), ⊤⁆ ≤
          Subgroup.comap f (Subgroup.topologicalClosure (commutator H))
        rw [Subgroup.commutator_le]
        intro g _ h _
        change f ⁅g, h⁆ ∈ Subgroup.topologicalClosure (commutator H)
        rw [map_commutatorElement]
        exact Subgroup.le_topologicalClosure _
          (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
      · change IsClosed (f ⁻¹' (Subgroup.topologicalClosure (commutator H) : Set H))
        exact (Subgroup.isClosed_topologicalClosure _).preimage hf)

/-- A continuous group equivalence induces an equivalence of topological abelianizations. -/
noncomputable def congr
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) :
    _root_.TopologicalAbelianization G ≃* _root_.TopologicalAbelianization H where
  toFun := map e.toMulEquiv.toMonoidHom e.continuous
  invFun := map e.symm.toMulEquiv.toMonoidHom e.symm.continuous
  left_inv x := by
    induction x using Quotient.inductionOn with
    | _ g => exact congrArg (QuotientGroup.mk'
        (Subgroup.topologicalClosure (commutator G))) (e.symm_apply_apply g)
  right_inv y := by
    induction y using Quotient.inductionOn with
    | _ h => exact congrArg (QuotientGroup.mk'
        (Subgroup.topologicalClosure (commutator H))) (e.apply_symm_apply h)
  map_mul' := (map e.toMulEquiv.toMonoidHom e.continuous).map_mul

@[simp]
theorem congr_mk
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) (g : G) :
    congr e (QuotientGroup.mk' (Subgroup.topologicalClosure (commutator G)) g) =
      QuotientGroup.mk' (Subgroup.topologicalClosure (commutator H)) (e g) :=
  rfl

@[simp]
theorem congr_refl
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    congr (ContinuousMulEquiv.refl G) =
      MulEquiv.refl (_root_.TopologicalAbelianization G) := by
  apply MulEquiv.ext
  intro x
  induction x using Quotient.inductionOn with
  | _ g => rfl

/-- Equivalences of topological abelianizations respect composition. -/
theorem congr_trans
    {G H I : Type*} [Group G] [Group H] [Group I]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace I]
    [IsTopologicalGroup G] [IsTopologicalGroup H] [IsTopologicalGroup I]
    (e : G ≃ₜ* H) (d : H ≃ₜ* I) :
    congr (e.trans d) = (congr e).trans (congr d) := by
  apply MulEquiv.ext
  intro x
  induction x using Quotient.inductionOn with
  | _ g => rfl

end TopologicalAbelianization

namespace LocalGaloisGroup

universe u

/-- Restriction of automorphisms is continuous for the two Krull topologies when the base-field
extension is finite. -/
private theorem continuous_restrictScalarsHom
    {k l A : Type*} [Field k] [Field l] [Field A]
    [Algebra k l] [Algebra l A] [Algebra k A] [IsScalarTower k l A]
    [FiniteDimensional k l] :
    Continuous (AlgEquiv.restrictScalarsHom k : (A ≃ₐ[l] A) → (A ≃ₐ[k] A)) := by
  apply continuous_of_tendsto_nhds_one (AlgEquiv.restrictScalarsHom k)
  rw [Filter.tendsto_def]
  intro s hs
  rw [krullTopology_mem_nhds_one_iff k A] at hs
  obtain ⟨E, hE, hEs⟩ := hs
  letI : FiniteDimensional k E := hE
  let F : IntermediateField k A :=
    (⊤ : IntermediateField k l).map (IsScalarTower.toAlgHom k l A)
  have hF : FiniteDimensional k F := by
    exact Module.Finite.equiv
      (IntermediateField.equivMap (⊤ : IntermediateField k l)
        (IsScalarTower.toAlgHom k l A)).toLinearEquiv
  letI : FiniteDimensional k F := hF
  let M : IntermediateField k A := E ⊔ F
  have hM : FiniteDimensional k M := E.finiteDimensional_sup F
  let N : IntermediateField l A := M.toSubfield.toIntermediateField (fun x => by
    apply (show F ≤ M from le_sup_right)
    exact ⟨x, Set.mem_univ x, rfl⟩)
  have hN : FiniteDimensional l N := by
    letI : Algebra k N := ((algebraMap l N).comp (algebraMap k l)).toAlgebra
    letI : IsScalarTower k l N := IsScalarTower.of_algebraMap_eq' rfl
    let eMN : M ≃ₗ[k] N :=
      { toFun := fun x => ⟨x, x.property⟩
        invFun := fun x => ⟨x, x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := by
          intro c x
          apply Subtype.ext
          simp only [IntermediateField.coe_smul, RingHom.id_apply] }
    letI : FiniteDimensional k N := Module.Finite.equiv eMN
    exact FiniteDimensional.right k l N
  rw [krullTopology_mem_nhds_one_iff l A]
  refine ⟨N, hN, ?_⟩
  intro σ hσ
  apply hEs
  change σ ∈ N.fixingSubgroup at hσ
  change σ.restrictScalars k ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  intro x hx
  apply hσ x
  exact (show E ≤ M from le_sup_left) hx

/-- The canonical identification between an open subgroup and the absolute Galois group of its
fixed field is a continuous group equivalence. -/
noncomputable def fixedFieldGaloisContinuousEquiv (G : LocalGaloisGroup.{u})
    (U : G.OpenSubgroupIndex) :
    (OrderDual.ofDual U).toSubgroup ≃ₜ*
      (G.presentation.algebraicClosure ≃ₐ[G.fixedField U]
        G.presentation.algebraicClosure) := by
  letI : FiniteDimensional G.presentation (G.fixedField U) :=
    G.fixedField_finiteDimensional U
  let e := G.fixedFieldGaloisEquiv U
  have hinv : Continuous e.symm := by
    change Continuous (fun σ :
      (G.presentation.algebraicClosure ≃ₐ[G.fixedField U]
        G.presentation.algebraicClosure) ↦
      (G.fixedFieldGaloisEquiv U).symm σ)
    exact (continuous_restrictScalarsHom (k := G.presentation)
      (l := G.fixedField U) (A := G.presentation.algebraicClosure)).subtype_mk
        (fun σ ↦ ((G.fixedFieldGaloisEquiv U).symm σ).property)
  have hfwd : Continuous e := hinv.continuous_symm_of_equiv_compact_to_t2
  exact
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_mul' := e.map_mul
      continuous_toFun := hfwd
      continuous_invFun := hinv }

/-- A morphism of local Galois groups induces an equivalence of their topological
abelianizations. -/
noncomputable def abelianizationEquiv {G H : LocalGaloisGroup.{u}} (f : G ⟶ H) :
    LCFT.AbelianizedAbsoluteGaloisGroup G.presentation ≃*
      LCFT.AbelianizedAbsoluteGaloisGroup H.presentation :=
  TopologicalAbelianization.congr f.equiv

/-- At every open subgroup, a morphism restricts to a morphism between the local Galois groups of
the corresponding fixed fields. -/
noncomputable def fixedFieldGroupHom
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H) (U : G.OpenSubgroupIndex) :
    LocalGaloisGroup.mk (G.fixedFieldPointed U) ⟶
      LocalGaloisGroup.mk
        (H.fixedFieldPointed (G.openSubgroupIndexEquiv f U)) where
  equiv := (G.fixedFieldGaloisContinuousEquiv U).symm.trans
    ((G.openSubgroupEquiv f U).trans
      (H.fixedFieldGaloisContinuousEquiv (G.openSubgroupIndexEquiv f U)))

/-- At every open subgroup, a morphism induces an equivalence between the abelianized absolute
Galois groups of the corresponding fixed fields. -/
noncomputable def fixedFieldAbelianizationEquiv
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H) (U : G.OpenSubgroupIndex) :
    LCFT.AbelianizedAbsoluteGaloisGroup (G.fixedFieldPointed U) ≃*
      LCFT.AbelianizedAbsoluteGaloisGroup
        (H.fixedFieldPointed (G.openSubgroupIndexEquiv f U)) :=
  abelianizationEquiv (G.fixedFieldGroupHom f U)

@[simp]
theorem abelianizationEquiv_id (G : LocalGaloisGroup.{u}) :
    abelianizationEquiv (𝟙 G) = MulEquiv.refl _ :=
  TopologicalAbelianization.congr_refl _

/-- Abelianized transport respects composition of local Galois-group morphisms. -/
theorem abelianizationEquiv_comp {G H I : LocalGaloisGroup.{u}}
    (f : G ⟶ H) (g : H ⟶ I) :
    abelianizationEquiv (f ≫ g) =
      (abelianizationEquiv f).trans (abelianizationEquiv g) :=
  TopologicalAbelianization.congr_trans f.equiv g.equiv

end LocalGaloisGroup
end OTriangle
end Anabelian
