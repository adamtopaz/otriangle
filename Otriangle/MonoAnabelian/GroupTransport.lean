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

/-- An equivalence between two open subgroups induces an equivalence between the absolute Galois
groups of their fixed fields.  Keeping the subgroup equivalence explicit is useful for coherence
calculations in which the two indices are only propositionally equal. -/
noncomputable def fixedFieldGroupHomOfSubgroupEquiv
    (G H : LocalGaloisGroup.{u}) (U : G.OpenSubgroupIndex)
    (V : H.OpenSubgroupIndex)
    (e : (OrderDual.ofDual U).toSubgroup ≃ₜ*
      (OrderDual.ofDual V).toSubgroup) :
    LocalGaloisGroup.mk (G.fixedFieldPointed U) ⟶
      LocalGaloisGroup.mk (H.fixedFieldPointed V) where
  equiv := (G.fixedFieldGaloisContinuousEquiv U).symm.trans
    (e.trans (H.fixedFieldGaloisContinuousEquiv V))

/-- At every open subgroup, a morphism restricts to a morphism between the local Galois groups of
the corresponding fixed fields. -/
noncomputable def fixedFieldGroupHom
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H) (U : G.OpenSubgroupIndex) :
    LocalGaloisGroup.mk (G.fixedFieldPointed U) ⟶
      LocalGaloisGroup.mk
        (H.fixedFieldPointed (G.openSubgroupIndexEquiv f U)) :=
  fixedFieldGroupHomOfSubgroupEquiv G H U (G.openSubgroupIndexEquiv f U)
    (G.openSubgroupEquiv f U)

/-- If two indices in the same ambient group are equal and an explicit subgroup equivalence is
the identity on ambient elements, then the induced fixed-field Galois equivalence is
heterogeneously the identity on every element. -/
theorem fixedFieldGroupHomOfSubgroupEquiv_apply_heq_of_eq
    (G : LocalGaloisGroup.{u}) (U V : G.OpenSubgroupIndex) (hVU : V = U)
    (e : (OrderDual.ofDual U).toSubgroup ≃ₜ*
      (OrderDual.ofDual V).toSubgroup)
    (he : ∀ x : (OrderDual.ofDual U).toSubgroup, HEq (e x) x)
    (σ : LCFT.AbsoluteGaloisGroup (G.fixedFieldPointed U)) :
    HEq ((fixedFieldGroupHomOfSubgroupEquiv G G U V e).equiv σ) σ := by
  subst V
  have he' : e = ContinuousMulEquiv.refl (OrderDual.ofDual U).toSubgroup := by
    apply ContinuousMulEquiv.ext
    intro x
    exact eq_of_heq (he x)
  subst e
  apply heq_of_eq
  change G.fixedFieldGaloisContinuousEquiv U
      ((G.fixedFieldGaloisContinuousEquiv U).symm σ) = σ
  exact (G.fixedFieldGaloisContinuousEquiv U).apply_symm_apply σ

/-- The fixed-field restriction of the identity ambient morphism is heterogeneously the identity
on elements. -/
theorem fixedFieldGroupHom_id_apply_heq (G : LocalGaloisGroup.{u})
    (U : G.OpenSubgroupIndex)
    (σ : LCFT.AbsoluteGaloisGroup (G.fixedFieldPointed U)) :
    HEq ((G.fixedFieldGroupHom (𝟙 G) U).equiv σ) σ :=
  fixedFieldGroupHomOfSubgroupEquiv_apply_heq_of_eq G U
    (G.openSubgroupIndexEquiv (𝟙 G) U)
    (G.openSubgroupIndexEquiv_id_apply U)
    (G.openSubgroupEquiv (𝟙 G) U)
    (G.openSubgroupEquiv_id_apply_heq U) σ

/-- Composition for fixed-field Galois transport attached to three explicit open-subgroup
equivalences.  The direct and composite target indices may be propositionally equal. -/
theorem fixedFieldGroupHomOfSubgroupEquiv_comp_apply_heq_of_eq
    (G H I : LocalGaloisGroup.{u})
    (U : G.OpenSubgroupIndex) (V : H.OpenSubgroupIndex)
    (W Z : I.OpenSubgroupIndex) (hZW : Z = W)
    (e : (OrderDual.ofDual U).toSubgroup ≃ₜ*
      (OrderDual.ofDual V).toSubgroup)
    (d : (OrderDual.ofDual V).toSubgroup ≃ₜ*
      (OrderDual.ofDual W).toSubgroup)
    (c : (OrderDual.ofDual U).toSubgroup ≃ₜ*
      (OrderDual.ofDual Z).toSubgroup)
    (hc : ∀ x : (OrderDual.ofDual U).toSubgroup,
      HEq (c x) (d (e x)))
    (σ : LCFT.AbsoluteGaloisGroup (G.fixedFieldPointed U)) :
    HEq ((fixedFieldGroupHomOfSubgroupEquiv G I U Z c).equiv σ)
      ((fixedFieldGroupHomOfSubgroupEquiv H I V W d).equiv
        ((fixedFieldGroupHomOfSubgroupEquiv G H U V e).equiv σ)) := by
  subst Z
  apply heq_of_eq
  change I.fixedFieldGaloisContinuousEquiv W
      (c ((G.fixedFieldGaloisContinuousEquiv U).symm σ)) =
    I.fixedFieldGaloisContinuousEquiv W
      (d ((H.fixedFieldGaloisContinuousEquiv V).symm
        (H.fixedFieldGaloisContinuousEquiv V
          (e ((G.fixedFieldGaloisContinuousEquiv U).symm σ)))))
  rw [(H.fixedFieldGaloisContinuousEquiv V).symm_apply_apply]
  congr 1
  exact eq_of_heq (hc ((G.fixedFieldGaloisContinuousEquiv U).symm σ))

/-- Fixed-field Galois transport respects composition, with heterogeneous equality accounting for
the propositionally equal target open-subgroup indices. -/
theorem fixedFieldGroupHom_comp_apply_heq
    {G H I : LocalGaloisGroup.{u}} (f : G ⟶ H) (g : H ⟶ I)
    (U : G.OpenSubgroupIndex)
    (σ : LCFT.AbsoluteGaloisGroup (G.fixedFieldPointed U)) :
    HEq ((G.fixedFieldGroupHom (f ≫ g) U).equiv σ)
      ((H.fixedFieldGroupHom g (G.openSubgroupIndexEquiv f U)).equiv
        ((G.fixedFieldGroupHom f U).equiv σ)) :=
  fixedFieldGroupHomOfSubgroupEquiv_comp_apply_heq_of_eq G H I U
    (G.openSubgroupIndexEquiv f U)
    (H.openSubgroupIndexEquiv g (G.openSubgroupIndexEquiv f U))
    (G.openSubgroupIndexEquiv (f ≫ g) U)
    (G.openSubgroupIndexEquiv_comp_apply f g U)
    (G.openSubgroupEquiv f U)
    (H.openSubgroupEquiv g (G.openSubgroupIndexEquiv f U))
    (G.openSubgroupEquiv (f ≫ g) U)
    (G.openSubgroupEquiv_comp_apply_heq f g U) σ

/-- At every open subgroup, a morphism induces an equivalence between the abelianized absolute
Galois groups of the corresponding fixed fields. -/
noncomputable def fixedFieldAbelianizationEquiv
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H) (U : G.OpenSubgroupIndex) :
    LCFT.AbelianizedAbsoluteGaloisGroup (G.fixedFieldPointed U) ≃*
      LCFT.AbelianizedAbsoluteGaloisGroup
        (H.fixedFieldPointed (G.openSubgroupIndexEquiv f U)) :=
  abelianizationEquiv (G.fixedFieldGroupHom f U)

/-- The abelianized fixed-field transport attached to an explicitly supplied equivalence of
open subgroups. -/
noncomputable def fixedFieldAbelianizationEquivOfSubgroupEquiv
    (G H : LocalGaloisGroup.{u}) (U : G.OpenSubgroupIndex)
    (V : H.OpenSubgroupIndex)
    (e : (OrderDual.ofDual U).toSubgroup ≃ₜ*
      (OrderDual.ofDual V).toSubgroup) :
    LCFT.AbelianizedAbsoluteGaloisGroup (G.fixedFieldPointed U) ≃*
      LCFT.AbelianizedAbsoluteGaloisGroup (H.fixedFieldPointed V) :=
  abelianizationEquiv (fixedFieldGroupHomOfSubgroupEquiv G H U V e)

/-- If an explicit equivalence between equal open subgroups is pointwise the identity, its
induced map on fixed-field abelianizations is heterogeneously the identity. -/
theorem fixedFieldAbelianizationEquivOfSubgroupEquiv_apply_heq_of_eq
    (G : LocalGaloisGroup.{u}) (U V : G.OpenSubgroupIndex) (hVU : V = U)
    (e : (OrderDual.ofDual U).toSubgroup ≃ₜ*
      (OrderDual.ofDual V).toSubgroup)
    (he : ∀ x : (OrderDual.ofDual U).toSubgroup, HEq (e x) x)
    (x : LCFT.AbelianizedAbsoluteGaloisGroup (G.fixedFieldPointed U)) :
    HEq (fixedFieldAbelianizationEquivOfSubgroupEquiv G G U V e x) x := by
  subst V
  have he' : e = ContinuousMulEquiv.refl (OrderDual.ofDual U).toSubgroup := by
    apply ContinuousMulEquiv.ext
    intro y
    exact eq_of_heq (he y)
  subst e
  have hgroup :
      (fixedFieldGroupHomOfSubgroupEquiv G G U U
        (ContinuousMulEquiv.refl (OrderDual.ofDual U).toSubgroup)).equiv =
        ContinuousMulEquiv.refl
          (LCFT.AbsoluteGaloisGroup (G.fixedFieldPointed U)) := by
    apply ContinuousMulEquiv.ext
    intro σ
    exact (G.fixedFieldGaloisContinuousEquiv U).apply_symm_apply σ
  apply heq_of_eq
  change TopologicalAbelianization.congr
      (fixedFieldGroupHomOfSubgroupEquiv G G U U
        (ContinuousMulEquiv.refl (OrderDual.ofDual U).toSubgroup)).equiv x = x
  rw [hgroup]
  induction x using Quotient.inductionOn with
  | _ σ => rfl

/-- Composition for abelianized fixed-field transport attached to explicit open-subgroup
equivalences. -/
theorem fixedFieldAbelianizationEquivOfSubgroupEquiv_comp_apply_heq_of_eq
    (G H I : LocalGaloisGroup.{u})
    (U : G.OpenSubgroupIndex) (V : H.OpenSubgroupIndex)
    (W Z : I.OpenSubgroupIndex) (hZW : Z = W)
    (e : (OrderDual.ofDual U).toSubgroup ≃ₜ*
      (OrderDual.ofDual V).toSubgroup)
    (d : (OrderDual.ofDual V).toSubgroup ≃ₜ*
      (OrderDual.ofDual W).toSubgroup)
    (c : (OrderDual.ofDual U).toSubgroup ≃ₜ*
      (OrderDual.ofDual Z).toSubgroup)
    (hc : ∀ y : (OrderDual.ofDual U).toSubgroup,
      HEq (c y) (d (e y)))
    (x : LCFT.AbelianizedAbsoluteGaloisGroup (G.fixedFieldPointed U)) :
    HEq (fixedFieldAbelianizationEquivOfSubgroupEquiv G I U Z c x)
      (fixedFieldAbelianizationEquivOfSubgroupEquiv H I V W d
        (fixedFieldAbelianizationEquivOfSubgroupEquiv G H U V e x)) := by
  subst Z
  induction x using Quotient.inductionOn with
  | _ σ =>
      apply heq_of_eq
      change QuotientGroup.mk'
          (Subgroup.topologicalClosure
            (commutator (LCFT.AbsoluteGaloisGroup (I.fixedFieldPointed W))))
          ((fixedFieldGroupHomOfSubgroupEquiv G I U W c).equiv σ) =
        QuotientGroup.mk'
          (Subgroup.topologicalClosure
            (commutator (LCFT.AbsoluteGaloisGroup (I.fixedFieldPointed W))))
          ((fixedFieldGroupHomOfSubgroupEquiv H I V W d).equiv
            ((fixedFieldGroupHomOfSubgroupEquiv G H U V e).equiv σ))
      congr 1
      exact eq_of_heq
        (fixedFieldGroupHomOfSubgroupEquiv_comp_apply_heq_of_eq
          G H I U V W W rfl e d c hc σ)

/-- Abelianized fixed-field transport along the identity is heterogeneously the identity. -/
theorem fixedFieldAbelianizationEquiv_id_apply_heq
    (G : LocalGaloisGroup.{u}) (U : G.OpenSubgroupIndex)
    (x : LCFT.AbelianizedAbsoluteGaloisGroup (G.fixedFieldPointed U)) :
    HEq (G.fixedFieldAbelianizationEquiv (CategoryStruct.id G) U x) x :=
  fixedFieldAbelianizationEquivOfSubgroupEquiv_apply_heq_of_eq G U
    (G.openSubgroupIndexEquiv (CategoryStruct.id G) U)
    (G.openSubgroupIndexEquiv_id_apply U)
    (G.openSubgroupEquiv (CategoryStruct.id G) U)
    (G.openSubgroupEquiv_id_apply_heq U) x

/-- Abelianized fixed-field transport respects composition. -/
theorem fixedFieldAbelianizationEquiv_comp_apply_heq
    {G H I : LocalGaloisGroup.{u}} (f : G ⟶ H) (g : H ⟶ I)
    (U : G.OpenSubgroupIndex)
    (x : LCFT.AbelianizedAbsoluteGaloisGroup (G.fixedFieldPointed U)) :
    HEq (G.fixedFieldAbelianizationEquiv (f ≫ g) U x)
      (H.fixedFieldAbelianizationEquiv g
        (G.openSubgroupIndexEquiv f U)
        (G.fixedFieldAbelianizationEquiv f U x)) :=
  fixedFieldAbelianizationEquivOfSubgroupEquiv_comp_apply_heq_of_eq
    G H I U
    (G.openSubgroupIndexEquiv f U)
    (H.openSubgroupIndexEquiv g (G.openSubgroupIndexEquiv f U))
    (G.openSubgroupIndexEquiv (f ≫ g) U)
    (G.openSubgroupIndexEquiv_comp_apply f g U)
    (G.openSubgroupEquiv f U)
    (H.openSubgroupEquiv g (G.openSubgroupIndexEquiv f U))
    (G.openSubgroupEquiv (f ≫ g) U)
    (G.openSubgroupEquiv_comp_apply_heq f g U) x

@[simp]
theorem fixedFieldAbelianizationEquiv_mk
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H) (U : G.OpenSubgroupIndex)
    (σ : LCFT.AbsoluteGaloisGroup (G.fixedFieldPointed U)) :
    G.fixedFieldAbelianizationEquiv f U
        (QuotientGroup.mk'
          (Subgroup.topologicalClosure
            (commutator (LCFT.AbsoluteGaloisGroup (G.fixedFieldPointed U)))) σ) =
      QuotientGroup.mk'
        (Subgroup.topologicalClosure
          (commutator (LCFT.AbsoluteGaloisGroup
            (H.fixedFieldPointed (G.openSubgroupIndexEquiv f U)))))
        ((G.fixedFieldGroupHom f U).equiv σ) :=
  TopologicalAbelianization.congr_mk _ _

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
