import Otriangle.MonoAnabelian.SpectralResidue
import Otriangle.LCFT

/-!
# The canonical spectral pointing of a pointed local field

The spectral norm canonically values the chosen algebraic closure while leaving the original
valuation on the base field untouched.  This file constructs the resulting residue action and
packages it as a second pointing of the same field and algebraic closure.  Keeping the native base
valuation is essential when this pointing is compared to the original one by local reciprocity.
-/

noncomputable section

namespace Anabelian.OTriangle.PointedMixedCharLocalField

open ValuativeRel
open Polynomial

universe u

variable (K : PointedMixedCharLocalField.{u})

/-- A base-field automorphism of the algebraic closure restricts to the spectral valuation ring,
with scalar ring the original valuation ring of `K`. -/
noncomputable def spectralClosureIntegerAlgEquiv
    (σ : LCFT.AbsoluteGaloisGroup K) :
    letI := K.nontriviallyNormedField
    letI := K.isUltrametricDist
    letI := K.completeSpace
    letI := SpectralLocalField.nontriviallyNormedField K K.algebraicClosure
    letI := SpectralLocalField.isUltrametricDist K K.algebraicClosure
    letI := SpectralLocalField.valuativeRel K K.algebraicClosure
    letI := K.spectralValuativeExtension K.algebraicClosure
    𝒪[K.algebraicClosure] ≃ₐ[𝒪[K]] 𝒪[K.algebraicClosure] := by
  letI := K.nontriviallyNormedField
  letI := K.isUltrametricDist
  letI := K.completeSpace
  letI := SpectralLocalField.nontriviallyNormedField K K.algebraicClosure
  letI := SpectralLocalField.isUltrametricDist K K.algebraicClosure
  letI : ValuativeRel K.algebraicClosure :=
    SpectralLocalField.valuativeRel K K.algebraicClosure
  letI : ValuativeExtension K K.algebraicClosure :=
    K.spectralValuativeExtension K.algebraicClosure
  let e : 𝒪[K.algebraicClosure] ≃+* 𝒪[K.algebraicClosure] :=
    { toFun := fun x =>
        ⟨σ x, (SpectralLocalField.automorphism_mem_integer_iff
          K K K.algebraicClosure σ x).mp x.property⟩
      invFun := fun x =>
        ⟨σ.symm x, (SpectralLocalField.automorphism_mem_integer_iff
          K K K.algebraicClosure σ.symm x).mp x.property⟩
      left_inv := fun x => Subtype.ext (σ.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (σ.apply_symm_apply x)
      map_mul' := fun x y => Subtype.ext (map_mul σ (x : K.algebraicClosure) y)
      map_add' := fun x y => Subtype.ext (map_add σ (x : K.algebraicClosure) y) }
  exact
    { toRingEquiv := e
      commutes' := fun x => Subtype.ext (σ.commutes (x : K)) }

/-- The residue action on the spectral valuation of the chosen algebraic closure, over the
original residue field of `K`. -/
noncomputable def spectralResidueGaloisMap :
    letI := K.nontriviallyNormedField
    letI := K.isUltrametricDist
    letI := K.completeSpace
    letI := SpectralLocalField.nontriviallyNormedField K K.algebraicClosure
    letI := SpectralLocalField.isUltrametricDist K K.algebraicClosure
    letI := SpectralLocalField.valuativeRel K K.algebraicClosure
    letI := K.spectralValuativeExtension K.algebraicClosure
    LCFT.AbsoluteGaloisGroup K →*
      (IsLocalRing.ResidueField 𝒪[K.algebraicClosure] ≃ₐ[LCFT.ResidueField K]
        IsLocalRing.ResidueField 𝒪[K.algebraicClosure]) := by
  letI := K.nontriviallyNormedField
  letI := K.isUltrametricDist
  letI := K.completeSpace
  letI := SpectralLocalField.nontriviallyNormedField K K.algebraicClosure
  letI := SpectralLocalField.isUltrametricDist K K.algebraicClosure
  letI : ValuativeRel K.algebraicClosure :=
    SpectralLocalField.valuativeRel K K.algebraicClosure
  letI : ValuativeExtension K K.algebraicClosure :=
    K.spectralValuativeExtension K.algebraicClosure
  refine
    { toFun := fun σ => IsLocalRing.ResidueField.mapAlgEquiv'
        (K.spectralClosureIntegerAlgEquiv σ)
      map_one' := ?_
      map_mul' := ?_ }
  · apply AlgEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    simp [spectralClosureIntegerAlgEquiv]
  · intro σ τ
    apply AlgEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    simp [spectralClosureIntegerAlgEquiv]

@[implicit_reducible]
private noncomputable def spectralClosureIntegerAction :
    letI := K.nontriviallyNormedField
    letI := K.isUltrametricDist
    letI := K.completeSpace
    letI := SpectralLocalField.nontriviallyNormedField K K.algebraicClosure
    letI := SpectralLocalField.isUltrametricDist K K.algebraicClosure
    letI := SpectralLocalField.valuativeRel K K.algebraicClosure
    letI := K.spectralValuativeExtension K.algebraicClosure
    MulSemiringAction (LCFT.AbsoluteGaloisGroup K) 𝒪[K.algebraicClosure] := by
  letI := K.nontriviallyNormedField
  letI := K.isUltrametricDist
  letI := K.completeSpace
  letI := SpectralLocalField.nontriviallyNormedField K K.algebraicClosure
  letI := SpectralLocalField.isUltrametricDist K K.algebraicClosure
  letI : ValuativeRel K.algebraicClosure :=
    SpectralLocalField.valuativeRel K K.algebraicClosure
  letI : ValuativeExtension K K.algebraicClosure :=
    K.spectralValuativeExtension K.algebraicClosure
  let h : LCFT.AbsoluteGaloisGroup K →* RingAut 𝒪[K.algebraicClosure] :=
    { toFun := fun σ => (K.spectralClosureIntegerAlgEquiv σ).toRingEquiv
      map_one' := by ext x; rfl
      map_mul' := fun σ τ => by ext x; rfl }
  exact MulSemiringAction.compHom 𝒪[K.algebraicClosure] h

private theorem spectralClosureIntegerSMulCommClass :
    letI := K.nontriviallyNormedField
    letI := K.isUltrametricDist
    letI := K.completeSpace
    letI := SpectralLocalField.nontriviallyNormedField K K.algebraicClosure
    letI := SpectralLocalField.isUltrametricDist K K.algebraicClosure
    letI := SpectralLocalField.valuativeRel K K.algebraicClosure
    letI := K.spectralValuativeExtension K.algebraicClosure
    letI := K.spectralClosureIntegerAction
    SMulCommClass (LCFT.AbsoluteGaloisGroup K) 𝒪[K] 𝒪[K.algebraicClosure] := by
  letI := K.nontriviallyNormedField
  letI := K.isUltrametricDist
  letI := K.completeSpace
  letI := SpectralLocalField.nontriviallyNormedField K K.algebraicClosure
  letI := SpectralLocalField.isUltrametricDist K K.algebraicClosure
  letI : ValuativeRel K.algebraicClosure :=
    SpectralLocalField.valuativeRel K K.algebraicClosure
  letI : ValuativeExtension K K.algebraicClosure :=
    K.spectralValuativeExtension K.algebraicClosure
  letI : MulSemiringAction (LCFT.AbsoluteGaloisGroup K) 𝒪[K.algebraicClosure] :=
    K.spectralClosureIntegerAction
  constructor
  intro σ e x
  change K.spectralClosureIntegerAlgEquiv σ (e • x) =
    e • K.spectralClosureIntegerAlgEquiv σ x
  exact map_smul (K.spectralClosureIntegerAlgEquiv σ) e x

private theorem spectralClosureIntegerIsInvariant :
    letI := K.nontriviallyNormedField
    letI := K.isUltrametricDist
    letI := K.completeSpace
    letI := SpectralLocalField.nontriviallyNormedField K K.algebraicClosure
    letI := SpectralLocalField.isUltrametricDist K K.algebraicClosure
    letI := SpectralLocalField.valuativeRel K K.algebraicClosure
    letI := K.spectralValuativeExtension K.algebraicClosure
    letI := K.spectralClosureIntegerAction
    Algebra.IsInvariant 𝒪[K] 𝒪[K.algebraicClosure]
      (LCFT.AbsoluteGaloisGroup K) := by
  letI := K.nontriviallyNormedField
  letI := K.isUltrametricDist
  letI := K.completeSpace
  letI := SpectralLocalField.nontriviallyNormedField K K.algebraicClosure
  letI := SpectralLocalField.isUltrametricDist K K.algebraicClosure
  letI : ValuativeRel K.algebraicClosure :=
    SpectralLocalField.valuativeRel K K.algebraicClosure
  letI : ValuativeExtension K K.algebraicClosure :=
    K.spectralValuativeExtension K.algebraicClosure
  letI : MulSemiringAction (LCFT.AbsoluteGaloisGroup K) 𝒪[K.algebraicClosure] :=
    K.spectralClosureIntegerAction
  constructor
  intro b hb
  have hfixed : ∀ σ : LCFT.AbsoluteGaloisGroup K,
      σ (b : K.algebraicClosure) = b := fun σ => congrArg Subtype.val (hb σ)
  obtain ⟨e, he⟩ :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (b : K.algebraicClosure)).2 hfixed
  refine ⟨⟨e, ?_⟩, ?_⟩
  · rw [Valuation.mem_integer_iff]
    rw [← (valuation K).vle_one_iff]
    rw [← ValuativeExtension.vle_iff_vle (A := K) (B := K.algebraicClosure)]
    rw [map_one, (valuation K.algebraicClosure).vle_one_iff, he]
    exact b.property
  · apply Subtype.ext
    exact he

private theorem spectralClosureIntegerContinuousSMul :
    letI := K.nontriviallyNormedField
    letI := K.isUltrametricDist
    letI := K.completeSpace
    letI := SpectralLocalField.nontriviallyNormedField K K.algebraicClosure
    letI := SpectralLocalField.isUltrametricDist K K.algebraicClosure
    letI := SpectralLocalField.valuativeRel K K.algebraicClosure
    letI := K.spectralValuativeExtension K.algebraicClosure
    letI := K.spectralClosureIntegerAction
    letI : TopologicalSpace 𝒪[K.algebraicClosure] := ⊥
    ContinuousSMul (LCFT.AbsoluteGaloisGroup K) 𝒪[K.algebraicClosure] := by
  letI := K.nontriviallyNormedField
  letI := K.isUltrametricDist
  letI := K.completeSpace
  letI := SpectralLocalField.nontriviallyNormedField K K.algebraicClosure
  letI := SpectralLocalField.isUltrametricDist K K.algebraicClosure
  letI : ValuativeRel K.algebraicClosure :=
    SpectralLocalField.valuativeRel K K.algebraicClosure
  letI : ValuativeExtension K K.algebraicClosure :=
    K.spectralValuativeExtension K.algebraicClosure
  letI : MulSemiringAction (LCFT.AbsoluteGaloisGroup K) 𝒪[K.algebraicClosure] :=
    K.spectralClosureIntegerAction
  letI : TopologicalSpace 𝒪[K.algebraicClosure] := ⊥
  letI : DiscreteTopology 𝒪[K.algebraicClosure] := discreteTopology_bot _
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro x
  have hstab :
      (MulAction.stabilizer (LCFT.AbsoluteGaloisGroup K) x :
          Set (LCFT.AbsoluteGaloisGroup K)) =
        (MulAction.stabilizer (LCFT.AbsoluteGaloisGroup K)
          (x : K.algebraicClosure) : Set (LCFT.AbsoluteGaloisGroup K)) := by
    ext σ
    change K.spectralClosureIntegerAlgEquiv σ x = x ↔
      σ (x : K.algebraicClosure) = x
    constructor
    · exact fun h => congrArg Subtype.val h
    · exact fun h => Subtype.ext h
  rw [hstab]
  exact stabilizer_isOpen_of_isIntegral (x : K.algebraicClosure)

/-- The spectral valuation ring of the algebraic closure is integral over the original valuation
ring of `K`. -/
theorem spectralClosureIntegerIsIntegral :
    letI := K.nontriviallyNormedField
    letI := K.isUltrametricDist
    letI := K.completeSpace
    letI := SpectralLocalField.nontriviallyNormedField K K.algebraicClosure
    letI := SpectralLocalField.isUltrametricDist K K.algebraicClosure
    letI := SpectralLocalField.valuativeRel K K.algebraicClosure
    letI := K.spectralValuativeExtension K.algebraicClosure
    Algebra.IsIntegral 𝒪[K] 𝒪[K.algebraicClosure] := by
  letI := K.nontriviallyNormedField
  letI := K.isUltrametricDist
  letI := K.completeSpace
  letI := SpectralLocalField.nontriviallyNormedField K K.algebraicClosure
  letI := SpectralLocalField.isUltrametricDist K K.algebraicClosure
  letI : ValuativeRel K.algebraicClosure :=
    SpectralLocalField.valuativeRel K K.algebraicClosure
  letI : ValuativeExtension K K.algebraicClosure :=
    K.spectralValuativeExtension K.algebraicClosure
  letI : MulSemiringAction (LCFT.AbsoluteGaloisGroup K) 𝒪[K.algebraicClosure] :=
    K.spectralClosureIntegerAction
  letI : SMulCommClass (LCFT.AbsoluteGaloisGroup K) 𝒪[K]
      𝒪[K.algebraicClosure] := K.spectralClosureIntegerSMulCommClass
  letI : TopologicalSpace 𝒪[K.algebraicClosure] := ⊥
  letI : DiscreteTopology 𝒪[K.algebraicClosure] := discreteTopology_bot _
  letI : ContinuousSMul (LCFT.AbsoluteGaloisGroup K) 𝒪[K.algebraicClosure] :=
    K.spectralClosureIntegerContinuousSMul
  letI : Algebra.IsInvariant 𝒪[K] 𝒪[K.algebraicClosure]
      (LCFT.AbsoluteGaloisGroup K) := K.spectralClosureIntegerIsInvariant
  exact Algebra.IsInvariant.isIntegral_of_profinite
    (A := 𝒪[K]) (B := 𝒪[K.algebraicClosure])
      (G := LCFT.AbsoluteGaloisGroup K)

/-- The native-base spectral residue action is surjective. -/
theorem spectralResidueGaloisMap_surjective :
    letI := K.nontriviallyNormedField
    letI := K.isUltrametricDist
    letI := K.completeSpace
    letI := SpectralLocalField.nontriviallyNormedField K K.algebraicClosure
    letI := SpectralLocalField.isUltrametricDist K K.algebraicClosure
    letI := SpectralLocalField.valuativeRel K K.algebraicClosure
    letI := K.spectralValuativeExtension K.algebraicClosure
    Function.Surjective K.spectralResidueGaloisMap := by
  letI := K.nontriviallyNormedField
  letI := K.isUltrametricDist
  letI := K.completeSpace
  letI := SpectralLocalField.nontriviallyNormedField K K.algebraicClosure
  letI := SpectralLocalField.isUltrametricDist K K.algebraicClosure
  letI : ValuativeRel K.algebraicClosure :=
    SpectralLocalField.valuativeRel K K.algebraicClosure
  letI : ValuativeExtension K K.algebraicClosure :=
    K.spectralValuativeExtension K.algebraicClosure
  letI : MulSemiringAction (LCFT.AbsoluteGaloisGroup K) 𝒪[K.algebraicClosure] :=
    K.spectralClosureIntegerAction
  letI : SMulCommClass (LCFT.AbsoluteGaloisGroup K) 𝒪[K]
      𝒪[K.algebraicClosure] := K.spectralClosureIntegerSMulCommClass
  letI : TopologicalSpace 𝒪[K.algebraicClosure] := ⊥
  letI : DiscreteTopology 𝒪[K.algebraicClosure] := discreteTopology_bot _
  letI : ContinuousSMul (LCFT.AbsoluteGaloisGroup K) 𝒪[K.algebraicClosure] :=
    K.spectralClosureIntegerContinuousSMul
  letI : Algebra.IsInvariant 𝒪[K] 𝒪[K.algebraicClosure]
      (LCFT.AbsoluteGaloisGroup K) := K.spectralClosureIntegerIsInvariant
  intro τ
  obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := LCFT.AbsoluteGaloisGroup K) (IsLocalRing.maximalIdeal 𝒪[K])
      (IsLocalRing.maximalIdeal 𝒪[K.algebraicClosure]) τ
  refine ⟨g.1, ?_⟩
  apply AlgEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  have hgy := DFunLike.congr_fun hg
    (IsLocalRing.residue 𝒪[K.algebraicClosure] x)
  change (IsLocalRing.ResidueField.mapAlgEquiv'
    (K.spectralClosureIntegerAlgEquiv g.1))
      (IsLocalRing.residue 𝒪[K.algebraicClosure] x) = _
  rw [IsLocalRing.ResidueField.mapAlgEquiv'_residue]
  have haction := Ideal.Quotient.stabilizerHom_apply
    (IsLocalRing.maximalIdeal 𝒪[K.algebraicClosure])
      (IsLocalRing.maximalIdeal 𝒪[K]) (LCFT.AbsoluteGaloisGroup K) g x
  exact haction.symm.trans hgy

/-- The native-base spectral residue action is continuous for the Krull topologies. -/
theorem spectralResidueGaloisMap_continuous :
    letI := K.nontriviallyNormedField
    letI := K.isUltrametricDist
    letI := K.completeSpace
    letI := SpectralLocalField.nontriviallyNormedField K K.algebraicClosure
    letI := SpectralLocalField.isUltrametricDist K K.algebraicClosure
    letI := SpectralLocalField.valuativeRel K K.algebraicClosure
    letI := K.spectralValuativeExtension K.algebraicClosure
    Continuous K.spectralResidueGaloisMap := by
  letI := K.nontriviallyNormedField
  letI := K.isUltrametricDist
  letI := K.completeSpace
  letI := SpectralLocalField.nontriviallyNormedField K K.algebraicClosure
  letI := SpectralLocalField.isUltrametricDist K K.algebraicClosure
  letI : ValuativeRel K.algebraicClosure :=
    SpectralLocalField.valuativeRel K K.algebraicClosure
  letI : ValuativeExtension K K.algebraicClosure :=
    K.spectralValuativeExtension K.algebraicClosure
  letI : Algebra.IsIntegral 𝒪[K] 𝒪[K.algebraicClosure] :=
    K.spectralClosureIntegerIsIntegral
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro N hN
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨L, hLfin, hLN⟩ := hN
  letI : FiniteDimensional (LCFT.ResidueField K) L := hLfin
  have hLfg : L.FG := IntermediateField.essFiniteType_iff.mp inferInstance
  obtain ⟨t, ht⟩ := hLfg
  let lift (y : IsLocalRing.ResidueField 𝒪[K.algebraicClosure]) :
      𝒪[K.algebraicClosure] := (IsLocalRing.residue_surjective y).choose
  have lift_spec (y : IsLocalRing.ResidueField 𝒪[K.algebraicClosure]) :
      IsLocalRing.residue 𝒪[K.algebraicClosure] (lift y) = y :=
    (IsLocalRing.residue_surjective y).choose_spec
  let S : Set K.algebraicClosure :=
    (fun y : IsLocalRing.ResidueField 𝒪[K.algebraicClosure] => (lift y : K.algebraicClosure)) ''
      (t : Set (IsLocalRing.ResidueField 𝒪[K.algebraicClosure]))
  let F : IntermediateField K K.algebraicClosure := IntermediateField.adjoin K S
  have hSfinite : S.Finite := t.finite_toSet.image _
  have hFfg : F.FG := IntermediateField.fg_adjoin_of_finite hSfinite
  letI : Algebra.EssFiniteType K F := IntermediateField.essFiniteType_iff.mpr hFfg
  letI : Module.Finite K F := Algebra.finite_of_essFiniteType_of_isAlgebraic
  letI : FiniteDimensional K F := by infer_instance
  apply mem_nhds_iff.mpr
  use (F.fixingSubgroup : Set (LCFT.AbsoluteGaloisGroup K))
  constructor
  · intro σ hσ
    apply hLN
    change K.spectralResidueGaloisMap σ ∈ L.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro z hz
    rw [← ht] at hz
    apply (IntermediateField.forall_mem_adjoin_smul_eq_self_iff
      (LCFT.ResidueField K) (K.spectralResidueGaloisMap σ)).mpr
      (fun y hy => ?_) z hz
    have hyS : (lift y : K.algebraicClosure) ∈ S := ⟨y, hy, rfl⟩
    have hylift : σ (lift y : K.algebraicClosure) = lift y := by
      change σ ∈ F.fixingSubgroup at hσ
      rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
      exact hσ (lift y : K.algebraicClosure)
        (IntermediateField.subset_adjoin (F := K) (S := S) hyS)
    change (IsLocalRing.ResidueField.mapAlgEquiv'
      (K.spectralClosureIntegerAlgEquiv σ)) y = y
    rw [← lift_spec y, IsLocalRing.ResidueField.mapAlgEquiv'_residue]
    rw [show K.spectralClosureIntegerAlgEquiv σ (lift y) = lift y from
      Subtype.ext hylift]
  · exact ⟨F.fixingSubgroup_isOpen, congrFun rfl⟩

/-- The same base field and algebraic closure, with the canonical spectral valuation and residue
action on the closure. -/
@[implicit_reducible]
noncomputable def spectralPointing : PointedMixedCharLocalField.{u} := by
  letI := K.nontriviallyNormedField
  letI := K.isUltrametricDist
  letI := K.completeSpace
  letI := SpectralLocalField.nontriviallyNormedField K K.algebraicClosure
  letI := SpectralLocalField.isUltrametricDist K K.algebraicClosure
  letI : ValuativeRel K.algebraicClosure :=
    SpectralLocalField.valuativeRel K K.algebraicClosure
  letI : ValuativeExtension K K.algebraicClosure :=
    K.spectralValuativeExtension K.algebraicClosure
  letI : Algebra.IsIntegral 𝒪[K] 𝒪[K.algebraicClosure] :=
    K.spectralClosureIntegerIsIntegral
  letI : Algebra.IsIntegral (LCFT.ResidueField K)
      (IsLocalRing.ResidueField 𝒪[K.algebraicClosure]) :=
    SpectralLocalField.residueField_isIntegral
      (R := 𝒪[K]) (S := 𝒪[K.algebraicClosure])
  letI : Algebra.IsAlgebraic (LCFT.ResidueField K)
      (IsLocalRing.ResidueField 𝒪[K.algebraicClosure]) :=
    ⟨fun x => IsIntegral.isAlgebraic (Algebra.IsIntegral.isIntegral x)⟩
  refine
    { carrier := K
      residueChar := K.residueChar
      algebraicClosure := K.algebraicClosure
      residueGaloisMap := K.spectralResidueGaloisMap
      residueGaloisMap_surjective := K.spectralResidueGaloisMap_surjective
      residueGaloisMap_continuous := K.spectralResidueGaloisMap_continuous
      residueGaloisMap_commutes := fun σ τ =>
        SpectralLocalField.finiteBaseGalois_commutes _ _ σ τ }

end Anabelian.OTriangle.PointedMixedCharLocalField
