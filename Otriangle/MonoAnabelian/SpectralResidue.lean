import Otriangle.MonoAnabelian.SpectralLocalField
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.LocalRing.ResidueField.Instances

/-!
# Residue actions for spectral valuations

An automorphism of an algebraic tower preserves its spectral valuation.  Consequently it restricts
to the valuation ring and descends to the residue field.  Profinite invariant theory then proves
that this residue action is surjective, while finite sets of integral lifts prove continuity for
the two Krull topologies.
-/

noncomputable section

namespace Anabelian
namespace OTriangle
namespace SpectralLocalField

open ValuativeRel
open Polynomial

variable (K E A : Type*)
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Field E] [Algebra K E]
  [Field A] [Algebra K A] [Algebra.IsAlgebraic K A]
  [Algebra E A] [IsScalarTower K E A]

/-- An automorphism over an intermediate field preserves the spectral valuation ring. -/
theorem automorphism_mem_integer_iff
    (σ : A ≃ₐ[E] A) (x : A) :
    letI := nontriviallyNormedField K A
    letI := isUltrametricDist K A
    letI := valuativeRel K A
    x ∈ 𝒪[A] ↔ σ x ∈ 𝒪[A] := by
  letI := nontriviallyNormedField K A
  letI := isUltrametricDist K A
  letI : ValuativeRel A := valuativeRel K A
  letI : (NormedField.valuation (K := A)).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff]
  rw [← (valuation A).vle_one_iff, ← (valuation A).vle_one_iff]
  rw [(NormedField.valuation (K := A)).vle_one_iff,
    (NormedField.valuation (K := A)).vle_one_iff]
  change spectralNorm K A x ≤ 1 ↔ spectralNorm K A (σ x) ≤ 1
  have hσ : spectralNorm K A x = spectralNorm K A (σ x) := by
    simpa using spectralNorm_eq_of_equiv (σ.restrictScalars K) x
  rw [hσ]

/-- An automorphism of an algebraic tower restricts to the spectral valuation ring. -/
noncomputable def automorphismIntegerAlgEquiv
    [Algebra.IsAlgebraic K E] (σ : A ≃ₐ[E] A) :
    letI := nontriviallyNormedField K E
    letI := isUltrametricDist K E
    letI := valuativeRel K E
    letI := nontriviallyNormedField K A
    letI := isUltrametricDist K A
    letI := valuativeRel K A
    letI := valuativeExtension K (E := E) (A := A)
    𝒪[A] ≃ₐ[𝒪[E]] 𝒪[A] := by
  letI := nontriviallyNormedField K E
  letI := isUltrametricDist K E
  letI : ValuativeRel E := valuativeRel K E
  letI := nontriviallyNormedField K A
  letI := isUltrametricDist K A
  letI : ValuativeRel A := valuativeRel K A
  letI : ValuativeExtension E A := valuativeExtension K (E := E) (A := A)
  let e : 𝒪[A] ≃+* 𝒪[A] :=
    { toFun := fun x =>
        ⟨σ x, (automorphism_mem_integer_iff K E A σ x).mp x.property⟩
      invFun := fun x =>
        ⟨σ.symm x, (automorphism_mem_integer_iff K E A σ.symm x).mp x.property⟩
      left_inv := fun x => Subtype.ext (σ.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (σ.apply_symm_apply x)
      map_mul' := fun x y => Subtype.ext (map_mul σ (x : A) (y : A))
      map_add' := fun x y => Subtype.ext (map_add σ (x : A) (y : A)) }
  exact
    { toRingEquiv := e
      commutes' := fun x => Subtype.ext (σ.commutes (x : E)) }

/-- The residue action induced by the spectral valuation on an algebraic tower. -/
noncomputable def residueGaloisMap [Algebra.IsAlgebraic K E] :
    letI := nontriviallyNormedField K E
    letI := isUltrametricDist K E
    letI := valuativeRel K E
    letI := nontriviallyNormedField K A
    letI := isUltrametricDist K A
    letI := valuativeRel K A
    letI := valuativeExtension K (E := E) (A := A)
    (A ≃ₐ[E] A) →* (𝓀[A] ≃ₐ[𝓀[E]] 𝓀[A]) := by
  letI := nontriviallyNormedField K E
  letI := isUltrametricDist K E
  letI : ValuativeRel E := valuativeRel K E
  letI := nontriviallyNormedField K A
  letI := isUltrametricDist K A
  letI : ValuativeRel A := valuativeRel K A
  letI : ValuativeExtension E A := valuativeExtension K (E := E) (A := A)
  refine
    { toFun := fun σ => IsLocalRing.ResidueField.mapAlgEquiv'
        (automorphismIntegerAlgEquiv K E A σ)
      map_one' := ?_
      map_mul' := ?_ }
  · apply AlgEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    simp [automorphismIntegerAlgEquiv]
  · intro σ τ
    apply AlgEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    simp [automorphismIntegerAlgEquiv]

variable [Algebra.IsAlgebraic K E]

/-- The spectral valuation ring carries the action induced by field automorphisms. -/
@[implicit_reducible]
noncomputable def integerMulSemiringAction :
    letI := nontriviallyNormedField K E
    letI := isUltrametricDist K E
    letI := valuativeRel K E
    letI := nontriviallyNormedField K A
    letI := isUltrametricDist K A
    letI := valuativeRel K A
    letI := valuativeExtension K (E := E) (A := A)
    MulSemiringAction (A ≃ₐ[E] A) 𝒪[A] := by
  letI := nontriviallyNormedField K E
  letI := isUltrametricDist K E
  letI : ValuativeRel E := valuativeRel K E
  letI := nontriviallyNormedField K A
  letI := isUltrametricDist K A
  letI : ValuativeRel A := valuativeRel K A
  letI : ValuativeExtension E A := valuativeExtension K (E := E) (A := A)
  let h : (A ≃ₐ[E] A) →* RingAut 𝒪[A] :=
    { toFun := fun σ => (automorphismIntegerAlgEquiv K E A σ).toRingEquiv
      map_one' := by
        ext x
        rfl
      map_mul' := fun σ τ => by
        ext x
        rfl }
  exact MulSemiringAction.compHom 𝒪[A] h

/-- The action on the spectral valuation ring fixes the base valuation ring. -/
theorem integerSMulCommClass :
    letI := nontriviallyNormedField K E
    letI := isUltrametricDist K E
    letI := valuativeRel K E
    letI := nontriviallyNormedField K A
    letI := isUltrametricDist K A
    letI := valuativeRel K A
    letI := valuativeExtension K (E := E) (A := A)
    letI := integerMulSemiringAction K E A
    SMulCommClass (A ≃ₐ[E] A) 𝒪[E] 𝒪[A] := by
  letI := nontriviallyNormedField K E
  letI := isUltrametricDist K E
  letI : ValuativeRel E := valuativeRel K E
  letI := nontriviallyNormedField K A
  letI := isUltrametricDist K A
  letI : ValuativeRel A := valuativeRel K A
  letI : ValuativeExtension E A := valuativeExtension K (E := E) (A := A)
  letI : MulSemiringAction (A ≃ₐ[E] A) 𝒪[A] :=
    integerMulSemiringAction K E A
  constructor
  intro σ e x
  change (automorphismIntegerAlgEquiv K E A σ) (e • x) =
    e • (automorphismIntegerAlgEquiv K E A σ) x
  exact map_smul (automorphismIntegerAlgEquiv K E A σ) e x

/-- The spectral valuation ring is invariant under the full Galois action: an integral element
fixed by every automorphism comes from the base valuation ring. -/
theorem integer_isInvariant [IsGalois E A] :
    letI := nontriviallyNormedField K E
    letI := isUltrametricDist K E
    letI := valuativeRel K E
    letI := nontriviallyNormedField K A
    letI := isUltrametricDist K A
    letI := valuativeRel K A
    letI := valuativeExtension K (E := E) (A := A)
    letI := integerMulSemiringAction K E A
    Algebra.IsInvariant 𝒪[E] 𝒪[A] (A ≃ₐ[E] A) := by
  letI := nontriviallyNormedField K E
  letI := isUltrametricDist K E
  letI : ValuativeRel E := valuativeRel K E
  letI := nontriviallyNormedField K A
  letI := isUltrametricDist K A
  letI : ValuativeRel A := valuativeRel K A
  letI : ValuativeExtension E A := valuativeExtension K (E := E) (A := A)
  letI : MulSemiringAction (A ≃ₐ[E] A) 𝒪[A] :=
    integerMulSemiringAction K E A
  constructor
  intro b hb
  have hfixed : ∀ σ : A ≃ₐ[E] A, σ (b : A) = b := fun σ =>
    congrArg Subtype.val (hb σ)
  obtain ⟨e, he⟩ :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (b : A)).2 hfixed
  refine ⟨⟨e, ?_⟩, ?_⟩
  · rw [Valuation.mem_integer_iff]
    rw [← (valuation E).vle_one_iff]
    rw [← ValuativeExtension.vle_iff_vle (A := E) (B := A)]
    rw [map_one]
    rw [(valuation A).vle_one_iff]
    rw [he]
    exact b.property
  · apply Subtype.ext
    exact he

/-- With the valuation ring discrete, its spectral Galois action is continuous for the Krull
topology. -/
theorem integer_continuousSMul [IsGalois E A] :
    letI := nontriviallyNormedField K E
    letI := isUltrametricDist K E
    letI := valuativeRel K E
    letI := nontriviallyNormedField K A
    letI := isUltrametricDist K A
    letI := valuativeRel K A
    letI := valuativeExtension K (E := E) (A := A)
    letI := integerMulSemiringAction K E A
    letI : TopologicalSpace 𝒪[A] := ⊥
    ContinuousSMul (A ≃ₐ[E] A) 𝒪[A] := by
  letI := nontriviallyNormedField K E
  letI := isUltrametricDist K E
  letI : ValuativeRel E := valuativeRel K E
  letI := nontriviallyNormedField K A
  letI := isUltrametricDist K A
  letI : ValuativeRel A := valuativeRel K A
  letI : ValuativeExtension E A := valuativeExtension K (E := E) (A := A)
  letI : MulSemiringAction (A ≃ₐ[E] A) 𝒪[A] :=
    integerMulSemiringAction K E A
  letI : TopologicalSpace 𝒪[A] := ⊥
  letI : DiscreteTopology 𝒪[A] := discreteTopology_bot _
  letI : Algebra.IsIntegral E A :=
    ⟨fun x => IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic x)⟩
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro x
  have hstab :
      (MulAction.stabilizer (A ≃ₐ[E] A) x : Set (A ≃ₐ[E] A)) =
        (MulAction.stabilizer (A ≃ₐ[E] A) (x : A) : Set (A ≃ₐ[E] A)) := by
    ext σ
    change (automorphismIntegerAlgEquiv K E A σ) x = x ↔ σ (x : A) = x
    constructor
    · exact fun h => congrArg Subtype.val h
    · exact fun h => Subtype.ext h
  rw [hstab]
  exact stabilizer_isOpen_of_isIntegral (x : A)

/-- The spectral valuation ring upstairs is integral over the base valuation ring.  This follows
from profinite invariance, rather than being imposed as an extra tower hypothesis. -/
theorem integer_isIntegral [IsGalois E A] :
    letI := nontriviallyNormedField K E
    letI := isUltrametricDist K E
    letI := valuativeRel K E
    letI := nontriviallyNormedField K A
    letI := isUltrametricDist K A
    letI := valuativeRel K A
    letI := valuativeExtension K (E := E) (A := A)
    Algebra.IsIntegral 𝒪[E] 𝒪[A] := by
  letI := nontriviallyNormedField K E
  letI := isUltrametricDist K E
  letI : ValuativeRel E := valuativeRel K E
  letI := nontriviallyNormedField K A
  letI := isUltrametricDist K A
  letI : ValuativeRel A := valuativeRel K A
  letI : ValuativeExtension E A := valuativeExtension K (E := E) (A := A)
  letI : MulSemiringAction (A ≃ₐ[E] A) 𝒪[A] :=
    integerMulSemiringAction K E A
  letI : SMulCommClass (A ≃ₐ[E] A) 𝒪[E] 𝒪[A] :=
    integerSMulCommClass K E A
  letI : TopologicalSpace 𝒪[A] := ⊥
  letI : DiscreteTopology 𝒪[A] := discreteTopology_bot _
  letI : ContinuousSMul (A ≃ₐ[E] A) 𝒪[A] :=
    integer_continuousSMul K E A
  letI : Algebra.IsInvariant 𝒪[E] 𝒪[A] (A ≃ₐ[E] A) :=
    integer_isInvariant K E A
  exact Algebra.IsInvariant.isIntegral_of_profinite
    (A := 𝒪[E]) (B := 𝒪[A]) (G := A ≃ₐ[E] A)

/-- Every automorphism of the residue extension lifts to the algebraic tower. -/
theorem residueGaloisMap_surjective [IsGalois E A] :
    letI := nontriviallyNormedField K E
    letI := isUltrametricDist K E
    letI := valuativeRel K E
    letI := nontriviallyNormedField K A
    letI := isUltrametricDist K A
    letI := valuativeRel K A
    letI := valuativeExtension K (E := E) (A := A)
    Function.Surjective (residueGaloisMap K E A) := by
  letI := nontriviallyNormedField K E
  letI := isUltrametricDist K E
  letI : ValuativeRel E := valuativeRel K E
  letI := nontriviallyNormedField K A
  letI := isUltrametricDist K A
  letI : ValuativeRel A := valuativeRel K A
  letI : ValuativeExtension E A := valuativeExtension K (E := E) (A := A)
  letI : MulSemiringAction (A ≃ₐ[E] A) 𝒪[A] :=
    integerMulSemiringAction K E A
  letI : SMulCommClass (A ≃ₐ[E] A) 𝒪[E] 𝒪[A] :=
    integerSMulCommClass K E A
  letI : TopologicalSpace 𝒪[A] := ⊥
  letI : DiscreteTopology 𝒪[A] := discreteTopology_bot _
  letI : ContinuousSMul (A ≃ₐ[E] A) 𝒪[A] :=
    integer_continuousSMul K E A
  letI : Algebra.IsInvariant 𝒪[E] 𝒪[A] (A ≃ₐ[E] A) :=
    integer_isInvariant K E A
  intro τ
  obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := A ≃ₐ[E] A) (IsLocalRing.maximalIdeal 𝒪[E])
      (IsLocalRing.maximalIdeal 𝒪[A]) τ
  refine ⟨g.1, ?_⟩
  apply AlgEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  have hgy := DFunLike.congr_fun hg (IsLocalRing.residue 𝒪[A] x)
  change (IsLocalRing.ResidueField.mapAlgEquiv'
    (automorphismIntegerAlgEquiv K E A g.1))
      (IsLocalRing.residue 𝒪[A] x) = _
  rw [IsLocalRing.ResidueField.mapAlgEquiv'_residue]
  have haction := Ideal.Quotient.stabilizerHom_apply
    (IsLocalRing.maximalIdeal 𝒪[A]) (IsLocalRing.maximalIdeal 𝒪[E])
      (A ≃ₐ[E] A) g x
  have hgy' : IsLocalRing.residue 𝒪[A] (g.1 • x) =
      τ (IsLocalRing.residue 𝒪[A] x) := haction.symm.trans hgy
  exact hgy'

/-- The spectral residue action is continuous for the Krull topologies. -/
theorem residueGaloisMap_continuous [IsGalois E A] :
    letI := nontriviallyNormedField K E
    letI := isUltrametricDist K E
    letI := valuativeRel K E
    letI := nontriviallyNormedField K A
    letI := isUltrametricDist K A
    letI := valuativeRel K A
    letI := valuativeExtension K (E := E) (A := A)
    Continuous (residueGaloisMap K E A) := by
  letI := nontriviallyNormedField K E
  letI := isUltrametricDist K E
  letI : ValuativeRel E := valuativeRel K E
  letI := nontriviallyNormedField K A
  letI := isUltrametricDist K A
  letI : ValuativeRel A := valuativeRel K A
  letI : ValuativeExtension E A := valuativeExtension K (E := E) (A := A)
  letI : Algebra.IsIntegral 𝒪[E] 𝒪[A] := integer_isIntegral K E A
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro N hN
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨L, hLfin, hLN⟩ := hN
  letI : FiniteDimensional 𝓀[E] L := hLfin
  have hLfg : L.FG := IntermediateField.essFiniteType_iff.mp inferInstance
  obtain ⟨t, ht⟩ := hLfg
  let lift (y : 𝓀[A]) : 𝒪[A] := (IsLocalRing.residue_surjective y).choose
  have lift_spec (y : 𝓀[A]) : IsLocalRing.residue 𝒪[A] (lift y) = y :=
    (IsLocalRing.residue_surjective y).choose_spec
  let S : Set A := (fun y : 𝓀[A] => (lift y : A)) '' (t : Set 𝓀[A])
  let F : IntermediateField E A := IntermediateField.adjoin E S
  have hSfinite : S.Finite := t.finite_toSet.image _
  have hFfg : F.FG := IntermediateField.fg_adjoin_of_finite hSfinite
  letI : Algebra.EssFiniteType E F :=
    IntermediateField.essFiniteType_iff.mpr hFfg
  letI : Module.Finite E F := Algebra.finite_of_essFiniteType_of_isAlgebraic
  letI : FiniteDimensional E F := by infer_instance
  apply mem_nhds_iff.mpr
  use (F.fixingSubgroup : Set (A ≃ₐ[E] A))
  constructor
  · intro σ hσ
    apply hLN
    change residueGaloisMap K E A σ ∈ L.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro z hz
    rw [← ht] at hz
    apply (IntermediateField.forall_mem_adjoin_smul_eq_self_iff 𝓀[E]
      (residueGaloisMap K E A σ)).mpr (fun y hy => ?_) z hz
    have hyS : (lift y : A) ∈ S := ⟨y, hy, rfl⟩
    have hylift : σ (lift y : A) = lift y := by
      change σ ∈ F.fixingSubgroup at hσ
      rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
      exact hσ (lift y : A)
        (IntermediateField.subset_adjoin (F := E) (S := S) hyS)
    change (IsLocalRing.ResidueField.mapAlgEquiv'
      (automorphismIntegerAlgEquiv K E A σ)) y = y
    rw [← lift_spec y, IsLocalRing.ResidueField.mapAlgEquiv'_residue]
    rw [show (automorphismIntegerAlgEquiv K E A σ) (lift y) = lift y from
      Subtype.ext hylift]
  · exact ⟨F.fixingSubgroup_isOpen, congrFun rfl⟩

/-- An integral extension of local rings induces an integral extension of residue fields. -/
theorem residueField_isIntegral
    {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra.IsIntegral R S] :
    Algebra.IsIntegral (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) := by
  constructor
  intro y
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨p, hpmonic, hproot⟩ := Algebra.IsIntegral.isIntegral (R := R) b
  change (Polynomial.aeval b) p = 0 at hproot
  refine ⟨p.map (IsLocalRing.residue R), hpmonic.map _, ?_⟩
  change (Polynomial.aeval (IsLocalRing.residue S b))
    (p.map (IsLocalRing.residue R)) = 0
  rw [← Polynomial.map_aeval_eq_aeval_map
    (φ := IsLocalRing.residue R) (ψ := IsLocalRing.residue S)]
  · rw [hproot, map_zero]
  · ext z
    exact IsLocalRing.ResidueField.algebraMap_residue (R := R) (S := S) z

/-- The automorphism group of any algebraic extension of a finite field is commutative.  Two
automorphisms commute after restriction to the finite field generated by each element. -/
theorem finiteBaseGalois_commutes
    (k L : Type*) [Field k] [Finite k] [Field L] [Algebra k L]
    [Algebra.IsAlgebraic k L]
    (σ τ : L ≃ₐ[k] L) : σ * τ = τ * σ := by
  ext x
  let M : IntermediateField k L := IntermediateField.adjoin k {x}
  letI : FiniteDimensional k M :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  letI : Finite M := Module.finite_of_finite k
  letI : Fintype M := Fintype.ofFinite M
  letI : Normal k M :=
    Normal.of_isSplittingField (X ^ Fintype.card M - X)
  let σM : M ≃ₐ[k] M := σ.restrictNormal M
  let τM : M ≃ₐ[k] M := τ.restrictNormal M
  letI : CommGroup (M ≃ₐ[k] M) := IsCyclic.commGroup
  have hcomm : σM * τM = τM * σM := mul_comm σM τM
  have hx : x ∈ M :=
    IntermediateField.subset_adjoin (F := k) (S := {x}) (Set.mem_singleton x)
  have h := DFunLike.congr_fun hcomm (⟨x, hx⟩ : M)
  simpa [σM, τM, AlgEquiv.restrictNormal_apply] using congrArg Subtype.val h

end SpectralLocalField
end OTriangle
end Anabelian
