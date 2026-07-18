import Otriangle.OTriangle.Core
import Mathlib.RingTheory.Norm.Basic

/-!
# Specification of local reciprocity

This file records the characterization of the local reciprocity maps for mixed-characteristic
local fields. The existence and uniqueness of the reciprocity family remain the two interface
assumptions; the surrounding residue, inertia, Frobenius, and functorial constructions are
implemented here.

The three defining properties are:

1. units map isomorphically onto inertia;
2. every uniformizer maps to arithmetic Frobenius modulo inertia;
3. reciprocity is compatible with norms along finite extensions.
-/

noncomputable section

open ValuativeRel

namespace Anabelian
namespace LCFT

open OTriangle
open scoped Topology commutatorElement

universe u

/-- The absolute Galois group attached to the algebraic closure fixed by `K`. -/
abbrev AbsoluteGaloisGroup (K : PointedMixedCharLocalField.{u}) : Type u :=
  K.algebraicClosure ≃ₐ[K] K.algebraicClosure

/-- The topological abelianization of the absolute Galois group attached to `K`. -/
abbrev AbelianizedAbsoluteGaloisGroup (K : PointedMixedCharLocalField.{u}) : Type u :=
  TopologicalAbelianization (AbsoluteGaloisGroup K)

/-- The residue field of `K`. -/
abbrev ResidueField (K : PointedMixedCharLocalField.{u}) : Type u :=
  𝓀[K]

/-- The residue field of the fixed algebraic closure `K̄`, formed directly from the
`ValuativeRel` carried by `K.algebraicClosure`. -/
abbrev AlgebraicClosureResidueField (K : PointedMixedCharLocalField.{u}) : Type u :=
  𝓀[K.algebraicClosure]

/-- The canonical valuation on the chosen algebraic closure extends the canonical valuation on
`K`.  This is the `Valuation.HasExtension` form of the `ValuativeExtension` field carried by a
pointed local field. -/
noncomputable abbrev algebraicClosureValuationHasExtension
    (K : PointedMixedCharLocalField.{u}) :
    (valuation K).HasExtension (valuation K.algebraicClosure) :=
  inferInstance

/-- The residue-field extension induced by the valuative extension `K̄/K`. -/
noncomputable abbrev algebraicClosureResidueFieldAlgebra
    (K : PointedMixedCharLocalField.{u}) :
    Algebra (ResidueField K) (AlgebraicClosureResidueField K) :=
  inferInstance

noncomputable abbrev algebraicClosureResidueFieldModule
    (K : PointedMixedCharLocalField.{u}) :
    Module (ResidueField K) (AlgebraicClosureResidueField K) :=
  (algebraicClosureResidueFieldAlgebra K).toModule

noncomputable abbrev algebraicClosureResidueFieldIsTorsionFree
    (K : PointedMixedCharLocalField.{u}) :
    Module.IsTorsionFree (ResidueField K) (AlgebraicClosureResidueField K) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (RingHom.injective (algebraMap (ResidueField K) (AlgebraicClosureResidueField K)))

/-- The residue field of an algebraically closed valued field is algebraically closed. -/
private theorem residueField_isAlgClosed
    (L : Type u) [Field L] [ValuativeRel L] [IsAlgClosed L] : IsAlgClosed 𝓀[L] := by
  let v := valuation L
  let A := v.integer
  apply IsAlgClosed.of_exists_root
  intro p hp hirr
  have hlifts : p ∈ Polynomial.lifts (IsLocalRing.residue A) := by
    rw [Polynomial.mem_lifts]
    exact Polynomial.map_surjective _ IsLocalRing.residue_surjective p
  obtain ⟨q, hqp, hqdeg, hqmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlifts hp
  have hqdeg0 : (q.map (algebraMap A L)).degree ≠ 0 := by
    rw [hqmonic.degree_map]
    exact (Polynomial.natDegree_pos_iff_degree_pos.mp <| hqdeg ▸ hirr.natDegree_pos).ne'
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root (q.map (algebraMap A L)) hqdeg0
  change (q.map (algebraMap A L)).eval y = 0 at hy
  have hyint : IsIntegral A y := by
    refine ⟨q, hqmonic, ?_⟩
    simpa [Polynomial.eval_map] using hy
  have hymem : y ∈ v.integer :=
    Valuation.Integers.mem_of_integral (Valuation.integer.integers v) hyint
  let yA : A := ⟨y, hymem⟩
  refine ⟨IsLocalRing.residue A yA, ?_⟩
  rw [← hqp, Polynomial.eval_map_apply]
  have hqy : q.eval yA = 0 := by
    apply Subtype.ext
    have heval := Polynomial.eval_map_apply (f := algebraMap A L) (p := q) yA
    rw [show algebraMap A L yA = y from rfl] at heval
    exact heval.symm.trans hy
  rw [hqy, map_zero]

/-- The residue extension induced by an algebraic valued extension is algebraic.  For a lift of a
residue element, normalize its minimal polynomial by a coefficient of maximal valuation.  The
normalized polynomial has integral coefficients, while the chosen coefficient reduces to one, so
its reduction is a nonzero polynomial annihilating the residue element. -/
private theorem algebraicClosureResidueField_isAlgebraic
    (K : PointedMixedCharLocalField.{u}) :
    Algebra.IsAlgebraic (ResidueField K) (AlgebraicClosureResidueField K) := by
  rw [Algebra.isAlgebraic_def]
  intro x
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective x
  let p : Polynomial K := minpoly K (b : K.algebraicClosure)
  have hbint : IsIntegral K (b : K.algebraicClosure) :=
    Algebra.IsIntegral.isIntegral (b : K.algebraicClosure)
  have hp0 : p ≠ 0 := minpoly.ne_zero hbint
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image p.support
    (fun n => valuation K (p.coeff n)) (Polynomial.support_nonempty.mpr hp0)
  have hci : p.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  let r : Polynomial K := Polynomial.C (p.coeff i)⁻¹ * p
  have hrcoeff (n : ℕ) : valuation K (r.coeff n) ≤ 1 := by
    simp only [r, Polynomial.coeff_C_mul, map_mul]
    by_cases hn : p.coeff n = 0
    · simp [hn]
    · rw [Valuation.map_inv, inv_mul_le_one₀ ((valuation K).pos_iff.mpr hci)]
      exact hmax n (Polynomial.mem_support_iff.mpr hn)
  have hrlifts : r ∈ Polynomial.lifts (algebraMap 𝒪[K] K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨r.coeff n, hrcoeff n⟩, rfl⟩
  obtain ⟨q, hq⟩ := Polynomial.mem_lifts r |>.mp hrlifts
  let qbar : Polynomial (ResidueField K) := q.map (IsLocalRing.residue 𝒪[K])
  have hqcoeff : q.coeff i = 1 := by
    apply Subtype.ext
    have h := congrArg (fun f : Polynomial K ↦ f.coeff i) hq
    simpa [r, hci] using h
  have hqbar0 : qbar ≠ 0 := by
    intro h
    have hc := congrArg (fun f : Polynomial (ResidueField K) ↦ f.coeff i) h
    simp [qbar, hqcoeff] at hc
  refine ⟨qbar, hqbar0, ?_⟩
  have hqroot : (Polynomial.aeval b) q = 0 := by
    have heval := Polynomial.map_aeval_eq_aeval_map
      (φ := algebraMap 𝒪[K] K)
      (ψ := algebraMap 𝒪[K.algebraicClosure] K.algebraicClosure)
      (by
        ext z
        exact IsScalarTower.algebraMap_apply 𝒪[K] K K.algebraicClosure z)
      q b
    have hroot : (Polynomial.aeval (b : K.algebraicClosure))
        (q.map (algebraMap 𝒪[K] K)) = 0 := by
      rw [hq]
      change (Polynomial.aeval (b : K.algebraicClosure))
        (Polynomial.C (p.coeff i)⁻¹ * p) = 0
      rw [map_mul, Polynomial.aeval_C]
      change (algebraMap K K.algebraicClosure) (p.coeff i)⁻¹ *
        (Polynomial.aeval (b : K.algebraicClosure)) (minpoly K (b : K.algebraicClosure)) = 0
      rw [minpoly.aeval, mul_zero]
    apply (Valuation.integer.integers (valuation K.algebraicClosure)).hom_inj
    simpa only [map_zero] using heval.trans hroot
  change (Polynomial.aeval (IsLocalRing.residue 𝒪[K.algebraicClosure] b)) qbar = 0
  simp only [qbar]
  rw [← Polynomial.map_aeval_eq_aeval_map
    (φ := IsLocalRing.residue 𝒪[K])
    (ψ := IsLocalRing.residue 𝒪[K.algebraicClosure])]
  · rw [hqroot, map_zero]
  · ext z
    simp only [RingHom.comp_apply]
    exact IsLocalRing.ResidueField.algebraMap_residue
      (R := 𝒪[K]) (S := 𝒪[K.algebraicClosure]) z

/-- The residue field of the fixed algebraic closure of `K` is an algebraic closure of the residue
field of `K`. -/
noncomputable instance algebraicClosureResidueFieldIsAlgClosure
    (K : PointedMixedCharLocalField.{u}) :
    IsAlgClosure (ResidueField K) (AlgebraicClosureResidueField K) := by
  letI : IsAlgClosed K.algebraicClosure := IsAlgClosure.isAlgClosed K
  exact ⟨residueField_isAlgClosed K.algebraicClosure,
    algebraicClosureResidueField_isAlgebraic K⟩

/-- The absolute Galois group of the residue field, computed using the algebraic closure induced by
`K.algebraicClosure`. -/
abbrev ResidueAbsoluteGaloisGroup (K : PointedMixedCharLocalField.{u}) : Type u :=
  AlgebraicClosureResidueField K ≃ₐ[ResidueField K] AlgebraicClosureResidueField K

/-- A continuous homomorphism from a topological group to a Hausdorff commutative group factors
through the topological abelianization. -/
private noncomputable def topologicalAbelianizationLift
    {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CommGroup A] [TopologicalSpace A] [T2Space A]
    (f : G →* A) (hf : Continuous f) : TopologicalAbelianization G →* A :=
  QuotientGroup.lift (Subgroup.topologicalClosure (commutator G)) f (by
    apply Subgroup.topologicalClosure_minimal
      (t := Subgroup.comap f (⊥ : Subgroup A))
    · change ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.comap f (⊥ : Subgroup A)
      rw [Subgroup.commutator_le]
      intro g _ h _
      change f ⁅g, h⁆ = 1
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
    · change IsClosed (f ⁻¹' ({1} : Set A))
      exact isClosed_singleton.preimage hf)

/-- The residue action after passing to the topological abelianization. -/
private noncomputable def residueGaloisAbelianizationMap
    (K : PointedMixedCharLocalField.{u}) :
    AbelianizedAbsoluteGaloisGroup K →* ResidueAbsoluteGaloisGroup K := by
  letI : CommGroup (ResidueAbsoluteGaloisGroup K) :=
    { (inferInstance : Group (ResidueAbsoluteGaloisGroup K)) with
      mul_comm := K.residueGaloisMap_commutes }
  exact topologicalAbelianizationLift K.residueGaloisMap
    K.residueGaloisMap_continuous

private theorem residueGaloisAbelianizationMap_surjective
    (K : PointedMixedCharLocalField.{u}) :
    Function.Surjective (residueGaloisAbelianizationMap K) := by
  intro τ
  obtain ⟨σ, rfl⟩ := K.residueGaloisMap_surjective τ
  refine ⟨QuotientGroup.mk'
    (Subgroup.topologicalClosure (commutator (AbsoluteGaloisGroup K))) σ, ?_⟩
  rfl

/-- The inertia subgroup in the abelianized absolute Galois group. -/
noncomputable def inertiaSubgroup (K : PointedMixedCharLocalField.{u}) :
    Subgroup (AbelianizedAbsoluteGaloisGroup K) :=
  (residueGaloisAbelianizationMap K).ker

/-- The canonical identification of the quotient by inertia with the absolute Galois group of the
residue field. -/
noncomputable def unramifiedQuotientEquiv (K : PointedMixedCharLocalField.{u}) :
    (AbelianizedAbsoluteGaloisGroup K ⧸ inertiaSubgroup K) ≃*
      ResidueAbsoluteGaloisGroup K :=
  QuotientGroup.quotientKerEquivOfSurjective (residueGaloisAbelianizationMap K)
    (residueGaloisAbelianizationMap_surjective K)

/-- Arithmetic Frobenius in the absolute Galois group of the finite residue field. -/
noncomputable def residueFrobenius (K : PointedMixedCharLocalField.{u}) :
    ResidueAbsoluteGaloisGroup K := by
  letI := Fintype.ofFinite (ResidueField K)
  exact FiniteField.frobeniusAlgEquivOfAlgebraic _ _

/-- Our Frobenius convention is arithmetic Frobenius: it raises elements to the cardinality of the
residue field. -/
theorem residueFrobenius_apply (K : PointedMixedCharLocalField.{u})
    (x : AlgebraicClosureResidueField K) :
    (show AlgebraicClosureResidueField K ≃ₐ[ResidueField K]
        AlgebraicClosureResidueField K from residueFrobenius K) x =
      x ^ Nat.card (ResidueField K) := by
  letI := Fintype.ofFinite (ResidueField K)
  rw [residueFrobenius, FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
  exact congrArg (x ^ ·) Fintype.card_eq_nat_card

/-- The canonical inclusion `𝒪_Kˣ → Kˣ`. -/
noncomputable def integerUnitsToFieldUnits (K : PointedMixedCharLocalField.{u}) :
    𝒪[K]ˣ →* Kˣ :=
  Units.map (algebraMap 𝒪[K] K)

/-- The subgroup `𝒪_Kˣ ≤ Kˣ`. -/
noncomputable def integerUnitSubgroup (K : PointedMixedCharLocalField.{u}) : Subgroup Kˣ :=
  MonoidHom.range (integerUnitsToFieldUnits K)

/-- A nonzero element of `K` is a uniformizer when its valuation is the distinguished generator of
the discrete value group. -/
def IsUniformizer (K : PointedMixedCharLocalField.{u}) (π : Kˣ) : Prop :=
  valuation K (π : K) = ValuativeRel.uniformizer K

/-- The type of candidate reciprocity homomorphisms for `K`. -/
abbrev ReciprocityHom (K : PointedMixedCharLocalField.{u}) :=
  Kˣ →* AbelianizedAbsoluteGaloisGroup K

/-- The first local-reciprocity condition: the restriction to `𝒪_Kˣ` is an isomorphism onto
inertia. -/
structure MapsUnitsIsomorphically (K : PointedMixedCharLocalField.{u})
    (rec : ReciprocityHom K) where
  /-- The isomorphism induced by reciprocity between units and inertia. -/
  unitsEquiv : 𝒪[K]ˣ ≃* inertiaSubgroup K
  /-- The isomorphism is the restriction of the reciprocity homomorphism. -/
  compatibility :
    (inertiaSubgroup K).subtype.comp unitsEquiv.toMonoidHom =
      rec.comp (integerUnitsToFieldUnits K)

/-- The units condition implies that reciprocity descends to the quotients by units and inertia. -/
theorem integerUnitSubgroup_le_comap_inertia {K : PointedMixedCharLocalField.{u}}
    {rec : ReciprocityHom K} (h : MapsUnitsIsomorphically K rec) :
    integerUnitSubgroup K ≤ Subgroup.comap rec (inertiaSubgroup K) := by
  rintro _ ⟨u, rfl⟩
  change rec (integerUnitsToFieldUnits K u) ∈ inertiaSubgroup K
  rw [← MonoidHom.comp_apply, ← h.compatibility]
  exact (h.unitsEquiv u).property

/-- The map `Kˣ / 𝒪_Kˣ → Gal_K^ab / I_K` induced by a candidate reciprocity map satisfying the
units condition. -/
noncomputable def inducedUnramifiedMap {K : PointedMixedCharLocalField.{u}}
    (rec : ReciprocityHom K) (h : MapsUnitsIsomorphically K rec) :
    (Kˣ ⧸ integerUnitSubgroup K) →*
      (AbelianizedAbsoluteGaloisGroup K ⧸ inertiaSubgroup K) :=
  QuotientGroup.map (integerUnitSubgroup K) (inertiaSubgroup K) rec
    (integerUnitSubgroup_le_comap_inertia h)

/-- The second local-reciprocity condition: the class of every uniformizer maps to arithmetic
Frobenius under the canonical identification of the unramified quotient with the residue-field
absolute Galois group. -/
def MapsUniformizersToFrobenius {K : PointedMixedCharLocalField.{u}}
    (rec : ReciprocityHom K) (h : MapsUnitsIsomorphically K rec) : Prop :=
  ∀ (π : Kˣ), IsUniformizer K π →
    unramifiedQuotientEquiv K
        (inducedUnramifiedMap rec h ((QuotientGroup.mk' (integerUnitSubgroup K)) π)) =
      residueFrobenius K

/-- A local reciprocity map for one field, equipped with the units and Frobenius properties that
characterize it. -/
structure LocalReciprocityMap (K : PointedMixedCharLocalField.{u}) where
  /-- The reciprocity homomorphism `Kˣ → Gal_K^ab`. -/
  toMonoidHom : ReciprocityHom K
  /-- Units map isomorphically onto inertia. -/
  mapsUnits : MapsUnitsIsomorphically K toMonoidHom
  /-- Uniformizers map to arithmetic Frobenius modulo inertia. -/
  mapsUniformizers : MapsUniformizersToFrobenius toMonoidHom mapsUnits

namespace LocalReciprocityMap

instance (K : PointedMixedCharLocalField.{u}) :
    CoeFun (LocalReciprocityMap K) (fun _ ↦ Kˣ → AbelianizedAbsoluteGaloisGroup K) where
  coe rec := rec.toMonoidHom

end LocalReciprocityMap

/-- A finite extension between pointed mixed-characteristic local fields. The chosen algebraic
closures are not required to be related: the induced map on abelianized absolute Galois groups is
canonical and is specified separately below. -/
@[pp_with_univ]
structure FiniteExtension (K L : PointedMixedCharLocalField.{u}) where
  [algebra : Algebra K L]
  [finiteDimensional : FiniteDimensional K L]

/-- A continuous homomorphism of topological groups descends to their topological
abelianizations. -/
private noncomputable def topologicalAbelianizationMap
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
    (f : G →* H) (hf : Continuous f) :
    TopologicalAbelianization G →* TopologicalAbelianization H :=
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

/-- Conjugating automorphisms by an algebra equivalence is continuous for the Krull topologies. -/
private theorem continuous_autCongr
    {k A B : Type*} [Field k] [Field A] [Field B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B) :
    Continuous (AlgEquiv.autCongr e : (A ≃ₐ[k] A) → (B ≃ₐ[k] B)) := by
  apply continuous_of_tendsto_nhds_one (AlgEquiv.autCongr e).toMonoidHom
  rw [Filter.tendsto_def]
  intro s hs
  rw [krullTopology_mem_nhds_one_iff k B] at hs
  obtain ⟨E, hE, hEs⟩ := hs
  letI : FiniteDimensional k E := hE
  let F : IntermediateField k A := E.map e.symm.toAlgHom
  have hF : FiniteDimensional k F := by
    exact Module.Finite.equiv
      (IntermediateField.equivMap E e.symm.toAlgHom).toLinearEquiv
  rw [krullTopology_mem_nhds_one_iff k A]
  refine ⟨F, hF, ?_⟩
  intro σ hσ
  apply hEs
  change σ ∈ F.fixingSubgroup at hσ
  change AlgEquiv.autCongr e σ ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  intro x hx
  change e (σ (e.symm x)) = x
  rw [hσ]
  · exact e.apply_symm_apply x
  · exact ⟨x, hx, rfl⟩

/-- Restriction from `L`-automorphisms to `K`-automorphisms is continuous when `L/K` is finite. -/
private theorem continuous_restrictScalars
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

namespace FiniteExtension

/-- The norm homomorphism `Lˣ → Kˣ` of a finite extension. -/
noncomputable def norm {K L : PointedMixedCharLocalField.{u}} (E : FiniteExtension K L) :
    Lˣ →* Kˣ := by
  letI := E.algebra
  letI := E.finiteDimensional
  exact Units.map (Algebra.norm K)

/-- The canonical map `Gal_L^ab → Gal_K^ab` induced by a finite extension `L/K`. At the level of
absolute Galois groups this depends on a choice of compatible algebraic closures only up to inner
conjugacy, so its abelianization is canonical. -/
noncomputable def abelianizedGaloisMap {K L : PointedMixedCharLocalField.{u}}
    (E : FiniteExtension K L) :
    AbelianizedAbsoluteGaloisGroup L →* AbelianizedAbsoluteGaloisGroup K := by
  letI : Algebra K L := E.algebra
  letI : FiniteDimensional K L := E.finiteDimensional
  letI : Algebra K L.algebraicClosure :=
    ((algebraMap L L.algebraicClosure).comp (algebraMap K L)).toAlgebra
  letI : IsScalarTower K L L.algebraicClosure := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsAlgClosure K L.algebraicClosure :=
    IsAlgClosure.ofAlgebraic K L L.algebraicClosure
  let e : L.algebraicClosure ≃ₐ[K] K.algebraicClosure :=
    IsAlgClosure.equiv K L.algebraicClosure K.algebraicClosure
  let f : AbsoluteGaloisGroup L →* AbsoluteGaloisGroup K :=
    (AlgEquiv.autCongr e).toMonoidHom.comp (AlgEquiv.restrictScalarsHom K)
  exact topologicalAbelianizationMap f
    ((continuous_autCongr e).comp continuous_restrictScalars)

end FiniteExtension

/-- A family of local reciprocity maps satisfying the three characterizing properties from local
class field theory. -/
structure LocalReciprocityFamily where
  /-- The local reciprocity map for every pointed mixed-characteristic local field. -/
  map : (K : PointedMixedCharLocalField.{u}) → LocalReciprocityMap K
  /-- The third local-reciprocity condition: for every finite extension `L/K`, reciprocity
  intertwines the norm `Lˣ → Kˣ` with the canonical map `Gal_L^ab → Gal_K^ab`. -/
  norm_naturality : ∀ (K L : PointedMixedCharLocalField.{u}) (E : FiniteExtension K L),
    (map K).toMonoidHom.comp E.norm =
      E.abelianizedGaloisMap.comp (map L).toMonoidHom

/-- Existence of the family of local reciprocity maps. This is the local existence theorem of
local class field theory and is intentionally left outside the present specification. -/
theorem localReciprocityFamily_exists : Nonempty (LocalReciprocityFamily.{u}) := by
  sorry -- Note: Leave this as a sorry!

/-- The family of local reciprocity maps selected by the specification. -/
noncomputable def localReciprocityFamily : LocalReciprocityFamily.{u} :=
  localReciprocityFamily_exists.some

/-- The three properties characterize the whole family of local reciprocity maps. -/
theorem localReciprocityFamily_unique (r s : LocalReciprocityFamily.{u}) : r = s := by
  sorry -- Note: Leave this as a sorry!

end LCFT
end Anabelian
