import Otriangle.MonoAnabelian.ResidueProcyclic

/-!
# Torsion-freeness of the residue absolute Galois group

The absolute Galois group of a finite field is not merely procyclic: it is torsion-free.  The
proof below works directly in the chosen algebraic closure.  If an automorphism is killed by
`n`, then around each element we enlarge its finite Galois field of definition to one whose
degree is divisible by `d * n`.  The finite-field Frobenius calculation then forces the
automorphism to act trivially on the original degree-`d` field.
-/

noncomputable section

namespace Anabelian.LCFT

open OTriangle

universe u

private theorem pow_mul_eq_one_of_eq
    {G : Type*} [Monoid G] (x y : G) (a n : ℕ)
    (hxy : x ^ a = y) (hy : y ^ n = 1) : x ^ (a * n) = 1 := by
  rw [pow_mul, hxy, hy]

private theorem exists_residueFiniteGaloisIntermediateField_super_degree_mul
    (K : PointedMixedCharLocalField.{u})
    (L : FiniteGaloisIntermediateField (ResidueField K)
      (AlgebraicClosureResidueField K))
    (n : ℕ) [NeZero n] :
    ∃ M : FiniteGaloisIntermediateField (ResidueField K)
        (AlgebraicClosureResidueField K),
      L.toIntermediateField ≤ M.toIntermediateField ∧
      Module.finrank (ResidueField K) L * n ∣
        Module.finrank (ResidueField K) M := by
  let k := ResidueField K
  let Ω := AlgebraicClosureResidueField K
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  letI : IsGalois k Ω := ⟨⟩
  letI : Finite L := Module.finite_of_finite k
  letI : CharP L K.residueChar :=
    charP_of_injective_algebraMap' k K.residueChar
  let E := FiniteField.Extension L K.residueChar n
  let ι : E →ₐ[L] Ω := IsAlgClosed.lift
  let N : IntermediateField L Ω := ι.fieldRange
  letI : FiniteDimensional L N :=
    Module.Finite.equiv ι.equivFieldRange.toLinearEquiv
  letI : Finite N := Module.finite_of_finite L
  haveI : IsScalarTower k L N := IsScalarTower.of_algebraMap_eq' rfl
  let NR : IntermediateField k Ω := N.restrictScalars k
  let eNR : NR ≃ₐ[k] N :=
    { toFun := fun y => ⟨y.1, y.2⟩
      invFun := fun y => ⟨y.1, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  let M : FiniteGaloisIntermediateField k Ω :=
    FiniteGaloisIntermediateField.adjoin k (N : Set Ω)
  have hNM : NR ≤ M := by
    intro y hy
    exact FiniteGaloisIntermediateField.subset_adjoin k (N : Set Ω) hy
  have hLM : L.toIntermediateField ≤ M.toIntermediateField := by
    intro y hy
    apply hNM
    change (y : Ω) ∈ ι.fieldRange
    refine ⟨algebraMap L E ⟨y, hy⟩, ?_⟩
    change ι (algebraMap L E ⟨y, hy⟩) = y
    calc
      ι (algebraMap L E ⟨y, hy⟩) =
          algebraMap L Ω ⟨y, hy⟩ := ι.commutes ⟨y, hy⟩
      _ = y := rfl
  letI : Algebra NR M :=
    RingHom.toAlgebra (IntermediateField.inclusion hNM)
  letI : IsScalarTower k NR M := IsScalarTower.of_algebraMap_eq' rfl
  have hNrank : Module.finrank k N = Module.finrank k L * n := by
    rw [← Module.finrank_mul_finrank k L N]
    congr 1
    change Module.finrank L ι.fieldRange = n
    rw [← ι.equivFieldRange.toLinearEquiv.finrank_eq]
    exact FiniteField.finrank_extension L K.residueChar n
  refine ⟨M, hLM, ?_⟩
  rw [← hNrank, ← eNR.toLinearEquiv.finrank_eq,
    ← Module.finrank_mul_finrank k NR M]
  exact dvd_mul_right _ _

/-- Every finite-order element of the residue absolute Galois group is trivial. -/
theorem residueAbsoluteGaloisGroup_isOfFinOrder_eq_one
    (K : PointedMixedCharLocalField.{u})
    (σ : ResidueAbsoluteGaloisGroup K) (hσ : IsOfFinOrder σ) : σ = 1 := by
  let k := ResidueField K
  let Ω := AlgebraicClosureResidueField K
  letI : Fintype k := Fintype.ofFinite k
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  letI : IsGalois k Ω := ⟨⟩
  obtain ⟨n, hn, hpow⟩ := hσ.exists_pow_eq_one
  apply AlgEquiv.ext
  intro x
  let L : FiniteGaloisIntermediateField k Ω :=
    FiniteGaloisIntermediateField.adjoin k {x}
  let d := Module.finrank k L
  letI : Finite L := Module.finite_of_finite k
  letI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨M, hLM, hdnM⟩ :=
    exists_residueFiniteGaloisIntermediateField_super_degree_mul K L n
  letI : Finite M := Module.finite_of_finite k
  let σM : M ≃ₐ[k] M := σ.restrictNormal M
  obtain ⟨a, ha⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k M).2 σM
  let φM : M ≃ₐ[k] M := FiniteField.frobeniusAlgEquivOfAlgebraic k M
  have hσMpow : σM ^ n = 1 := by
    change (σ.restrictNormalHom M) ^ n = 1
    rw [← map_pow, hpow, map_one]
  change φM ^ a.1 = σM at ha
  have hφpow : φM ^ (a.1 * n) = 1 :=
    pow_mul_eq_one_of_eq φM σM a.1 n ha hσMpow
  have hMdvd : Module.finrank k M ∣ a.1 * n := by
    have hord := FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic k M
    convert orderOf_dvd_of_pow_eq_one hφpow using 1
    exact hord.symm
  have hdvd : d ∣ a.1 := by
    apply (mul_dvd_mul_iff_right hn.ne').mp
    exact hdnM.trans hMdvd
  obtain ⟨b, hb⟩ := hdvd
  have hxL : x ∈ L.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin k {x} (by simp)
  let xm : M := ⟨x, hLM hxL⟩
  have ha_x := DFunLike.congr_fun ha xm
  let φL : L ≃ₐ[k] L := FiniteField.frobeniusAlgEquivOfAlgebraic k L
  have hφLd : φL ^ d = 1 := by
    have hord := FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic k L
    change φL ^ Module.finrank k L = 1
    rw [← hord]
    exact pow_orderOf_eq_one φL
  let xl : L := ⟨x, hxL⟩
  have hφLd_x : (φL ^ d) xl = xl := by
    rw [hφLd]
    rfl
  have hφMd_x : (φM ^ d) xm = xm := by
    apply Subtype.ext
    change ((φM ^ d) xm : Ω) = x
    simp only [φM, AlgEquiv.coe_pow]
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    have h := congrArg Subtype.val hφLd_x
    simp only [φL, AlgEquiv.coe_pow] at h
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate] at h
    exact h
  have hφMd_pow_x : ∀ m : ℕ, ((φM ^ d) ^ m) xm = xm := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        rw [pow_succ, AlgEquiv.mul_apply, hφMd_x, ih]
  have hφMa_x : (φM ^ a.1) xm = xm := by
    rw [hb, pow_mul]
    exact hφMd_pow_x b
  have hσM_x : σM xm = xm := ha_x ▸ hφMa_x
  have hσx := congrArg Subtype.val hσM_x
  change σ x = x
  simpa [σM, xm, AlgEquiv.restrictNormal_apply] using hσx

end Anabelian.LCFT
