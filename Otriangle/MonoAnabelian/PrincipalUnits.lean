import Otriangle.MonoAnabelian.SpectralLocalField
import Mathlib.RingTheory.Henselian
import Mathlib.GroupTheory.Torsion
import Mathlib.FieldTheory.Finite.Basic

/-!
# Prime-to-residue-characteristic divisibility of principal units

For a mixed-characteristic local field `K`, every prime-to-residue-characteristic prime-power
equation `x ^ l = u` with `u` a principal unit has a principal-unit solution.  This is the
Henselian part of the local multiplicative-group calculation underlying Hoshi's Lemma 1.2 and
Lemma 3.4.
-/

noncomputable section

namespace Anabelian
namespace LCFT

open OTriangle
open ValuativeRel

universe u

/-- If `l` differs from the residue characteristic, the `l`th-power map on principal units is
surjective. -/
theorem principalUnit_pow_surjective_of_ne_residueChar
    (K : PointedMixedCharLocalField.{u}) (l : ℕ) (hl : l.Prime)
    (hne : l ≠ K.residueChar) :
    Function.Surjective
      (powMonoidHom
        (α := (valuation K).valuationSubring.principalUnitGroup) l) := by
  letI := K.nontriviallyNormedField
  letI := K.isUltrametricDist
  letI := K.completeSpace
  let A : ValuationSubring K := (valuation K).valuationSubring
  letI : HenselianRing A (IsLocalRing.maximalIdeal A) := by
    change HenselianRing (valuation K).integer
      (IsLocalRing.maximalIdeal (valuation K).integer)
    infer_instance
  intro u
  let uKer : (Units.map (IsLocalRing.residue A).toMonoidHom).ker :=
    A.principalUnitGroupEquiv u
  let uA : A := ((uKer : Aˣ) : A)
  let f : Polynomial A := Polynomial.X ^ l - Polynomial.C uA
  have hf : f.Monic := by
    exact Polynomial.monic_X_pow_sub_C uA hl.ne_zero
  have huResidue : IsLocalRing.residue A uA = 1 := by
    have h := uKer.property
    rw [MonoidHom.mem_ker] at h
    exact Units.ext_iff.mp h
  have hfOne : f.eval 1 ∈ IsLocalRing.maximalIdeal A := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [f, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, one_pow, map_sub, map_one]
    change 1 - IsLocalRing.residue A uA = 0
    rw [huResidue, sub_self]
  letI : CharP (IsLocalRing.ResidueField A) K.residueChar := by
    change CharP (IsLocalRing.ResidueField (valuation K).integer) K.residueChar
    infer_instance
  have hlCast : (l : IsLocalRing.ResidueField A) ≠ 0 := by
    intro hzero
    have hdiv : K.residueChar ∣ l :=
      (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField A)
        K.residueChar l).mp hzero
    rcases (Nat.dvd_prime hl).mp hdiv with hOne | heq
    · exact (Fact.out : K.residueChar.Prime).ne_one hOne
    · exact hne heq.symm
  have hfDeriv : IsUnit
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (f.derivative.eval 1)) := by
    refine ⟨Units.mk0 (l : IsLocalRing.ResidueField A) hlCast, ?_⟩
    change (l : IsLocalRing.ResidueField A) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (f.derivative.eval 1)
    rw [show f.derivative.eval 1 = (l : A) by
      simp [f, Polynomial.derivative_X_pow]]
    exact (map_natCast (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) l).symm
  obtain ⟨a, haRoot, haOne⟩ :=
    HenselianRing.is_henselian f hf (1 : A) hfOne hfDeriv
  have haPow : a ^ l = uA := by
    apply sub_eq_zero.mp
    simpa [Polynomial.IsRoot, f] using haRoot
  have haResidue : IsLocalRing.residue A a = 1 := by
    have hzero : IsLocalRing.residue A (a - 1) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).2 haOne
    rwa [map_sub, map_one, sub_eq_zero] at hzero
  have haUnit : IsUnit a :=
    (IsLocalRing.residue_ne_zero_iff_isUnit a).mp (by simp [haResidue])
  let aKer : (Units.map (IsLocalRing.residue A).toMonoidHom).ker :=
    ⟨haUnit.unit, by
      rw [MonoidHom.mem_ker]
      apply Units.ext
      exact haResidue⟩
  let v : A.principalUnitGroup := A.principalUnitGroupEquiv.symm aKer
  refine ⟨v, ?_⟩
  change v ^ l = u
  apply A.principalUnitGroupEquiv.injective
  rw [map_pow]
  change aKer ^ l = uKer
  apply Subtype.ext
  apply Units.ext
  exact haPow

/-- Every nonzero residue class has a root-of-unity lift in the valuation-ring unit group. -/
theorem residueUnit_has_torsion_lift
    (K : PointedMixedCharLocalField.{u})
    (b : (IsLocalRing.ResidueField
      (valuation K).valuationSubring)ˣ) :
    ∃ t : (valuation K).valuationSubring.unitGroup,
      IsOfFinOrder t ∧
        (valuation K).valuationSubring.unitGroupToResidueFieldUnits t = b := by
  letI := K.nontriviallyNormedField
  letI := K.isUltrametricDist
  letI := K.completeSpace
  let A : ValuationSubring K := (valuation K).valuationSubring
  letI : HenselianRing A (IsLocalRing.maximalIdeal A) := by
    change HenselianRing (valuation K).integer
      (IsLocalRing.maximalIdeal (valuation K).integer)
    infer_instance
  letI : Finite (IsLocalRing.ResidueField A) := by
    change Finite (IsLocalRing.ResidueField (valuation K).integer)
    infer_instance
  letI := Fintype.ofFinite (IsLocalRing.ResidueField A)
  let n := Fintype.card (IsLocalRing.ResidueField A) - 1
  have hn : 0 < n := by
    dsimp [n]
    exact Nat.sub_pos_of_lt Fintype.one_lt_card
  obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective
    (b : IsLocalRing.ResidueField A)
  have ha₀' : IsLocalRing.residue A a₀ = b := by
    exact ha₀
  let f : Polynomial A := Polynomial.X ^ n - 1
  have hf : f.Monic := by
    simpa only [Polynomial.C_1] using
      Polynomial.monic_X_pow_sub_C (1 : A) hn.ne'
  have hfRootMod : f.eval a₀ ∈ IsLocalRing.maximalIdeal A := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [f, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one, map_sub, map_pow, map_one]
    change (IsLocalRing.residue A a₀) ^ n - 1 = 0
    rw [ha₀']
    exact sub_eq_zero.mpr
      (FiniteField.pow_card_sub_one_eq_one (b : IsLocalRing.ResidueField A)
        (Units.ne_zero b))
  have hnCast : (n : IsLocalRing.ResidueField A) = -1 := by
    dsimp [n]
    rw [Nat.cast_sub ((Nat.succ_le_iff).2 Fintype.card_pos), Nat.cast_card_eq_zero,
      Nat.cast_one, zero_sub]
  have hfDerivNe : IsLocalRing.residue A (f.derivative.eval a₀) ≠ 0 := by
    have heqA : f.derivative.eval a₀ = (n : A) * a₀ ^ (n - 1) := by
      simp [f, Polynomial.derivative_X_pow]
    have heq : IsLocalRing.residue A (f.derivative.eval a₀) =
        (n : IsLocalRing.ResidueField A) *
          (IsLocalRing.residue A a₀) ^ (n - 1) := by
      rw [heqA, map_mul, map_natCast, map_pow]
    rw [heq, hnCast, ha₀']
    exact mul_ne_zero (neg_ne_zero.mpr one_ne_zero) (pow_ne_zero _ (Units.ne_zero b))
  have hfDeriv : IsUnit
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (f.derivative.eval a₀)) := by
    refine ⟨Units.mk0 (IsLocalRing.residue A (f.derivative.eval a₀)) hfDerivNe, rfl⟩
  obtain ⟨a, haRoot, haCongr⟩ :=
    HenselianRing.is_henselian f hf a₀ hfRootMod hfDeriv
  have haPow : a ^ n = 1 := by
    apply sub_eq_zero.mp
    simpa [Polynomial.IsRoot, f] using haRoot
  have haResidue : IsLocalRing.residue A a = b := by
    have hzero : IsLocalRing.residue A (a - a₀) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).2 haCongr
    rw [map_sub, sub_eq_zero] at hzero
    exact hzero.trans ha₀'
  have haUnit : IsUnit a := IsUnit.of_pow_eq_one haPow hn.ne'
  let t : A.unitGroup := A.unitGroupMulEquiv.symm haUnit.unit
  refine ⟨t, ?_, ?_⟩
  · apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨n, hn, ?_⟩
    apply A.unitGroupMulEquiv.injective
    rw [map_pow, map_one]
    apply Units.ext
    exact haPow
  · apply Units.ext
    exact haResidue

/-- Away from the residue characteristic, every valuation-ring unit is a torsion unit times an
`l`th power. -/
theorem integerUnit_eq_torsion_mul_pow
    (K : PointedMixedCharLocalField.{u}) (l : ℕ) (hl : l.Prime)
    (hne : l ≠ K.residueChar)
    (u : (valuation K).valuationSubring.unitGroup) :
    ∃ t : (valuation K).valuationSubring.unitGroup,
      IsOfFinOrder t ∧
        ∃ v : (valuation K).valuationSubring.unitGroup, u = t * v ^ l := by
  let A : ValuationSubring K := (valuation K).valuationSubring
  let b := A.unitGroupToResidueFieldUnits u
  obtain ⟨t, ht, htResidue⟩ := residueUnit_has_torsion_lift K b
  have hwKer : u * t⁻¹ ∈ A.unitGroupToResidueFieldUnits.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, htResidue, mul_inv_cancel]
  rw [A.ker_unitGroupToResidueFieldUnits] at hwKer
  let w : A.principalUnitGroup :=
    ⟨((u * t⁻¹ : A.unitGroup) : Kˣ), hwKer⟩
  obtain ⟨z, hz⟩ :=
    principalUnit_pow_surjective_of_ne_residueChar K l hl hne w
  let v : A.unitGroup := ⟨(z : Kˣ), A.principal_units_le_units z.property⟩
  refine ⟨t, ht, v, ?_⟩
  apply Subtype.ext
  change (u : Kˣ) = (t : Kˣ) * (z : Kˣ) ^ l
  have hz' := congrArg Subtype.val hz
  change (z : Kˣ) ^ l = (u : Kˣ) * (t : Kˣ)⁻¹ at hz'
  rw [hz']
  simp

/-- The torsion-free quotient of the valuation-ring unit group. -/
abbrev IntegerUnitTorsionFreeQuotient
    (K : PointedMixedCharLocalField.{u}) :=
  (valuation K).valuationSubring.unitGroup ⧸
    CommGroup.torsion (valuation K).valuationSubring.unitGroup

/-- Away from the residue characteristic, the torsion-free valuation-ring unit group is
`l`-divisible. -/
theorem integerUnitTorsionFree_pow_surjective_of_ne_residueChar
    (K : PointedMixedCharLocalField.{u}) (l : ℕ) (hl : l.Prime)
    (hne : l ≠ K.residueChar) :
    Function.Surjective
      (powMonoidHom (α := IntegerUnitTorsionFreeQuotient K) l) := by
  intro y
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective
    (CommGroup.torsion (valuation K).valuationSubring.unitGroup) y
  obtain ⟨t, ht, v, hu⟩ :=
    integerUnit_eq_torsion_mul_pow K l hl hne u
  refine ⟨(v : IntegerUnitTorsionFreeQuotient K), ?_⟩
  change (v : IntegerUnitTorsionFreeQuotient K) ^ l =
    (u : IntegerUnitTorsionFreeQuotient K)
  rw [hu]
  change ((v ^ l : (valuation K).valuationSubring.unitGroup) :
      IntegerUnitTorsionFreeQuotient K) =
    ((t * v ^ l : (valuation K).valuationSubring.unitGroup) :
      IntegerUnitTorsionFreeQuotient K)
  rw [QuotientGroup.eq_iff_div_mem]
  have htInv := (CommGroup.torsion
    (valuation K).valuationSubring.unitGroup).inv_mem ht
  simpa [div_eq_mul_inv, mul_comm] using htInv

end LCFT
end Anabelian
