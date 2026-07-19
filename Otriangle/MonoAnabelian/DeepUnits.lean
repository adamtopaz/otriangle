import Otriangle.MonoAnabelian.PrincipalUnits
import Mathlib.Algebra.Ring.GeomSum

/-!
# Torsion-free deep principal units

Let `p` be the residue characteristic of a mixed-characteristic local field `K`.  The units
`x` satisfying `v(x - 1) < v(p)` form a subgroup, and this subgroup is torsion-free.  This is
the elementary valuation-theoretic torsion control needed for the residue-characteristic part
of the mod-power calculation behind Hoshi's Lemma 1.2 and Lemma 3.4.
-/

noncomputable section

namespace Anabelian.LCFT

open OTriangle
open ValuativeRel

universe u

/-- The valuation of every natural-number cast is at most one. -/
theorem valuation_natCast_le_one {F Γ₀ : Type*} [Field F]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) (n : ℕ) :
    v (n : F) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ]
      exact (v.map_add _ _).trans (max_le ih (by simp))

/-- The residue characteristic lies in the maximal ideal of the valuation ring. -/
theorem residueChar_cast_valuation_lt_one
    (K : PointedMixedCharLocalField.{u}) :
    valuation K (K.residueChar : K) < 1 := by
  let A : ValuationSubring K := (valuation K).valuationSubring
  letI : CharP (IsLocalRing.ResidueField A) K.residueChar := by
    change CharP (IsLocalRing.ResidueField (valuation K).integer) K.residueChar
    infer_instance
  let pA : A := ⟨(K.residueChar : K), by
    rw [Valuation.mem_valuationSubring_iff]
    exact valuation_natCast_le_one (valuation K) K.residueChar⟩
  have hpA : pA ∈ IsLocalRing.maximalIdeal A := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change (K.residueChar : IsLocalRing.ResidueField A) = 0
    rw [CharP.cast_eq_zero_iff (IsLocalRing.ResidueField A) K.residueChar]
  simpa [A, pA] using
    (Valuation.mem_maximalIdeal_iff K (valuation K)).mp hpA

/-- Among prime casts, the residue characteristic has the smallest valuation. -/
theorem residueCharValuation_le_primeCastValuation
    (K : PointedMixedCharLocalField.{u}) (l : ℕ) (hl : l.Prime) :
    valuation K (K.residueChar : K) ≤ valuation K (l : K) := by
  by_cases h : l = K.residueChar
  · rw [h]
  have hlRes : (l : IsLocalRing.ResidueField (valuation K).integer) ≠ 0 := by
    intro hzero
    have hdiv : K.residueChar ∣ l :=
      (CharP.cast_eq_zero_iff
        (IsLocalRing.ResidueField (valuation K).integer)
        K.residueChar l).mp hzero
    rcases (Nat.dvd_prime hl).mp hdiv with hOne | heq
    · exact (Fact.out : K.residueChar.Prime).ne_one hOne
    · exact h heq.symm
  have hlval : valuation K (l : K) = 1 := by
    let lA : (valuation K).integer :=
      ⟨(l : K), valuation_natCast_le_one (valuation K) l⟩
    have hlUnit : IsUnit lA :=
      (IsLocalRing.residue_ne_zero_iff_isUnit lA).mp hlRes
    exact (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation K))).mp hlUnit
  rw [hlval]
  exact valuation_natCast_le_one (valuation K) K.residueChar

/-- Units closer to one than the residue characteristic form the deep principal-unit group. -/
def deepPrincipalUnitGroup (K : PointedMixedCharLocalField.{u}) : Subgroup Kˣ where
  carrier := {x | valuation K ((x : K) - 1) < valuation K (K.residueChar : K)}
  one_mem' := by
    change valuation K (((1 : Kˣ) : K) - 1) < valuation K (K.residueChar : K)
    simp only [Units.val_one, sub_self, map_zero]
    exact ((map_ne_zero (valuation K)).mpr
      (show (K.residueChar : K) ≠ 0 by exact_mod_cast
        (Fact.out : K.residueChar.Prime).ne_zero)).bot_lt
  mul_mem' := by
    intro a b ha hb
    change valuation K ((a : K) - 1) < valuation K (K.residueChar : K) at ha
    change valuation K ((b : K) - 1) < valuation K (K.residueChar : K) at hb
    change valuation K (((a * b : Kˣ) : K) - 1) < valuation K (K.residueChar : K)
    have hp := residueChar_cast_valuation_lt_one K
    have hva : valuation K (a : K) = 1 := by
      rw [show (a : K) = 1 + ((a : K) - 1) by ring]
      exact (valuation K).map_one_add_of_lt (ha.trans hp)
    rw [show ((a * b : Kˣ) : K) - 1 =
      (a : K) * ((b : K) - 1) + ((a : K) - 1) by
        simp only [Units.val_mul]
        ring]
    calc
      valuation K ((a : K) * ((b : K) - 1) + ((a : K) - 1)) ≤
          max (valuation K ((a : K) * ((b : K) - 1)))
            (valuation K ((a : K) - 1)) := (valuation K).map_add _ _
      _ = max (valuation K ((b : K) - 1)) (valuation K ((a : K) - 1)) := by
        rw [map_mul, hva, one_mul]
      _ < valuation K (K.residueChar : K) := max_lt hb ha
  inv_mem' := by
    intro a ha
    change valuation K ((a : K) - 1) < valuation K (K.residueChar : K) at ha
    change valuation K (((a⁻¹ : Kˣ) : K) - 1) < valuation K (K.residueChar : K)
    have hp := residueChar_cast_valuation_lt_one K
    have hva : valuation K (a : K) = 1 := by
      rw [show (a : K) = 1 + ((a : K) - 1) by ring]
      exact (valuation K).map_one_add_of_lt (ha.trans hp)
    rw [show (((a⁻¹ : Kˣ) : K) - 1) =
      -((a : K)⁻¹) * ((a : K) - 1) by
        rw [Units.val_inv_eq_inv_val]
        field_simp
        ring]
    rw [map_mul, (valuation K).map_neg, (valuation K).map_inv, hva, inv_one, one_mul]
    exact ha

/-- A deep principal unit whose prime power is one is itself one. -/
theorem deepPrincipalUnit_prime_pow_eq_one
    (K : PointedMixedCharLocalField.{u}) (l : ℕ) (hl : l.Prime)
    (x : deepPrincipalUnitGroup K) (hxpow : x ^ l = 1) : x = 1 := by
  let A : ValuationSubring K := (valuation K).valuationSubring
  have hp := residueChar_cast_valuation_lt_one K
  have hxa : valuation K (((x : Kˣ) : K) - 1) < 1 := x.property.trans hp
  have hxval : valuation K ((x : Kˣ) : K) = 1 := by
    rw [show ((x : Kˣ) : K) = 1 + (((x : Kˣ) : K) - 1) by ring]
    exact (valuation K).map_one_add_of_lt hxa
  let xA : A := ⟨((x : Kˣ) : K), by
    rw [Valuation.mem_valuationSubring_iff, hxval]⟩
  let a : A := xA - 1
  by_cases ha : a = 0
  · apply Subtype.ext
    apply Units.ext
    exact sub_eq_zero.mp (congrArg Subtype.val ha)
  let S : A := ∑ i ∈ Finset.range l, xA ^ i
  have hS : S = 0 := by
    have hgeom := geom_sum_mul xA l
    have hxpowA : xA ^ l = 1 := by
      apply Subtype.ext
      exact congrArg Units.val (congrArg Subtype.val hxpow)
    rw [hxpowA, sub_self] at hgeom
    have hmul : S * a = 0 := by simpa [S, a] using hgeom
    exact (mul_eq_zero.mp hmul).resolve_right ha
  have hlmem : (l : A) ∈ Ideal.span ({a} : Set A) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    let q := Ideal.Quotient.mk (Ideal.span ({a} : Set A))
    have hxmod : q xA = 1 := by
      rw [← sub_eq_zero]
      calc
        q xA - 1 = q (xA - 1) := by rw [map_sub, map_one]
        _ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.mem_span_singleton_self a)
    calc
      q (l : A) = ∑ _i ∈ Finset.range l,
          (1 : A ⧸ Ideal.span ({a} : Set A)) := by simp
      _ = ∑ i ∈ Finset.range l, (q xA) ^ i := by simp [hxmod]
      _ = q S := by simp [S]
      _ = 0 := by rw [hS, map_zero]
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hlmem
  have hqK : (l : K) = (((x : Kˣ) : K) - 1) * (q : K) := by
    exact congrArg Subtype.val hq
  have hqval : valuation K (q : K) ≤ 1 := q.property
  have hlle : valuation K (l : K) ≤ valuation K (((x : Kˣ) : K) - 1) := by
    rw [hqK, map_mul]
    simpa only [mul_one] using
      (mul_le_mul_left' hqval (valuation K (((x : Kˣ) : K) - 1)))
  exfalso
  exact (not_le_of_gt x.property)
    ((residueCharValuation_le_primeCastValuation K l hl).trans hlle)

/-- Every finite-order deep principal unit is one. -/
theorem deepPrincipalUnit_eq_one_of_isOfFinOrder
    (K : PointedMixedCharLocalField.{u})
    (x : deepPrincipalUnitGroup K) (hx : IsOfFinOrder x) : x = 1 := by
  have hn0 : orderOf x ≠ 0 := hx.orderOf_pos.ne'
  by_contra hxne
  have hn1 : orderOf x ≠ 1 := by
    intro h
    exact hxne (orderOf_eq_one_iff.mp h)
  let l := (orderOf x).minFac
  have hl : l.Prime := Nat.minFac_prime hn1
  have hldvd : l ∣ orderOf x := Nat.minFac_dvd (orderOf x)
  let y : deepPrincipalUnitGroup K := x ^ (orderOf x / l)
  have hyorder : orderOf y = l :=
    orderOf_pow_orderOf_div hn0 hldvd
  have hypow : y ^ l = 1 := by
    rw [← hyorder]
    exact pow_orderOf_eq_one y
  have hyone : y = 1 :=
    deepPrincipalUnit_prime_pow_eq_one K l hl y hypow
  have : l = 1 := by
    rw [← hyorder, hyone, orderOf_one]
  exact hl.ne_one this

instance deepPrincipalUnitGroup_isMulTorsionFree
    (K : PointedMixedCharLocalField.{u}) :
    IsMulTorsionFree (deepPrincipalUnitGroup K) :=
  IsMulTorsionFree.of_not_isOfFinOrder fun x hx hfin ↦
    hx (deepPrincipalUnit_eq_one_of_isOfFinOrder K x hfin)

end Anabelian.LCFT
