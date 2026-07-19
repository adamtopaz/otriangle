import Otriangle.MonoAnabelian.DeepUnits
import Mathlib.RingTheory.Henselian
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Deep residue-characteristic power roots

This module proves a uniform power-root estimate in a pointed mixed-characteristic local field.
Every valuation-ring element congruent to `1` modulo `p ^ 3` is a `p`th power, where `p` is the
residue characteristic.  The proof expands `(1 + p ^ 2 y) ^ p` and solves the remaining equation
by the contraction mapping theorem.
-/

noncomputable section

namespace Anabelian.LCFT

open OTriangle ValuativeRel

universe u

local instance (K : PointedMixedCharLocalField.{u}) : NontriviallyNormedField K :=
  K.nontriviallyNormedField

local instance (K : PointedMixedCharLocalField.{u}) : IsUltrametricDist K :=
  K.isUltrametricDist

local instance (K : PointedMixedCharLocalField.{u}) : CompleteSpace K :=
  K.completeSpace

/-- The higher-order correction in the expansion of `(1 + p ^ 2 y) ^ p`. -/
def deepRootCorrection (K : PointedMixedCharLocalField.{u})
    (y : (valuation K).integer) : (valuation K).integer :=
  ∑ k ∈ Finset.range (K.residueChar + 1),
    if 2 ≤ k then (K.residueChar.choose k : (valuation K).integer) *
      (K.residueChar : (valuation K).integer) ^ (2 * k - 3) * y ^ k else 0

/-- The binomial expansion separates a linear term from a correction divisible by `p`. -/
theorem deepRootCorrection_identity
    (K : PointedMixedCharLocalField.{u})
    (y : (valuation K).integer) :
    (1 + (K.residueChar : (valuation K).integer) ^ 2 * y) ^ K.residueChar =
      1 + (K.residueChar : (valuation K).integer) ^ 3 *
        (y + deepRootCorrection K y) := by
  rw [show 1 + (K.residueChar : (valuation K).integer) ^ 2 * y =
    (K.residueChar : (valuation K).integer) ^ 2 * y + 1 by ring, add_pow]
  simp only [deepRootCorrection]
  let pA : (valuation K).integer := K.residueChar
  let high : ℕ → (valuation K).integer := fun k ↦
    if 2 ≤ k then (K.residueChar.choose k : (valuation K).integer) *
      pA ^ (2 * k - 3) * y ^ k else 0
  calc
    ∑ m ∈ Finset.range (K.residueChar + 1),
        (pA ^ 2 * y) ^ m * 1 ^ (K.residueChar - m) *
          (K.residueChar.choose m : (valuation K).integer) =
      ∑ m ∈ Finset.range (K.residueChar + 1),
        if m = 0 then 1 else if m = 1 then pA ^ 3 * y else pA ^ 3 * high m := by
          apply Finset.sum_congr rfl
          intro m hm
          simp only [one_pow, mul_one]
          by_cases hm0 : m = 0
          · subst m
            simp
          by_cases hm1 : m = 1
          · subst m
            simp [pA, Nat.choose_one_right]
            ring
          have hm2 : 2 ≤ m := by omega
          simp only [hm0, hm1, if_false, high, if_pos hm2]
          rw [mul_pow, ← pow_mul]
          have hexp : 3 + (2 * m - 3) = 2 * m := by omega
          have heqpow : pA ^ (2 * m) = pA ^ 3 * pA ^ (2 * m - 3) := by
            rw [← pow_add, hexp]
          rw [heqpow]
          ring
    _ = 1 + pA ^ 3 *
        (y + ∑ k ∈ Finset.range (K.residueChar + 1), high k) := by
      have hdecomp :
          (∑ m ∈ Finset.range (K.residueChar + 1),
            if m = 0 then 1 else if m = 1 then pA ^ 3 * y else pA ^ 3 * high m) =
          (∑ m ∈ Finset.range (K.residueChar + 1), if m = 0 then 1 else 0) +
          (∑ m ∈ Finset.range (K.residueChar + 1),
            if m = 1 then pA ^ 3 * y else 0) +
          pA ^ 3 * (∑ m ∈ Finset.range (K.residueChar + 1), high m) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro m hm
        by_cases hm0 : m = 0
        · subst m
          simp [high]
        by_cases hm1 : m = 1
        · subst m
          simp [high]
        simp [hm0, hm1]
      rw [hdecomp]
      simp
      rw [if_pos (Fact.out : K.residueChar.Prime).pos]
      ring
    _ = _ := rfl

/-- Powers are nonexpanding on the valuation ring. -/
theorem integer_norm_pow_sub_pow_le
    (K : PointedMixedCharLocalField.{u})
    (x y : (valuation K).integer) (n : ℕ) :
    ‖((x ^ n - y ^ n : (valuation K).integer) : K)‖ ≤
      ‖((x - y : (valuation K).integer) : K)‖ := by
  obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow x y n
  have hqK := congrArg (fun z : (valuation K).integer ↦ (z : K)) hq
  rw [hqK]
  change ‖(((x - y : (valuation K).integer) : K) * (q : K))‖ ≤
    ‖((x - y : (valuation K).integer) : K)‖
  rw [norm_mul]
  have hqnorm : ‖(q : K)‖ ≤ 1 := by
    rw [← norm_one (α := K)]
    apply (K.norm_le_norm_iff_vle (q : K) 1).mpr
    apply (valuation K).vle_one_iff.mpr
    exact (Valuation.mem_integer_iff (valuation K) (q : K)).mp q.property
  exact mul_le_of_le_one_right (norm_nonneg _) hqnorm

/-- Every valuation-ring element has norm at most one. -/
theorem integer_norm_le_one
    (K : PointedMixedCharLocalField.{u})
    (x : (valuation K).integer) :
    ‖(x : K)‖ ≤ 1 := by
  rw [← norm_one (α := K)]
  apply (K.norm_le_norm_iff_vle (x : K) 1).mpr
  apply (valuation K).vle_one_iff.mpr
  exact (Valuation.mem_integer_iff (valuation K) (x : K)).mp x.property

/-- The residue characteristic is strictly topologically nilpotent. -/
theorem residueChar_norm_lt_one
    (K : PointedMixedCharLocalField.{u}) :
    ‖(K.residueChar : K)‖ < 1 := by
  rw [← norm_one (α := K)]
  apply lt_of_not_ge
  intro h
  have hvle : (1 : K) ≤ᵥ (K.residueChar : K) :=
    (K.norm_le_norm_iff_vle 1 (K.residueChar : K)).mp h
  have hv : 1 ≤ valuation K (K.residueChar : K) :=
    (valuation K).one_vle_iff.mp hvle
  exact (not_le_of_gt (residueChar_cast_valuation_lt_one K)) hv

/-- The higher-order correction is Lipschitz with constant `|p| < 1`. -/
theorem deepRootCorrection_sub_norm_le
    (K : PointedMixedCharLocalField.{u})
    (x y : (valuation K).integer) :
    ‖deepRootCorrection K x - deepRootCorrection K y‖ ≤
      ‖(K.residueChar : (valuation K).integer)‖ * ‖x - y‖ := by
  simp only [deepRootCorrection, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_
  intro k hk
  by_cases hk2 : 2 ≤ k
  · simp only [if_pos hk2]
    have hexp : 2 * k - 3 = (2 * k - 4) + 1 := by omega
    have hfactor :
        (K.residueChar.choose k : (valuation K).integer) *
              (K.residueChar : (valuation K).integer) ^ (2 * k - 3) * x ^ k -
            (K.residueChar.choose k : (valuation K).integer) *
              (K.residueChar : (valuation K).integer) ^ (2 * k - 3) * y ^ k =
          (K.residueChar : (valuation K).integer) *
            ((K.residueChar.choose k : (valuation K).integer) *
              (K.residueChar : (valuation K).integer) ^ (2 * k - 4)) *
            (x ^ k - y ^ k) := by
      rw [hexp, pow_succ]
      ring
    rw [hfactor]
    rw [norm_mul, norm_mul]
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_
      (norm_nonneg (K.residueChar : (valuation K).integer))
    refine (mul_le_of_le_one_left (norm_nonneg _)
      (by simpa using (integer_norm_le_one K
        ((K.residueChar.choose k : (valuation K).integer) *
          (K.residueChar : (valuation K).integer) ^ (2 * k - 4))))).trans ?_
    simpa using integer_norm_pow_sub_pow_le K x y k
  · simpa [hk2] using
      mul_nonneg (norm_nonneg (K.residueChar : (valuation K).integer))
        (norm_nonneg (x - y))

/-- The contraction whose fixed point supplies a deep `p`th root. -/
def deepRootMap (K : PointedMixedCharLocalField.{u})
    (a y : (valuation K).integer) : (valuation K).integer :=
  a - deepRootCorrection K y

theorem deepRootMap_contracting
    (K : PointedMixedCharLocalField.{u})
    (a : (valuation K).integer) :
    ContractingWith ‖(K.residueChar : (valuation K).integer)‖₊
      (deepRootMap K a) := by
  constructor
  · apply NNReal.coe_lt_one.mp
    change ‖(K.residueChar : (valuation K).integer)‖ < 1
    simpa using residueChar_norm_lt_one K
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [deepRootMap, dist_eq_norm]
    have hsub :
        (a - deepRootCorrection K x) - (a - deepRootCorrection K y) =
          -(deepRootCorrection K x - deepRootCorrection K y) := by
      abel
    rw [hsub, norm_neg]
    change ‖deepRootCorrection K x - deepRootCorrection K y‖ ≤
      ‖(K.residueChar : (valuation K).integer)‖ * ‖x - y‖
    exact deepRootCorrection_sub_norm_le K x y

/-- The correction equation `y + H(y) = a` has a solution in the valuation ring. -/
theorem exists_deepRootSolution
    (K : PointedMixedCharLocalField.{u})
    (a : (valuation K).integer) :
    ∃ y : (valuation K).integer, y + deepRootCorrection K y = a := by
  have hf := deepRootMap_contracting K a
  obtain ⟨y, hy, -, -⟩ := hf.exists_fixedPoint 0 (edist_ne_top _ _)
  refine ⟨y, ?_⟩
  change a - deepRootCorrection K y = y at hy
  exact ((sub_eq_iff_eq_add).mp hy).symm

/-- Every element of `1 + p ^ 3 𝒪_K` is a `p`th power in the valuation ring. -/
theorem one_add_residueChar_cube_is_pow
    (K : PointedMixedCharLocalField.{u})
    (a : (valuation K).integer) :
    ∃ z : (valuation K).integer,
      z ^ K.residueChar =
        1 + (K.residueChar : (valuation K).integer) ^ 3 * a := by
  obtain ⟨y, hy⟩ := exists_deepRootSolution K a
  refine ⟨1 + (K.residueChar : (valuation K).integer) ^ 2 * y, ?_⟩
  rw [deepRootCorrection_identity]
  rw [hy]

/-- A strengthened form of `one_add_residueChar_cube_is_pow` which records that the chosen root
is itself congruent to one modulo `p²`. -/
theorem one_add_residueChar_cube_is_pow_of_one_add_square
    (K : PointedMixedCharLocalField.{u})
    (a : (valuation K).integer) :
    ∃ y : (valuation K).integer,
      (1 + (K.residueChar : (valuation K).integer) ^ 2 * y) ^ K.residueChar =
        1 + (K.residueChar : (valuation K).integer) ^ 3 * a := by
  obtain ⟨y, hy⟩ := exists_deepRootSolution K a
  refine ⟨y, ?_⟩
  rw [deepRootCorrection_identity, hy]

end Anabelian.LCFT
