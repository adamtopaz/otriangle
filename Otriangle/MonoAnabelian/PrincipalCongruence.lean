import Otriangle.MonoAnabelian.LocalArithmeticInvariants
import Otriangle.MonoAnabelian.DeepPowerRoots

/-!
# Principal congruence quotients in residue characteristic

Write `p` for the residue characteristic and `A = O_K`.  The kernel of
`A× → (A / p^n A)×` is the principal congruence group `U[p^n]`.  On `U[p²]`, division
of `u - 1` by `p²`, followed by reduction modulo `p`, is a homomorphism

`U[p²] → A / pA`.

Its kernel is `U[p³]` and it is onto.  The `p`th-power map carries `U[p²]` exactly onto
`U[p³]`; this is the elementary deep-unit substitute for the local logarithm in Hoshi's
calculation of the residue-characteristic rank.
-/

noncomputable section

namespace Anabelian.LCFT

open OTriangle ValuativeRel

universe u

/-- The ideal `p^n O_K`. -/
def residueCharPowerIdeal (K : PointedMixedCharLocalField.{u}) (n : ℕ) :
    Ideal (LocalIntegerRing K) :=
  residueCharIdeal K ^ n

/-- Reduction of valuation-ring units modulo `p^n`. -/
def integerUnitReduction (K : PointedMixedCharLocalField.{u}) (n : ℕ) :
    (LocalIntegerRing K)ˣ →* (LocalIntegerRing K ⧸ residueCharPowerIdeal K n)ˣ :=
  Units.map (Ideal.Quotient.mk (residueCharPowerIdeal K n))

/-- The principal congruence group `1 + p^n O_K`. -/
def residueCharPrincipalCongruenceGroup
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) :
    Subgroup (LocalIntegerRing K)ˣ :=
  (integerUnitReduction K n).ker

theorem mem_residueCharPrincipalCongruenceGroup_iff
    (K : PointedMixedCharLocalField.{u}) (n : ℕ)
    (u : (LocalIntegerRing K)ˣ) :
    u ∈ residueCharPrincipalCongruenceGroup K n ↔
      (u : LocalIntegerRing K) - 1 ∈ residueCharPowerIdeal K n := by
  rw [residueCharPrincipalCongruenceGroup, MonoidHom.mem_ker]
  rw [Units.ext_iff]
  change Ideal.Quotient.mk (residueCharPowerIdeal K n)
      (u : LocalIntegerRing K) = 1 ↔ _
  rw [← map_one (Ideal.Quotient.mk (residueCharPowerIdeal K n)),
    ← sub_eq_zero, ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem

theorem residueCharPowerIdeal_eq_span_pow
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) :
    residueCharPowerIdeal K n =
      Ideal.span {(residueCharInteger K) ^ n} := by
  rw [residueCharPowerIdeal, residueCharIdeal]
  exact Ideal.span_singleton_pow (residueCharInteger K) n

/-- A principal-congruence unit has a coefficient after dividing `u - 1` by `p^n`. -/
def principalCongruenceCoefficient
    (K : PointedMixedCharLocalField.{u}) (n : ℕ)
    (u : residueCharPrincipalCongruenceGroup K n) :
    LocalIntegerRing K := by
  have hu : (u.1 : LocalIntegerRing K) - 1 ∈
      Ideal.span {(residueCharInteger K) ^ n} := by
    rw [← residueCharPowerIdeal_eq_span_pow]
    exact (mem_residueCharPrincipalCongruenceGroup_iff K n u.1).mp u.2
  exact (Ideal.mem_span_singleton.mp hu).choose

theorem residueCharInteger_pow_mul_principalCongruenceCoefficient
    (K : PointedMixedCharLocalField.{u}) (n : ℕ)
    (u : residueCharPrincipalCongruenceGroup K n) :
    (residueCharInteger K) ^ n * principalCongruenceCoefficient K n u =
      (u.1 : LocalIntegerRing K) - 1 := by
  have hu : (u.1 : LocalIntegerRing K) - 1 ∈
      Ideal.span {(residueCharInteger K) ^ n} := by
    rw [← residueCharPowerIdeal_eq_span_pow]
    exact (mem_residueCharPrincipalCongruenceGroup_iff K n u.1).mp u.2
  exact (Ideal.mem_span_singleton.mp hu).choose_spec.symm

theorem principalCongruenceUnit_eq_one_add
    (K : PointedMixedCharLocalField.{u}) (n : ℕ)
    (u : residueCharPrincipalCongruenceGroup K n) :
    (u.1 : LocalIntegerRing K) = 1 +
      (residueCharInteger K) ^ n * principalCongruenceCoefficient K n u := by
  rw [residueCharInteger_pow_mul_principalCongruenceCoefficient]
  ring

/-- The normalized coefficient of a `1 + p²` unit, reduced modulo `p`. -/
def squarePrincipalCoefficientMod
    (K : PointedMixedCharLocalField.{u}) :
    residueCharPrincipalCongruenceGroup K 2 →*
      Multiplicative (LocalIntegerRing K ⧸ residueCharIdeal K) where
  toFun u := Multiplicative.ofAdd <|
    Ideal.Quotient.mk (residueCharIdeal K)
      (principalCongruenceCoefficient K 2 u)
  map_one' := by
    apply Multiplicative.toAdd.injective
    change Ideal.Quotient.mk (residueCharIdeal K)
        (principalCongruenceCoefficient K 2
          (1 : residueCharPrincipalCongruenceGroup K 2)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have h := residueCharInteger_pow_mul_principalCongruenceCoefficient K 2
      (1 : residueCharPrincipalCongruenceGroup K 2)
    have hp0 : (residueCharInteger K) ^ 2 ≠ 0 :=
      pow_ne_zero _ (residueCharInteger_ne_zero K)
    have hc : principalCongruenceCoefficient K 2
        (1 : residueCharPrincipalCongruenceGroup K 2) = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left hp0
      simpa using h
    rw [hc]
    exact (residueCharIdeal K).zero_mem
  map_mul' := by
    intro x y
    apply Multiplicative.toAdd.injective
    change Ideal.Quotient.mk (residueCharIdeal K)
        (principalCongruenceCoefficient K 2 (x * y)) =
      Ideal.Quotient.mk (residueCharIdeal K)
        (principalCongruenceCoefficient K 2 x) +
      Ideal.Quotient.mk (residueCharIdeal K)
        (principalCongruenceCoefficient K 2 y)
    rw [← map_add]
    apply (Submodule.Quotient.eq (residueCharIdeal K)).mpr
    change principalCongruenceCoefficient K 2 (x * y) -
        (principalCongruenceCoefficient K 2 x +
          principalCongruenceCoefficient K 2 y) ∈ residueCharIdeal K
    let p : LocalIntegerRing K := residueCharInteger K
    let a := principalCongruenceCoefficient K 2 x
    let b := principalCongruenceCoefficient K 2 y
    let c := principalCongruenceCoefficient K 2 (x * y)
    have hp0 : p ^ 2 ≠ 0 := pow_ne_zero _ (residueCharInteger_ne_zero K)
    have hxy : p ^ 2 * c = p ^ 2 * (a + b + p ^ 2 * (a * b)) := by
      have hx := principalCongruenceUnit_eq_one_add K 2 x
      have hy := principalCongruenceUnit_eq_one_add K 2 y
      have hxy' := principalCongruenceUnit_eq_one_add K 2 (x * y)
      change ((x.1 * y.1 : (LocalIntegerRing K)ˣ) : LocalIntegerRing K) =
          1 + p ^ 2 * c at hxy'
      change (x.1 : LocalIntegerRing K) = 1 + p ^ 2 * a at hx
      change (y.1 : LocalIntegerRing K) = 1 + p ^ 2 * b at hy
      rw [Units.val_mul, hx, hy] at hxy'
      apply add_left_cancel (a := (1 : LocalIntegerRing K))
      rw [← hxy']
      ring
    have hc : c = a + b + p ^ 2 * (a * b) :=
      mul_left_cancel₀ hp0 hxy
    change c - (a + b) ∈ residueCharIdeal K
    rw [hc]
    have heq : a + b + p ^ 2 * (a * b) - (a + b) =
        p ^ 2 * (a * b) := by ring
    rw [heq]
    change p ^ 2 * (a * b) ∈ Ideal.span
      ({p} : Set (LocalIntegerRing K))
    exact Ideal.mem_span_singleton.mpr ⟨p * (a * b), by ring⟩

theorem squarePrincipalCoefficientMod_surjective
    (K : PointedMixedCharLocalField.{u}) :
    Function.Surjective (squarePrincipalCoefficientMod K) := by
  intro q
  let qadd : LocalIntegerRing K ⧸ residueCharIdeal K := q.toAdd
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective qadd
  let p : LocalIntegerRing K := residueCharInteger K
  let zA : LocalIntegerRing K := 1 + p ^ 2 * a
  have hzunit : IsUnit zA := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit zA).mp
    have hpzero : IsLocalRing.residue (LocalIntegerRing K) p = 0 := by
      change (K.residueChar : LocalResidueField K) = 0
      rw [CharP.cast_eq_zero_iff (LocalResidueField K) K.residueChar]
    simp only [zA, map_add, map_mul, map_pow, map_one, hpzero,
      zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, add_zero]
    exact one_ne_zero
  let z : (LocalIntegerRing K)ˣ := hzunit.unit
  have hzval : (z : LocalIntegerRing K) = zA := hzunit.unit_spec
  have hzmem : z ∈ residueCharPrincipalCongruenceGroup K 2 := by
    rw [mem_residueCharPrincipalCongruenceGroup_iff,
      residueCharPowerIdeal_eq_span_pow]
    rw [hzval]
    change zA - 1 ∈ Ideal.span ({p ^ 2} : Set (LocalIntegerRing K))
    rw [show zA - 1 = p ^ 2 * a by simp [zA]]
    exact Ideal.mem_span_singleton.mpr ⟨a, rfl⟩
  let zu : residueCharPrincipalCongruenceGroup K 2 := ⟨z, hzmem⟩
  refine ⟨zu, ?_⟩
  apply Multiplicative.toAdd.injective
  change Ideal.Quotient.mk (residueCharIdeal K)
      (principalCongruenceCoefficient K 2 zu) = qadd
  rw [← ha]
  have hp2 : p ^ 2 ≠ 0 := pow_ne_zero _ (residueCharInteger_ne_zero K)
  have hcoef := residueCharInteger_pow_mul_principalCongruenceCoefficient K 2 zu
  have hza : p ^ 2 * a = (zu.1 : LocalIntegerRing K) - 1 := by
    rw [hzval]
    simp [zA]
  have hc : principalCongruenceCoefficient K 2 zu = a := by
    apply mul_left_cancel₀ hp2
    exact hcoef.trans hza.symm
  rw [hc]

/-- Vanishing of the normalized square coefficient is exactly congruence modulo `p³`. -/
theorem squarePrincipalCoefficientMod_eq_one_iff
    (K : PointedMixedCharLocalField.{u})
    (u : residueCharPrincipalCongruenceGroup K 2) :
    squarePrincipalCoefficientMod K u = 1 ↔
      u.1 ∈ residueCharPrincipalCongruenceGroup K 3 := by
  let p : LocalIntegerRing K := residueCharInteger K
  let c := principalCongruenceCoefficient K 2 u
  have hp2 : p ^ 2 ≠ 0 := pow_ne_zero _ (residueCharInteger_ne_zero K)
  rw [mem_residueCharPrincipalCongruenceGroup_iff]
  change Ideal.Quotient.mk (residueCharIdeal K) c = 0 ↔
    (u.1 : LocalIntegerRing K) - 1 ∈
      residueCharPowerIdeal K 3
  rw [Ideal.Quotient.eq_zero_iff_mem]
  rw [residueCharPowerIdeal_eq_span_pow]
  constructor
  · intro hc
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hc
    have hu := residueCharInteger_pow_mul_principalCongruenceCoefficient K 2 u
    rw [← hu]
    apply Ideal.mem_span_singleton.mpr
    refine ⟨d, ?_⟩
    change p ^ 2 * c = p ^ 3 * d
    rw [hd]
    ring
  · intro hu
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hu
    apply Ideal.mem_span_singleton.mpr
    refine ⟨d, ?_⟩
    have hcEq := residueCharInteger_pow_mul_principalCongruenceCoefficient K 2 u
    change c = p * d
    apply mul_left_cancel₀ hp2
    rw [hcEq, hd]
    ring

/-- Higher `p`-power congruence groups are contained in lower ones. -/
theorem residueCharPrincipalCongruenceGroup_mono
    (K : PointedMixedCharLocalField.{u}) {m n : ℕ} (h : m ≤ n) :
    residueCharPrincipalCongruenceGroup K n ≤
      residueCharPrincipalCongruenceGroup K m := by
  intro u hu
  rw [mem_residueCharPrincipalCongruenceGroup_iff] at hu ⊢
  exact (Ideal.pow_le_pow_right h) hu

/-- The cube congruence group, regarded inside the square congruence group. -/
def cubePrincipalInsideSquare (K : PointedMixedCharLocalField.{u}) :
    Subgroup (residueCharPrincipalCongruenceGroup K 2) :=
  (residueCharPrincipalCongruenceGroup K 3).comap
    (residueCharPrincipalCongruenceGroup K 2).subtype

theorem squarePrincipalCoefficientMod_ker
    (K : PointedMixedCharLocalField.{u}) :
    (squarePrincipalCoefficientMod K).ker = cubePrincipalInsideSquare K := by
  ext u
  rw [MonoidHom.mem_ker]
  exact squarePrincipalCoefficientMod_eq_one_iff K u

/-- Raising a `1 + p²` unit to the `p`th power gives a `1 + p³` unit. -/
theorem squarePrincipal_pow_mem_cube
    (K : PointedMixedCharLocalField.{u})
    (u : residueCharPrincipalCongruenceGroup K 2) :
    u ^ K.residueChar ∈ cubePrincipalInsideSquare K := by
  change (u.1 ^ K.residueChar : (LocalIntegerRing K)ˣ) ∈
    residueCharPrincipalCongruenceGroup K 3
  rw [mem_residueCharPrincipalCongruenceGroup_iff]
  rw [residueCharPowerIdeal_eq_span_pow]
  let p : LocalIntegerRing K := residueCharInteger K
  let a := principalCongruenceCoefficient K 2 u
  have hu := principalCongruenceUnit_eq_one_add K 2 u
  change ((u.1 ^ K.residueChar : (LocalIntegerRing K)ˣ) :
      LocalIntegerRing K) - 1 ∈ Ideal.span ({p ^ 3} : Set (LocalIntegerRing K))
  rw [Units.val_pow_eq_pow_val, hu]
  have hid := deepRootCorrection_identity K a
  change (1 + p ^ 2 * a) ^ K.residueChar =
      1 + p ^ 3 * (a + deepRootCorrection K a) at hid
  rw [hid]
  apply Ideal.mem_span_singleton.mpr
  refine ⟨a + deepRootCorrection K a, by ring⟩

/-- Every `1 + p³` unit is the `p`th power of a `1 + p²` unit. -/
theorem exists_squarePrincipal_pow_eq_of_mem_cube
    (K : PointedMixedCharLocalField.{u})
    (u : residueCharPrincipalCongruenceGroup K 2)
    (hu : u ∈ cubePrincipalInsideSquare K) :
    ∃ z : residueCharPrincipalCongruenceGroup K 2,
      z ^ K.residueChar = u := by
  have hu3 : u.1 ∈ residueCharPrincipalCongruenceGroup K 3 := hu
  let p : LocalIntegerRing K := residueCharInteger K
  let a := principalCongruenceCoefficient K 3 ⟨u.1, hu3⟩
  have hueq := principalCongruenceUnit_eq_one_add K 3 ⟨u.1, hu3⟩
  change (u.1 : LocalIntegerRing K) = 1 + p ^ 3 * a at hueq
  obtain ⟨y, hy⟩ := one_add_residueChar_cube_is_pow_of_one_add_square K a
  change (1 + p ^ 2 * y) ^ K.residueChar = 1 + p ^ 3 * a at hy
  let zA : LocalIntegerRing K := 1 + p ^ 2 * y
  have hzpow : zA ^ K.residueChar = (u.1 : LocalIntegerRing K) := by
    rw [hueq]
    exact hy
  have hzunit : IsUnit zA := by
    rw [← isUnit_pow_iff (Fact.out : K.residueChar.Prime).ne_zero]
    rw [hzpow]
    exact Units.isUnit u.1
  let z : (LocalIntegerRing K)ˣ := hzunit.unit
  have hzval : (z : LocalIntegerRing K) = zA := hzunit.unit_spec
  have hzmem : z ∈ residueCharPrincipalCongruenceGroup K 2 := by
    rw [mem_residueCharPrincipalCongruenceGroup_iff,
      residueCharPowerIdeal_eq_span_pow]
    change (z : LocalIntegerRing K) - 1 ∈
      Ideal.span ({p ^ 2} : Set (LocalIntegerRing K))
    rw [hzval]
    apply Ideal.mem_span_singleton.mpr
    refine ⟨y, by simp [zA]⟩
  refine ⟨⟨z, hzmem⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  change (z : LocalIntegerRing K) ^ K.residueChar =
    (u.1 : LocalIntegerRing K)
  rw [hzval]
  exact hzpow

/-- On the square principal-congruence group, the range of the `p`th-power map is exactly the
cube congruence subgroup. -/
theorem squarePrincipal_pow_range
    (K : PointedMixedCharLocalField.{u}) :
    (powMonoidHom
      (α := residueCharPrincipalCongruenceGroup K 2)
      K.residueChar).range = cubePrincipalInsideSquare K := by
  ext u
  constructor
  · rintro ⟨z, rfl⟩
    exact squarePrincipal_pow_mem_cube K z
  · intro hu
    obtain ⟨z, hz⟩ := exists_squarePrincipal_pow_eq_of_mem_cube K u hu
    exact ⟨z, hz⟩

/-- The exact size of the deep-unit quotient by residue-characteristic powers.  This is the
factor `p^(e f)` in the local multiplicative-rank calculation. -/
theorem squarePrincipalModPowerQuotient_card
    (K : PointedMixedCharLocalField.{u}) :
    Nat.card
        (residueCharPrincipalCongruenceGroup K 2 ⧸
          (powMonoidHom
            (α := residueCharPrincipalCongruenceGroup K 2)
            K.residueChar).range) =
      K.residueChar ^
        (absoluteRamificationIndex K * localResidueDegree K) := by
  let f := squarePrincipalCoefficientMod K
  have hf : Function.Surjective f :=
    squarePrincipalCoefficientMod_surjective K
  calc
    Nat.card
        (residueCharPrincipalCongruenceGroup K 2 ⧸
          (powMonoidHom
            (α := residueCharPrincipalCongruenceGroup K 2)
            K.residueChar).range) =
        Nat.card
          (residueCharPrincipalCongruenceGroup K 2 ⧸ f.ker) := by
            rw [squarePrincipal_pow_range, squarePrincipalCoefficientMod_ker]
    _ = Nat.card
          (Multiplicative (LocalIntegerRing K ⧸ residueCharIdeal K)) :=
      Nat.card_congr
        (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
    _ = Nat.card (LocalIntegerRing K ⧸ residueCharIdeal K) :=
      Nat.card_congr Multiplicative.toAdd
    _ = K.residueChar ^
          (absoluteRamificationIndex K * localResidueDegree K) :=
      residueCharIdeal_quotient_card K

end Anabelian.LCFT
