import Otriangle.MonoAnabelian.ResidueCharacteristicRank

/-!
# Finiteness of the residue-characteristic power quotient

A sufficiently deep open subgroup of the valuation-ring units consists of residue-characteristic
powers.  The unit power quotient is therefore finite.  Combining it with a uniformizer exponent
modulo the residue characteristic gives a finite parameter space for the full multiplicative
power quotient and hence for its torsion-free quotient.
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

def cubeDeepPrincipalUnitGroup
    (K : PointedMixedCharLocalField.{u}) : Subgroup Kˣ where
  carrier := {x | valuation K ((x : K) - 1) <
    valuation K ((K.residueChar : K) ^ 3)}
  one_mem' := by
    change valuation K (((1 : Kˣ) : K) - 1) <
      valuation K ((K.residueChar : K) ^ 3)
    simp only [Units.val_one, sub_self, map_zero]
    exact ((map_ne_zero (valuation K)).mpr
      (pow_ne_zero 3 (show (K.residueChar : K) ≠ 0 by exact_mod_cast
        (Fact.out : K.residueChar.Prime).ne_zero))).bot_lt
  mul_mem' := by
    intro a b ha hb
    change valuation K ((a : K) - 1) <
      valuation K ((K.residueChar : K) ^ 3) at ha
    change valuation K ((b : K) - 1) <
      valuation K ((K.residueChar : K) ^ 3) at hb
    change valuation K (((a * b : Kˣ) : K) - 1) <
      valuation K ((K.residueChar : K) ^ 3)
    have hpCube : valuation K ((K.residueChar : K) ^ 3) < 1 := by
      rw [map_pow]
      exact pow_lt_one₀ bot_le (residueChar_cast_valuation_lt_one K) (by decide)
    have hva : valuation K (a : K) = 1 := by
      rw [show (a : K) = 1 + ((a : K) - 1) by ring]
      exact (valuation K).map_one_add_of_lt (ha.trans hpCube)
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
      _ < valuation K ((K.residueChar : K) ^ 3) := max_lt hb ha
  inv_mem' := by
    intro a ha
    change valuation K ((a : K) - 1) <
      valuation K ((K.residueChar : K) ^ 3) at ha
    change valuation K (((a⁻¹ : Kˣ) : K) - 1) <
      valuation K ((K.residueChar : K) ^ 3)
    have hpCube : valuation K ((K.residueChar : K) ^ 3) < 1 := by
      rw [map_pow]
      exact pow_lt_one₀ bot_le (residueChar_cast_valuation_lt_one K) (by decide)
    have hva : valuation K (a : K) = 1 := by
      rw [show (a : K) = 1 + ((a : K) - 1) by ring]
      exact (valuation K).map_one_add_of_lt (ha.trans hpCube)
    rw [show (((a⁻¹ : Kˣ) : K) - 1) =
      -((a : K)⁻¹) * ((a : K) - 1) by
        rw [Units.val_inv_eq_inv_val]
        field_simp
        ring]
    rw [map_mul, (valuation K).map_neg, (valuation K).map_inv, hva,
      inv_one, one_mul]
    exact ha

def cubeDeepIntegerUnitGroup
    (K : PointedMixedCharLocalField.{u}) :
    Subgroup (valuation K).integerˣ :=
  (cubeDeepPrincipalUnitGroup K).comap (integerRingUnitsToFieldUnits K)

theorem cubeDeepIntegerUnitGroup_isOpen
    (K : PointedMixedCharLocalField.{u}) :
    IsOpen (cubeDeepIntegerUnitGroup K : Set (valuation K).integerˣ) := by
  change IsOpen {x : (valuation K).integerˣ |
    valuation K ((((x : (valuation K).integer) : K)) - 1) <
      valuation K ((K.residueChar : K) ^ 3)}
  have hopen : IsOpen {z : K |
      valuation K z < valuation K ((K.residueChar : K) ^ 3)} := by
    simpa only [Valuation.restrict_lt_iff_lt_embedding,
      Valuation.embedding_restrict] using
      (Valuation.isOpen_ball
        ((valuation K).restrict ((K.residueChar : K) ^ 3)))
  exact hopen.preimage (by fun_prop)

theorem cubeDeepIntegerUnitGroup_quotient_finite
    (K : PointedMixedCharLocalField.{u}) :
    Finite ((valuation K).integerˣ ⧸ cubeDeepIntegerUnitGroup K) := by
  let A := (valuation K).integer
  haveI : CompactSpace A := by
    change CompactSpace 𝒪[K]
    infer_instance
  exact Subgroup.quotient_finite_of_isOpen _
    (cubeDeepIntegerUnitGroup_isOpen K)

theorem cubeDeepIntegerUnitGroup_le_powRange
    (K : PointedMixedCharLocalField.{u}) :
    cubeDeepIntegerUnitGroup K ≤
      (powMonoidHom (α := (valuation K).integerˣ) K.residueChar).range := by
  intro x hx
  change valuation K ((((x : (valuation K).integer) : K)) - 1) <
    valuation K ((K.residueChar : K) ^ 3) at hx
  have hpne : (K.residueChar : K) ^ 3 ≠ 0 :=
    pow_ne_zero 3 (by exact_mod_cast (Fact.out : K.residueChar.Prime).ne_zero)
  let a : (valuation K).integer :=
    ⟨(((x : (valuation K).integer) : K) - 1) /
      (K.residueChar : K) ^ 3, by
        rw [Valuation.mem_integer_iff, (valuation K).map_div]
        apply (div_le_one₀ ((map_ne_zero (valuation K)).mpr hpne).bot_lt).mpr
        exact hx.le⟩
  have hxa :
      1 + (K.residueChar : (valuation K).integer) ^ 3 * a =
        (x : (valuation K).integer) := by
    apply Subtype.ext
    change 1 + (K.residueChar : K) ^ 3 *
      ((((x : (valuation K).integer) : K) - 1) /
        (K.residueChar : K) ^ 3) = ((x : (valuation K).integer) : K)
    field_simp [show (K.residueChar : K) ≠ 0 by
      exact_mod_cast (Fact.out : K.residueChar.Prime).ne_zero]
    ring
  obtain ⟨z, hz⟩ := one_add_residueChar_cube_is_pow K a
  have hzpow : z ^ K.residueChar = (x : (valuation K).integer) := hz.trans hxa
  have hzunit : IsUnit z := by
    rw [← isUnit_pow_iff (Fact.out : K.residueChar.Prime).ne_zero]
    rw [hzpow]
    exact Units.isUnit x
  let zu : (valuation K).integerˣ := hzunit.unit
  refine ⟨zu, ?_⟩
  apply Units.ext
  change z ^ K.residueChar = (x : (valuation K).integer)
  exact hzpow

theorem integerUnitsModPower_finite
    (K : PointedMixedCharLocalField.{u}) :
    Finite ((valuation K).integerˣ ⧸
      (powMonoidHom (α := (valuation K).integerˣ) K.residueChar).range) := by
  let H := cubeDeepIntegerUnitGroup K
  let P := (powMonoidHom (α := (valuation K).integerˣ) K.residueChar).range
  let f : ((valuation K).integerˣ ⧸ H) →*
      ((valuation K).integerˣ ⧸ P) :=
    QuotientGroup.map H P (MonoidHom.id _) (by
      simpa only [Subgroup.comap_id] using
        cubeDeepIntegerUnitGroup_le_powRange K)
  haveI : Finite ((valuation K).integerˣ ⧸ H) :=
    cubeDeepIntegerUnitGroup_quotient_finite K
  apply Finite.of_surjective f
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective P q
  exact ⟨(x : (valuation K).integerˣ ⧸ H), rfl⟩

abbrev FieldModPowerQuotient
    (K : PointedMixedCharLocalField.{u}) :=
  Kˣ ⧸ (powMonoidHom (α := Kˣ) K.residueChar).range

noncomputable def integerUnitModPowerToFieldModPower
    (K : PointedMixedCharLocalField.{u}) :
    ((valuation K).integerˣ ⧸
      (powMonoidHom (α := (valuation K).integerˣ) K.residueChar).range) →*
      FieldModPowerQuotient K :=
  QuotientGroup.lift
    (powMonoidHom (α := (valuation K).integerˣ) K.residueChar).range
    ((QuotientGroup.mk'
      (powMonoidHom (α := Kˣ) K.residueChar).range).comp
        (integerUnitsToFieldUnits K)) (by
      intro x hx
      obtain ⟨y, rfl⟩ := hx
      rw [MonoidHom.mem_ker]
      change ((integerUnitsToFieldUnits K (y ^ K.residueChar) : Kˣ) :
        FieldModPowerQuotient K) = 1
      rw [map_pow]
      rw [QuotientGroup.eq_one_iff]
      exact ⟨integerUnitsToFieldUnits K y, rfl⟩)

noncomputable def fieldModPowerParam
    (K : PointedMixedCharLocalField.{u}) :
    Fin K.residueChar ×
      ((valuation K).integerˣ ⧸
        (powMonoidHom (α := (valuation K).integerˣ) K.residueChar).range) →
      FieldModPowerQuotient K :=
  fun rq ↦
    ((uniformizerUnit K : FieldModPowerQuotient K) ^ (rq.1 : ℕ)) *
      integerUnitModPowerToFieldModPower K rq.2

theorem uniformizer_zpow_eq_emod
    (K : PointedMixedCharLocalField.{u}) (z : ℤ) :
    (((uniformizerUnit K) ^ z : Kˣ) : FieldModPowerQuotient K) =
      (((uniformizerUnit K) ^ (Int.toNat (z % K.residueChar)) : Kˣ) :
        FieldModPowerQuotient K) := by
  have hpZ : (0 : ℤ) < K.residueChar := by
    exact_mod_cast (Fact.out : K.residueChar.Prime).pos
  have hrnonneg : 0 ≤ z % (K.residueChar : ℤ) :=
    Int.emod_nonneg z hpZ.ne'
  have hz : z - (Int.toNat (z % K.residueChar) : ℤ) =
      (z / K.residueChar) * K.residueChar := by
    rw [Int.toNat_of_nonneg hrnonneg]
    have hdecomp := Int.ediv_mul_add_emod z (K.residueChar : ℤ)
    omega
  rw [QuotientGroup.eq_iff_div_mem]
  change (uniformizerUnit K) ^ z *
      ((uniformizerUnit K) ^ (Int.toNat (z % K.residueChar)))⁻¹ ∈
    (powMonoidHom (α := Kˣ) K.residueChar).range
  rw [← zpow_natCast, ← zpow_sub, hz, zpow_mul]
  refine ⟨(uniformizerUnit K) ^ (z / K.residueChar), ?_⟩
  change ((uniformizerUnit K) ^ (z / K.residueChar)) ^ K.residueChar =
    ((uniformizerUnit K) ^ (z / K.residueChar)) ^ (K.residueChar : ℤ)
  exact (zpow_natCast _ _).symm

theorem fieldModPowerParam_surjective
    (K : PointedMixedCharLocalField.{u}) :
    Function.Surjective (fieldModPowerParam K) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom (α := Kˣ) K.residueChar).range q
  obtain ⟨z, u, hu, hxu⟩ := exists_uniformizer_zpow_mul_integerUnit K x
  obtain ⟨a, ha⟩ := hu
  have hpZ : (0 : ℤ) < K.residueChar := by
    exact_mod_cast (Fact.out : K.residueChar.Prime).pos
  have hrnonneg : 0 ≤ z % (K.residueChar : ℤ) :=
    Int.emod_nonneg z hpZ.ne'
  let r : Fin K.residueChar :=
    ⟨Int.toNat (z % K.residueChar),
      (Int.toNat_lt hrnonneg).mpr (Int.emod_lt_of_pos z hpZ)⟩
  let UQ := (valuation K).integerˣ ⧸
    (powMonoidHom (α := (valuation K).integerˣ) K.residueChar).range
  refine ⟨(r, (a : UQ)), ?_⟩
  simp only [fieldModPowerParam, r, UQ,
    QuotientGroup.lift_mk, MonoidHom.coe_comp, Function.comp_apply]
  change (((uniformizerUnit K) ^ Int.toNat (z % K.residueChar) : Kˣ) :
      FieldModPowerQuotient K) *
      ((integerUnitsToFieldUnits K a : Kˣ) : FieldModPowerQuotient K) =
    (x : FieldModPowerQuotient K)
  rw [hxu, ← ha]
  change (((uniformizerUnit K) ^ Int.toNat (z % K.residueChar) : Kˣ) :
      FieldModPowerQuotient K) *
      ((integerUnitsToFieldUnits K a : Kˣ) : FieldModPowerQuotient K) =
    (((uniformizerUnit K) ^ z * integerUnitsToFieldUnits K a : Kˣ) :
      FieldModPowerQuotient K)
  let qF : Kˣ →* FieldModPowerQuotient K := QuotientGroup.mk' _
  change qF ((uniformizerUnit K) ^ Int.toNat (z % K.residueChar)) *
      qF (integerUnitsToFieldUnits K a) =
    qF ((uniformizerUnit K) ^ z * integerUnitsToFieldUnits K a)
  rw [map_mul]
  have hπ := uniformizer_zpow_eq_emod K z
  change qF ((uniformizerUnit K) ^ z) =
    qF ((uniformizerUnit K) ^ Int.toNat (z % K.residueChar)) at hπ
  rw [← hπ]

theorem fieldModPowerQuotient_finite
    (K : PointedMixedCharLocalField.{u}) :
    Finite (FieldModPowerQuotient K) := by
  let UQ := (valuation K).integerˣ ⧸
    (powMonoidHom (α := (valuation K).integerˣ) K.residueChar).range
  haveI : Finite UQ := integerUnitsModPower_finite K
  haveI : Finite (Fin K.residueChar × UQ) := inferInstance
  exact Finite.of_surjective (fieldModPowerParam K)
    (fieldModPowerParam_surjective K)

noncomputable def fieldModPowerToTorsionFreeModPower
    (K : PointedMixedCharLocalField.{u}) :
    FieldModPowerQuotient K →*
      FieldTorsionFreeModPowerQuotient K K.residueChar :=
  let qT : Kˣ →* FieldTorsionFreeQuotient K :=
    QuotientGroup.mk' (CommGroup.torsion Kˣ)
  let qP : FieldTorsionFreeQuotient K →*
      FieldTorsionFreeModPowerQuotient K K.residueChar :=
    QuotientGroup.mk'
      (powMonoidHom (α := FieldTorsionFreeQuotient K) K.residueChar).range
  QuotientGroup.lift
    (powMonoidHom (α := Kˣ) K.residueChar).range
    (qP.comp qT) (by
      intro x hx
      obtain ⟨y, rfl⟩ := hx
      rw [MonoidHom.mem_ker]
      change qP (qT (y ^ K.residueChar)) = 1
      rw [map_pow]
      change (((qT y) ^ K.residueChar : FieldTorsionFreeQuotient K) :
        FieldTorsionFreeModPowerQuotient K K.residueChar) = 1
      rw [QuotientGroup.eq_one_iff]
      exact ⟨qT y, rfl⟩)

theorem fieldModPowerToTorsionFreeModPower_surjective
    (K : PointedMixedCharLocalField.{u}) :
    Function.Surjective (fieldModPowerToTorsionFreeModPower K) := by
  intro q
  obtain ⟨qT, rfl⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom (α := FieldTorsionFreeQuotient K) K.residueChar).range q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CommGroup.torsion Kˣ) qT
  exact ⟨(x : FieldModPowerQuotient K), rfl⟩

theorem fieldTorsionFreeModPowerQuotient_residueChar_finite
    (K : PointedMixedCharLocalField.{u}) :
    Finite (FieldTorsionFreeModPowerQuotient K K.residueChar) := by
  haveI : Finite (FieldModPowerQuotient K) :=
    fieldModPowerQuotient_finite K
  exact Finite.of_surjective (fieldModPowerToTorsionFreeModPower K)
    (fieldModPowerToTorsionFreeModPower_surjective K)

end Anabelian.LCFT
