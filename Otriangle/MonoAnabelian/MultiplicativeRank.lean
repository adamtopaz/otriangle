import Otriangle.MonoAnabelian.PrincipalUnits
import Otriangle.MonoAnabelian.OneField
import Mathlib.GroupTheory.Torsion

/-!
# The prime-to-residue-characteristic rank of a local multiplicative group

The discrete valuation supplies the unique prime-to-residue-characteristic direction in the
torsion-free local multiplicative group.  Together with the principal-unit calculation, this
proves that its quotient by `l`th powers has exactly `l` elements whenever `l` is a prime other
than the residue characteristic.
-/

noncomputable section

namespace Anabelian
namespace LCFT

open OTriangle
open ValuativeRel

universe u

/-- The additive integer-valued discrete valuation, written multiplicatively on field units. -/
noncomputable def fieldUnitDiscreteValuation
    (K : PointedMixedCharLocalField.{u}) : Kˣ →* Multiplicative ℤ :=
  ((Units.mapEquiv
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toMulEquiv).trans
    WithZero.unitsWithZeroEquiv).toMonoidHom.comp (fieldUnitValuation K)

/-- The chosen uniformizer has discrete valuation `-1` in the convention used by the
`ValuativeRel` value group. -/
theorem fieldUnitDiscreteValuation_uniformizer
    (K : PointedMixedCharLocalField.{u}) :
    fieldUnitDiscreteValuation K (uniformizerUnit K) =
      Multiplicative.ofAdd (-1 : ℤ) := by
  let e : (ValueGroupWithZero K)ˣ ≃* Multiplicative ℤ :=
    (Units.mapEquiv
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toMulEquiv).trans
      WithZero.unitsWithZeroEquiv
  have hπval : (fieldUnitValuation K (uniformizerUnit K) : ValueGroupWithZero K) =
      ValuativeRel.uniformizer K := uniformizerUnit_isUniformizer K
  have hπ : e (fieldUnitValuation K (uniformizerUnit K)) =
      Multiplicative.ofAdd (-1 : ℤ) := by
    dsimp [e]
    apply WithZero.coe_injective
    rw [WithZero.coe_unitsWithZeroEquiv_eq_units_val]
    change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
      (fieldUnitValuation K (uniformizerUnit K) : ValueGroupWithZero K) = _
    rw [hπval, valueGroupWithZeroIsoInt_uniformizer]
    rfl
  exact hπ

/-- Torsion field units have discrete valuation zero. -/
theorem fieldUnitDiscreteValuation_eq_one_of_isOfFinOrder
    (K : PointedMixedCharLocalField.{u}) (x : Kˣ) (hx : IsOfFinOrder x) :
    fieldUnitDiscreteValuation K x = 1 := by
  obtain ⟨n, hn, hpow⟩ := hx.exists_pow_eq_one
  have hmap := congrArg (fieldUnitDiscreteValuation K) hpow
  rw [map_pow, map_one] at hmap
  have hadd := congrArg Multiplicative.toAdd hmap
  change n • (fieldUnitDiscreteValuation K x).toAdd = 0 at hadd
  change (n : ℤ) * (fieldUnitDiscreteValuation K x).toAdd = 0 at hadd
  have hzero : (fieldUnitDiscreteValuation K x).toAdd = 0 := by
    have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
    exact (mul_eq_zero.mp hadd).resolve_left hn0
  apply Multiplicative.toAdd.injective
  simp [hzero]

/-- A uniformizer cannot be an `l`th power modulo torsion. -/
theorem uniformizer_not_pow_mod_torsion
    (K : PointedMixedCharLocalField.{u}) (l : ℕ) (hl : l.Prime)
    (x : Kˣ) :
    uniformizerUnit K * (x ^ l)⁻¹ ∉ CommGroup.torsion Kˣ := by
  intro ht
  have hval := fieldUnitDiscreteValuation_eq_one_of_isOfFinOrder K _ ht
  rw [map_mul, map_inv, map_pow,
    fieldUnitDiscreteValuation_uniformizer] at hval
  have hadd := congrArg Multiplicative.toAdd hval
  change (-1 : ℤ) + -(l • (fieldUnitDiscreteValuation K x).toAdd) = 0 at hadd
  change (-1 : ℤ) +
    -((l : ℤ) * (fieldUnitDiscreteValuation K x).toAdd) = 0 at hadd
  have heq : (l : ℤ) *
      (-(fieldUnitDiscreteValuation K x).toAdd) = 1 := by
    linarith
  have hdivZ : (l : ℤ) ∣ 1 := ⟨_, heq.symm⟩
  have hdivN : l ∣ 1 := by exact_mod_cast hdivZ
  exact hl.ne_one (Nat.dvd_one.mp hdivN)

/-- Every field unit is a uniformizer power times a torsion unit times an `l`th power, away from
the residue characteristic. -/
theorem fieldUnit_eq_uniformizer_zpow_mul_torsion_mul_pow
    (K : PointedMixedCharLocalField.{u}) (l : ℕ) (hl : l.Prime)
    (hne : l ≠ K.residueChar) (x : Kˣ) :
    ∃ (z : ℤ) (t : Kˣ), IsOfFinOrder t ∧
      ∃ v : Kˣ, x = uniformizerUnit K ^ z * t * v ^ l := by
  obtain ⟨z, u, hu, hxu⟩ := exists_uniformizer_zpow_mul_integerUnit K x
  obtain ⟨a, rfl⟩ := hu
  let A : ValuationSubring K := (valuation K).valuationSubring
  let aA : Aˣ := a
  let au : A.unitGroup := A.unitGroupMulEquiv.symm aA
  obtain ⟨t, ht, v, huv⟩ := integerUnit_eq_torsion_mul_pow K l hl hne au
  let tK : Kˣ := t
  let vK : Kˣ := v
  have htK : IsOfFinOrder tK := by
    obtain ⟨n, hn, htn⟩ := ht.exists_pow_eq_one
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨n, hn, ?_⟩
    exact congrArg Subtype.val htn
  refine ⟨z, tK, htK, vK, ?_⟩
  have huv' := congrArg Subtype.val huv
  have hunit : integerUnitsToFieldUnits K a = tK * vK ^ l := by
    apply Units.ext
    exact congrArg Units.val huv'
  rw [hxu, hunit, mul_assoc]

/-- The torsion-free quotient of the local multiplicative group. -/
abbrev FieldTorsionFreeQuotient (K : PointedMixedCharLocalField.{u}) :=
  Kˣ ⧸ CommGroup.torsion Kˣ

/-- The torsion-free local multiplicative group modulo `l`th powers. -/
abbrev FieldTorsionFreeModPowerQuotient
    (K : PointedMixedCharLocalField.{u}) (l : ℕ) :=
  FieldTorsionFreeQuotient K ⧸
    (powMonoidHom (α := FieldTorsionFreeQuotient K) l).range

/-- The uniformizer class in the torsion-free mod-power quotient. -/
noncomputable def fieldUniformizerModPower
    (K : PointedMixedCharLocalField.{u}) (l : ℕ) :
    FieldTorsionFreeModPowerQuotient K l :=
  ((uniformizerUnit K : Kˣ) : FieldTorsionFreeQuotient K)

theorem fieldUniformizerModPower_ne_one
    (K : PointedMixedCharLocalField.{u}) (l : ℕ) (hl : l.Prime) :
    fieldUniformizerModPower K l ≠ 1 := by
  intro hg
  let qT : Kˣ →* FieldTorsionFreeQuotient K :=
    QuotientGroup.mk' (CommGroup.torsion Kˣ)
  have hmem : qT (uniformizerUnit K) ∈
      (powMonoidHom (α := FieldTorsionFreeQuotient K) l).range := by
    rw [← QuotientGroup.eq_one_iff]
    exact hg
  obtain ⟨z, hz⟩ := hmem
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
    (CommGroup.torsion Kˣ) z
  change qT (x ^ l) = qT (uniformizerUnit K) at hz
  change ((x ^ l : Kˣ) : FieldTorsionFreeQuotient K) =
    ((uniformizerUnit K : Kˣ) : FieldTorsionFreeQuotient K) at hz
  rw [QuotientGroup.eq_iff_div_mem] at hz
  apply uniformizer_not_pow_mod_torsion K l hl x
  have hinv := (CommGroup.torsion Kˣ).inv_mem hz
  simpa [div_eq_mul_inv, mul_comm] using hinv

/-- For a prime away from the residue characteristic, the torsion-free local multiplicative
group modulo `l`th powers has exactly `l` elements. -/
theorem fieldTorsionFreeModPowerQuotient_card_eq_prime
    (K : PointedMixedCharLocalField.{u}) (l : ℕ) (hl : l.Prime)
    (hne : l ≠ K.residueChar) :
    Nat.card (FieldTorsionFreeModPowerQuotient K l) = l := by
  let Q := FieldTorsionFreeModPowerQuotient K l
  let qT : Kˣ →* FieldTorsionFreeQuotient K :=
    QuotientGroup.mk' (CommGroup.torsion Kˣ)
  let qP : FieldTorsionFreeQuotient K →* Q :=
    QuotientGroup.mk'
      (powMonoidHom (α := FieldTorsionFreeQuotient K) l).range
  let g : Q := fieldUniformizerModPower K l
  have hgpow : g ^ l = 1 := by
    change qP (qT (uniformizerUnit K)) ^ l = 1
    rw [← map_pow]
    change (((qT (uniformizerUnit K)) ^ l : FieldTorsionFreeQuotient K) : Q) = 1
    rw [QuotientGroup.eq_one_iff]
    exact ⟨qT (uniformizerUnit K), rfl⟩
  have hgne : g ≠ 1 := fieldUniformizerModPower_ne_one K l hl
  have htop : Subgroup.zpowers g = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective
      (powMonoidHom (α := FieldTorsionFreeQuotient K) l).range y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (CommGroup.torsion Kˣ) z
    obtain ⟨n, t, ht, v, hx⟩ :=
      fieldUnit_eq_uniformizer_zpow_mul_torsion_mul_pow K l hl hne x
    refine ⟨n, ?_⟩
    change qP (qT (uniformizerUnit K)) ^ n = qP (qT x)
    rw [← map_zpow, hx]
    have htq : qT t = 1 := by
      change ((t : Kˣ) : FieldTorsionFreeQuotient K) = 1
      rw [QuotientGroup.eq_one_iff]
      exact ht
    have hvq : qP ((qT v) ^ l) = 1 := by
      change (((qT v) ^ l : FieldTorsionFreeQuotient K) : Q) = 1
      rw [QuotientGroup.eq_one_iff]
      exact ⟨qT v, rfl⟩
    simp only [map_mul, map_zpow, map_pow, htq, hvq, mul_one]
  have hordNe : orderOf g ≠ 1 := by
    intro h
    exact hgne (orderOf_eq_one_iff.mp h)
  have hord : orderOf g = l :=
    (hl.eq_one_or_self_of_dvd (orderOf g)
      (orderOf_dvd_of_pow_eq_one hgpow)).resolve_left hordNe
  rw [← orderOf_eq_card_of_zpowers_eq_top htop, hord]

end LCFT
end Anabelian
