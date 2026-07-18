import Otriangle.LCFT
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.GroupTheory.OrderOfElement

/-!
# One-field multiplicative reconstruction

This module develops Hoshi's Proposition 3.11 for the integral multiplicative monoid.  The first
step is to derive injectivity of local reciprocity from its units and Frobenius properties.
-/

noncomputable section

namespace Anabelian
namespace LCFT

open OTriangle
open ValuativeRel

universe u

/-- Arithmetic Frobenius on the algebraic closure of a finite residue field has infinite order. -/
theorem residueFrobenius_not_isOfFinOrder (K : PointedMixedCharLocalField.{u}) :
    ¬ IsOfFinOrder (residueFrobenius K) := by
  letI := Fintype.ofFinite (ResidueField K)
  letI : IsAlgClosed (AlgebraicClosureResidueField K) :=
    IsAlgClosure.isAlgClosed (ResidueField K)
  intro hfinite
  obtain ⟨n, hn, hpow⟩ := hfinite.exists_pow_eq_one
  let d := n + 1
  let E := FiniteField.Extension (ResidueField K) K.residueChar d
  let ι : E →ₐ[ResidueField K] AlgebraicClosureResidueField K := IsAlgClosed.lift
  have hfrob : FiniteField.Extension.frob (ResidueField K) K.residueChar d ^ n = 1 := by
    ext x
    apply ι.injective
    have hpowx := DFunLike.congr_fun hpow (ι x)
    simp only [residueFrobenius, AlgEquiv.coe_pow, AlgEquiv.one_apply] at hpowx
    rw [
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate] at hpowx
    rw [FiniteField.Extension.frob_iterate_apply]
    rw [map_pow]
    change ι x ^ Nat.card (ResidueField K) ^ n = ι x
    simpa only [Fintype.card_eq_nat_card] using hpowx
  have horder : orderOf (FiniteField.Extension.frob
      (ResidueField K) K.residueChar d) = d := by
    change orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic
      (ResidueField K) E) = d
    rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
      FiniteField.finrank_extension]
  have hdvd : d ∣ n := by
    rw [← horder]
    exact orderOf_dvd_of_pow_eq_one hfrob
  exact (Nat.not_succ_le_self n) (Nat.le_of_dvd hn hdvd)

private theorem withZeroMulInt_le_exp_neg_one_of_lt_one
    {x : WithZero (Multiplicative ℤ)} (hx : x < 1) :
    x ≤ WithZero.exp (-1 : ℤ) := by
  induction x using WithZero.recZeroCoe with
  | zero => exact bot_le
  | coe x =>
      rw [WithZero.exp_eq_coe_ofAdd]
      norm_cast at hx ⊢
      change x.toAdd < 0 at hx
      change x.toAdd ≤ -1
      omega

/-- The order isomorphism for the value group sends the distinguished uniformizer value to
`exp (-1)`. -/
theorem valueGroupWithZeroIsoInt_uniformizer (K : PointedMixedCharLocalField.{u}) :
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (ValuativeRel.uniformizer K) =
      WithZero.exp (-1 : ℤ) := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  apply le_antisymm
  · apply withZeroMulInt_le_exp_neg_one_of_lt_one
    have h := (map_lt_map_iff e).mpr (ValuativeRel.uniformizer_lt_one (R := K))
    simpa [e] using h
  · have hpre : e.symm (WithZero.exp (-1 : ℤ)) ≤ ValuativeRel.uniformizer K := by
      rw [ValuativeRel.le_uniformizer_iff]
      apply (map_lt_map_iff e).mp
      rw [e.apply_symm_apply, map_one, WithZero.exp_eq_coe_ofAdd]
      norm_cast
    have h := (map_le_map_iff e).mpr hpre
    simpa [e] using h

/-- Valuation on nonzero field elements, with its values regarded as units of the value group. -/
noncomputable def fieldUnitValuation (K : PointedMixedCharLocalField.{u}) :
    Kˣ →* (ValueGroupWithZero K)ˣ :=
  Units.map (valuation K).toMonoidWithZeroHom.toMonoidHom

theorem fieldUnitValuation_surjective (K : PointedMixedCharLocalField.{u}) :
    Function.Surjective (fieldUnitValuation K) := by
  intro γ
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero K)
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    apply γ.ne_zero
    simpa using hx.symm
  refine ⟨Units.mk0 x hx0, ?_⟩
  apply Units.ext
  exact hx

/-- A uniformizer chosen from surjectivity of the canonical valuation. -/
noncomputable def uniformizerUnit (K : PointedMixedCharLocalField.{u}) : Kˣ :=
  (fieldUnitValuation_surjective K
    (Units.mk0 (ValuativeRel.uniformizer K) (ValuativeRel.uniformizer_ne_zero (R := K)))).choose

theorem uniformizerUnit_isUniformizer (K : PointedMixedCharLocalField.{u}) :
    IsUniformizer K (uniformizerUnit K) := by
  have h := (fieldUnitValuation_surjective K
    (Units.mk0 (ValuativeRel.uniformizer K)
      (ValuativeRel.uniformizer_ne_zero (R := K)))).choose_spec
  exact congrArg Units.val h

/-- Every nonzero value is an integral power of the value of the chosen uniformizer. -/
theorem exists_fieldUnitValuation_eq_uniformizer_zpow
    (K : PointedMixedCharLocalField.{u}) (x : Kˣ) :
    ∃ n : ℤ, fieldUnitValuation K x = fieldUnitValuation K (uniformizerUnit K) ^ n := by
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
  let m : ℤ := (e (fieldUnitValuation K x)).toAdd
  refine ⟨-m, e.injective ?_⟩
  rw [map_zpow, hπ]
  apply Multiplicative.toAdd.injective
  simp [m]

/-- Value one is equivalent to lying in the image of the valuation-ring unit group. -/
theorem mem_integerUnitSubgroup_of_fieldUnitValuation_eq_one
    (K : PointedMixedCharLocalField.{u}) (x : Kˣ)
    (hx : fieldUnitValuation K x = 1) : x ∈ integerUnitSubgroup K := by
  have hxval : valuation K (x : K) = 1 := congrArg Units.val hx
  let a : 𝒪[K] := ⟨(x : K), by
    rw [Valuation.mem_integer_iff, hxval]⟩
  have ha : IsUnit a :=
    (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation K))).mpr hxval
  refine ⟨ha.unit, ?_⟩
  apply Units.ext
  rfl

/-- Multiplicative decomposition into a power of a uniformizer and a valuation-ring unit. -/
theorem exists_uniformizer_zpow_mul_integerUnit
    (K : PointedMixedCharLocalField.{u}) (x : Kˣ) :
    ∃ (n : ℤ) (u : Kˣ), u ∈ integerUnitSubgroup K ∧
      x = uniformizerUnit K ^ n * u := by
  obtain ⟨n, hn⟩ := exists_fieldUnitValuation_eq_uniformizer_zpow K x
  let u := x * (uniformizerUnit K ^ n)⁻¹
  have huval : fieldUnitValuation K u = 1 := by
    simp only [u, map_mul, map_inv, map_zpow, hn, mul_inv_cancel]
  refine ⟨n, u, mem_integerUnitSubgroup_of_fieldUnitValuation_eq_one K u huval, ?_⟩
  simp [u]

/-- Reciprocity is injective on valuation-ring units by the units--inertia isomorphism. -/
theorem LocalReciprocityMap.eq_one_of_mem_integerUnitSubgroup
    {K : PointedMixedCharLocalField.{u}} (rec : LocalReciprocityMap K) (x : Kˣ)
    (hxunit : x ∈ integerUnitSubgroup K) (hx : rec.toMonoidHom x = 1) : x = 1 := by
  obtain ⟨a, rfl⟩ := hxunit
  have hcompat := DFunLike.congr_fun rec.mapsUnits.compatibility a
  have heq : rec.mapsUnits.unitsEquiv a = 1 := by
    apply Subtype.ext
    change (inertiaSubgroup K).subtype (rec.mapsUnits.unitsEquiv a) = 1
    calc
      _ = rec.toMonoidHom (integerUnitsToFieldUnits K a) := by simpa using hcompat
      _ = 1 := hx
  have ha : a = 1 := rec.mapsUnits.unitsEquiv.injective (by simpa using heq)
  rw [ha, map_one]

/-- The units and Frobenius properties imply that the kernel of local reciprocity is trivial. -/
theorem LocalReciprocityMap.eq_one_of_map_eq_one
    {K : PointedMixedCharLocalField.{u}} (rec : LocalReciprocityMap K) (x : Kˣ)
    (hx : rec.toMonoidHom x = 1) : x = 1 := by
  obtain ⟨n, u, hu, hdecomp⟩ := exists_uniformizer_zpow_mul_integerUnit K x
  let qK : Kˣ →* (Kˣ ⧸ integerUnitSubgroup K) :=
    QuotientGroup.mk' (integerUnitSubgroup K)
  let qG : AbelianizedAbsoluteGaloisGroup K →*
      (AbelianizedAbsoluteGaloisGroup K ⧸ inertiaSubgroup K) :=
    QuotientGroup.mk' (inertiaSubgroup K)
  let recQ := inducedUnramifiedMap rec.toMonoidHom rec.mapsUnits
  have hπ := rec.mapsUniformizers (uniformizerUnit K) (uniformizerUnit_isUniformizer K)
  have hqu : qK u = 1 := (QuotientGroup.eq_one_iff _).mpr hu
  have hxq : unramifiedQuotientEquiv K (recQ (qK x)) = 1 := by
    change unramifiedQuotientEquiv K (qG (rec.toMonoidHom x)) = 1
    rw [hx, map_one, map_one]
  have hqx : qK (uniformizerUnit K ^ n) = qK x := by
    rw [hdecomp, map_mul, hqu, mul_one]
  have hfrob : residueFrobenius K ^ n = 1 := by
    calc
      residueFrobenius K ^ n =
          (unramifiedQuotientEquiv K (recQ (qK (uniformizerUnit K)))) ^ n := by rw [hπ]
      _ = unramifiedQuotientEquiv K (recQ (qK (uniformizerUnit K ^ n))) := by
        simp only [map_zpow]
      _ = unramifiedQuotientEquiv K (recQ (qK x)) := by
        rw [hqx]
      _ = 1 := hxq
  have hn : n = 0 := by
    apply (injective_zpow_iff_not_isOfFinOrder.mpr
      (residueFrobenius_not_isOfFinOrder K))
    simpa using hfrob
  have hxu : x = u := by simpa [hn] using hdecomp
  rw [hxu] at hx ⊢
  exact rec.eq_one_of_mem_integerUnitSubgroup u hu hx

/-- Local reciprocity is injective; this is derived rather than included in
`LocalReciprocityMap`. -/
theorem LocalReciprocityMap.injective {K : PointedMixedCharLocalField.{u}}
    (rec : LocalReciprocityMap K) : Function.Injective rec.toMonoidHom := by
  intro x y hxy
  have hker : rec.toMonoidHom (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  exact mul_inv_eq_one.mp (rec.eq_one_of_map_eq_one (x * y⁻¹) hker)

/-- The monoid `𝒪_K^▹` of nonzero integral elements of the base field. -/
noncomputable def baseIntegerMonoid (K : PointedMixedCharLocalField.{u}) : Submonoid Kˣ :=
  Submonoid.comap (Units.coeHom K) (valuation K).integer.toSubmonoid

namespace LocalReciprocityFamily

/-- Restriction of reciprocity to `𝒪_K^▹`. -/
noncomputable def integerMonoidHom (reciprocity : LocalReciprocityFamily.{u})
    (K : PointedMixedCharLocalField.{u}) :
    baseIntegerMonoid K →* AbelianizedAbsoluteGaloisGroup K :=
  (reciprocity.map K).toMonoidHom.comp (baseIntegerMonoid K).subtype

theorem integerMonoidHom_injective (reciprocity : LocalReciprocityFamily.{u})
    (K : PointedMixedCharLocalField.{u}) :
    Function.Injective (reciprocity.integerMonoidHom K) :=
  (reciprocity.map K).injective.comp (baseIntegerMonoid K).subtype_injective

/-- The reconstructed one-field integral monoid, realized inside `G_K^ab`. -/
noncomputable def reconstructedBaseIntegerMonoid
    (reciprocity : LocalReciprocityFamily.{u}) (K : PointedMixedCharLocalField.{u}) :
    Submonoid (AbelianizedAbsoluteGaloisGroup K) :=
  MonoidHom.mrange (reciprocity.integerMonoidHom K)

/-- Restricted reciprocity identifies `𝒪_K^▹` with its reconstructed image. -/
noncomputable def baseIntegerMonoidEquiv
    (reciprocity : LocalReciprocityFamily.{u}) (K : PointedMixedCharLocalField.{u}) :
    baseIntegerMonoid K ≃* reciprocity.reconstructedBaseIntegerMonoid K :=
  MulEquiv.ofLeftInverse' (reciprocity.integerMonoidHom K)
    (Function.leftInverse_invFun (reciprocity.integerMonoidHom_injective K))

end LocalReciprocityFamily

end LCFT
end Anabelian
