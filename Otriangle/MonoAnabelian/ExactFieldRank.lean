import Otriangle.MonoAnabelian.ExactUnitRank

/-!
# Exact residue-characteristic rank of the local multiplicative group

The local-unit quotient is exactly the kernel of discrete valuation modulo the residue
characteristic.  A uniformizer supplies the complementary cyclic factor, so the full
torsion-free multiplicative quotient has cardinality `p^(e f + 1)`.
-/

noncomputable section

namespace Anabelian.LCFT

open OTriangle ValuativeRel

universe u

/-- The kernel of discrete valuation modulo `p` consists exactly of local-unit classes. -/
theorem fieldModPowerDiscreteValuationMod_ker_eq_integerUnit_range
    (K : PointedMixedCharLocalField.{u}) :
    (fieldModPowerDiscreteValuationMod K).ker =
      (integerUnitModPowerToFieldModPowerTorsionFree K).range := by
  let U := (valuation K).valuationSubring.unitGroup
  let UQ := IntegerUnitTorsionFreeQuotient K
  let UMP := IntegerUnitTorsionFreeModPowerQuotient K
  let FQ := FieldTorsionFreeQuotient K
  let FMP := FieldTorsionFreeModPowerQuotient K K.residueChar
  let qF : Kˣ →* FQ := QuotientGroup.mk' (CommGroup.torsion Kˣ)
  let qP : FQ →* FMP :=
    QuotientGroup.mk' (powMonoidHom (α := FQ) K.residueChar).range
  ext q
  constructor
  · intro hq
    rw [MonoidHom.mem_ker] at hq
    obtain ⟨q0, rfl⟩ := QuotientGroup.mk'_surjective
      (powMonoidHom (α := FQ) K.residueChar).range q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (CommGroup.torsion Kˣ) q0
    change fieldDiscreteValuationModRaw K x = 1 at hq
    let m : ℤ := (fieldUnitDiscreteValuation K x).toAdd
    have hmzero : (m : ZMod K.residueChar) = 0 := by
      have h := congrArg Multiplicative.toAdd hq
      exact h
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd m K.residueChar).mp hmzero
    let y : Kˣ := x * (uniformizerUnit K) ^ m
    have hydisc : fieldUnitDiscreteValuation K y = 1 := by
      apply Multiplicative.toAdd.injective
      simp only [y, map_mul, map_zpow,
        fieldUnitDiscreteValuation_uniformizer, toAdd_mul, toAdd_zpow]
      change m + m • (-1 : ℤ) = 0
      simp
    have hyval : valuation K (y : K) = 1 :=
      (fieldUnitDiscreteValuation_eq_one_iff K y).mp hydisc
    let yu : U :=
      ⟨y, (Valuation.mem_unitGroup_iff K (valuation K) y).mpr hyval⟩
    refine ⟨(((yu : U) : UQ) : UMP), ?_⟩
    change qP (qF y) = qP (qF x)
    have hmk : m = (K.residueChar : ℤ) * k := hk
    have hπ : qP (qF ((uniformizerUnit K) ^ m)) = 1 := by
      change (((qF ((uniformizerUnit K) ^ m) : FQ)) : FMP) = 1
      rw [QuotientGroup.eq_one_iff]
      refine ⟨qF ((uniformizerUnit K) ^ k), ?_⟩
      change (qF ((uniformizerUnit K) ^ k)) ^ K.residueChar =
        qF ((uniformizerUnit K) ^ m)
      rw [← map_pow]
      apply congrArg qF
      calc
        ((uniformizerUnit K) ^ k) ^ K.residueChar =
            ((uniformizerUnit K) ^ k) ^ (K.residueChar : ℤ) :=
          (zpow_natCast _ _).symm
        _ = (uniformizerUnit K) ^ (k * (K.residueChar : ℤ)) :=
          (zpow_mul _ _ _).symm
        _ = (uniformizerUnit K) ^ m := by rw [hmk, mul_comm]
    change qP (qF (x * (uniformizerUnit K) ^ m)) = qP (qF x)
    rw [map_mul, map_mul, hπ, mul_one]
  · rintro ⟨q, rfl⟩
    exact fieldModPowerDiscreteValuationMod_integerUnit K q

/-- The exact cardinality of the torsion-free local multiplicative group modulo
residue-characteristic powers. -/
theorem fieldTorsionFreeModPowerQuotient_card_eq_residueDegreeProduct_succ
    (K : PointedMixedCharLocalField.{u}) :
    Nat.card (FieldTorsionFreeModPowerQuotient K K.residueChar) =
      K.residueChar ^
        (absoluteRamificationIndex K * localResidueDegree K + 1) := by
  let UMP := IntegerUnitTorsionFreeModPowerQuotient K
  let FMP := FieldTorsionFreeModPowerQuotient K K.residueChar
  let T := Multiplicative (ZMod K.residueChar)
  let i : UMP →* FMP :=
    integerUnitModPowerToFieldModPowerTorsionFree K
  let f : FMP →* T := fieldModPowerDiscreteValuationMod K
  haveI : Finite FMP :=
    fieldTorsionFreeModPowerQuotient_residueChar_finite K
  have hi : Function.Injective i :=
    integerUnitModPowerToFieldModPowerTorsionFree_injective K
  have hf : Function.Surjective f :=
    fieldModPowerDiscreteValuationMod_surjective K
  let ei : UMP ≃* i.range :=
    MulEquiv.ofBijective i.rangeRestrict
      ⟨fun _ _ h ↦ hi (congrArg Subtype.val h), i.rangeRestrict_surjective⟩
  have hker : Nat.card f.ker =
      K.residueChar ^
        (absoluteRamificationIndex K * localResidueDegree K) := by
    rw [fieldModPowerDiscreteValuationMod_ker_eq_integerUnit_range K]
    exact (Nat.card_congr ei.symm.toEquiv).trans
      (integerUnitTorsionFreeModPowerQuotient_card_eq_residueDegreeProduct K)
  have hrange : Nat.card f.range = K.residueChar := by
    rw [f.range_eq_top_of_surjective hf, Subgroup.card_top]
    exact (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod _)
  calc
    Nat.card FMP = Nat.card f.ker * Nat.card f.range := by
      rw [← Subgroup.index_ker f]
      exact f.ker.card_mul_index.symm
    _ = K.residueChar ^
          (absoluteRamificationIndex K * localResidueDegree K) *
        K.residueChar := by rw [hker, hrange]
    _ = K.residueChar ^
        (absoluteRamificationIndex K * localResidueDegree K + 1) := by
      rw [pow_succ]

end Anabelian.LCFT
