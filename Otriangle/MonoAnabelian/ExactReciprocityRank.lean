import Otriangle.MonoAnabelian.ExactFieldRank
import Otriangle.MonoAnabelian.ResidueCharacteristicReciprocityRank

/-!
# Exact residue-characteristic rank after local reciprocity

The kernel of the unramified projection on the abelianized mod-`p` quotient consists exactly of
classes arising from local units.  Its quotient is the rank-one unramified direction.  This
transports the exact cardinality `p^(e f + 1)` to the abelianized absolute Galois group.
-/

noncomputable section

namespace Anabelian.LCFT

open OTriangle ValuativeRel

universe u

/-- The kernel of the abelianized unramified projection modulo `p` is exactly the image of the
local-unit quotient under reciprocity. -/
theorem abelianizedModPowerToResidue_ker_eq_integerUnit_range
    {K : PointedMixedCharLocalField.{u}} (rec : LocalReciprocityMap K) :
    (abelianizedModPowerToResidue K K.residueChar).ker =
      (integerUnitModPowerToAbelianizedModPower rec).range := by
  let A := (valuation K).valuationSubring
  let U := A.unitGroup
  let UQ := IntegerUnitTorsionFreeQuotient K
  let UMP := IntegerUnitTorsionFreeModPowerQuotient K
  let B := AbelianizedAbsoluteGaloisGroup K
  let BT := AbelianizedTorsionFreeQuotient K
  let BMP := AbelianizedTorsionFreeModPowerQuotient K K.residueChar
  let R := ResidueAbsoluteGaloisGroup K
  let RT := ResidueTorsionFreeQuotient K
  let RMP := ResidueTorsionFreeModPowerQuotient K K.residueChar
  let qB : B →* BT := QuotientGroup.mk' (CommGroup.torsion B)
  let qBP : BT →* BMP :=
    QuotientGroup.mk' (powMonoidHom (α := BT) K.residueChar).range
  let qR : R →* RT := QuotientGroup.mk' (CommGroup.torsion R)
  ext q
  constructor
  · intro hq
    rw [MonoidHom.mem_ker] at hq
    obtain ⟨bt, rfl⟩ := QuotientGroup.mk'_surjective
      (powMonoidHom (α := BT) K.residueChar).range q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective
      (CommGroup.torsion B) bt
    change (((qR (unramifiedProjection K b) : RT) : RMP)) = 1 at hq
    have hpow : qR (unramifiedProjection K b) ∈
        (powMonoidHom (α := RT) K.residueChar).range := by
      rwa [← QuotientGroup.eq_one_iff]
    obtain ⟨rt, hrt⟩ := hpow
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk'_surjective
      (CommGroup.torsion R) rt
    change qR (σ ^ K.residueChar) =
      qR (unramifiedProjection K b) at hrt
    have htor : σ ^ K.residueChar *
        (unramifiedProjection K b)⁻¹ ∈ CommGroup.torsion R := by
      rw [← QuotientGroup.eq_one_iff]
      change qR (σ ^ K.residueChar *
        (unramifiedProjection K b)⁻¹) = 1
      rw [map_mul, map_inv, hrt, mul_inv_cancel]
    have hratio : σ ^ K.residueChar *
        (unramifiedProjection K b)⁻¹ = 1 :=
      residueAbsoluteGaloisGroup_isOfFinOrder_eq_one K _ htor
    have hσ : σ ^ K.residueChar = unramifiedProjection K b :=
      mul_inv_eq_one.mp hratio
    obtain ⟨c, hc⟩ := unramifiedProjection_surjective K σ
    let d : B := b * (c ^ K.residueChar)⁻¹
    have hdproj : unramifiedProjection K d = 1 := by
      simp only [d, map_mul, map_inv, map_pow, hc]
      rw [hσ]
      simp
    have hd : d ∈ inertiaSubgroup K :=
      (unramifiedProjection_eq_one_iff K d).mp hdproj
    obtain ⟨a, ha⟩ := rec.mapsUnits.unitsEquiv.surjective ⟨d, hd⟩
    let u : U := A.unitGroupMulEquiv.symm a
    have huField : integerUnitsToFieldUnits K a = (u : Kˣ) := by
      apply Units.ext
      rfl
    have hrec : rec.toMonoidHom (u : Kˣ) = d := by
      calc
        rec.toMonoidHom (u : Kˣ) =
            rec.toMonoidHom (integerUnitsToFieldUnits K a) :=
          congrArg rec.toMonoidHom huField.symm
        _ = d := by
          have hcompat := DFunLike.congr_fun rec.mapsUnits.compatibility a
          exact hcompat.symm.trans (congrArg Subtype.val ha)
    refine ⟨(((u : U) : UQ) : UMP), ?_⟩
    change qBP (qB (rec.toMonoidHom (u : Kˣ))) = qBP (qB b)
    rw [hrec]
    have hcP : qBP (qB (c ^ K.residueChar)) = 1 := by
      change (((qB (c ^ K.residueChar) : BT)) : BMP) = 1
      rw [QuotientGroup.eq_one_iff]
      refine ⟨qB c, ?_⟩
      change (qB c) ^ K.residueChar = qB (c ^ K.residueChar)
      exact (map_pow qB c K.residueChar).symm
    have hcPinv : (qBP (qB (c ^ K.residueChar)))⁻¹ = 1 := by
      rw [hcP, inv_one]
    change qBP (qB (b * (c ^ K.residueChar)⁻¹)) = qBP (qB b)
    rw [map_mul, map_inv, map_mul]
    calc
      qBP (qB b) * (qBP (qB (c ^ K.residueChar)))⁻¹ =
          qBP (qB b) * 1 := congrArg (qBP (qB b) * ·) hcPinv
      _ = qBP (qB b) := mul_one _
  · rintro ⟨q, rfl⟩
    exact abelianizedModPowerToResidue_integerUnit rec q

/-- Hoshi's exact residue-characteristic mod-power cardinal on the abelianized local Galois
group. -/
theorem abelianizedTorsionFreeModPowerQuotient_card_eq_residueDegreeProduct_succ
    {K : PointedMixedCharLocalField.{u}} (rec : LocalReciprocityMap K) :
    Nat.card
        (AbelianizedTorsionFreeModPowerQuotient K K.residueChar) =
      K.residueChar ^
        (absoluteRamificationIndex K * localResidueDegree K + 1) := by
  let UMP := IntegerUnitTorsionFreeModPowerQuotient K
  let FMP := FieldTorsionFreeModPowerQuotient K K.residueChar
  let BMP := AbelianizedTorsionFreeModPowerQuotient K K.residueChar
  let RMP := ResidueTorsionFreeModPowerQuotient K K.residueChar
  let i : UMP →* BMP := integerUnitModPowerToAbelianizedModPower rec
  let f : BMP →* RMP := abelianizedModPowerToResidue K K.residueChar
  haveI : Finite FMP :=
    fieldTorsionFreeModPowerQuotient_residueChar_finite K
  haveI : Finite BMP := Finite.of_surjective
    (reciprocityModPowerMap rec K.residueChar)
    (reciprocityModPowerMap_surjective rec K.residueChar Fact.out)
  have hi : Function.Injective i :=
    integerUnitModPowerToAbelianizedModPower_injective rec
  have hf : Function.Surjective f :=
    abelianizedModPowerToResidue_residueChar_surjective rec
  let ei : UMP ≃* i.range :=
    MulEquiv.ofBijective i.rangeRestrict
      ⟨fun _ _ h ↦ hi (congrArg Subtype.val h), i.rangeRestrict_surjective⟩
  have hker : Nat.card f.ker =
      K.residueChar ^
        (absoluteRamificationIndex K * localResidueDegree K) := by
    rw [abelianizedModPowerToResidue_ker_eq_integerUnit_range rec]
    exact (Nat.card_congr ei.symm.toEquiv).trans
      (integerUnitTorsionFreeModPowerQuotient_card_eq_residueDegreeProduct K)
  have hrange : Nat.card f.range = K.residueChar := by
    rw [f.range_eq_top_of_surjective hf, Subgroup.card_top]
    exact residueTorsionFreeModPowerQuotient_card_eq_prime K K.residueChar Fact.out
  calc
    Nat.card BMP = Nat.card f.ker * Nat.card f.range := by
      rw [← Subgroup.index_ker f]
      exact f.ker.card_mul_index.symm
    _ = K.residueChar ^
          (absoluteRamificationIndex K * localResidueDegree K) *
        K.residueChar := by rw [hker, hrange]
    _ = K.residueChar ^
        (absoluteRamificationIndex K * localResidueDegree K + 1) := by
      rw [pow_succ]

end Anabelian.LCFT
