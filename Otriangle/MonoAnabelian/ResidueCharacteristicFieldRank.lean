import Otriangle.MonoAnabelian.ResidueUnitRank
import Mathlib.GroupTheory.Index

/-!
# Two multiplicative directions in residue characteristic

The valuation-ring unit direction injects into the field power quotient.  Discrete valuation
modulo the residue characteristic supplies an independent uniformizer direction.  Counting the
kernel and image proves that the finite torsion-free field quotient has cardinality at least the
square of the residue characteristic.
-/

noncomputable section

namespace Anabelian.LCFT

open OTriangle ValuativeRel

universe u

noncomputable def integerUnitTorsionFreeToFieldTorsionFree
    (K : PointedMixedCharLocalField.{u}) :
    IntegerUnitTorsionFreeQuotient K →* FieldTorsionFreeQuotient K :=
  let U := (valuation K).valuationSubring.unitGroup
  QuotientGroup.lift (CommGroup.torsion U)
    ((QuotientGroup.mk' (CommGroup.torsion Kˣ)).comp U.subtype) (by
      intro x hx
      rw [MonoidHom.mem_ker]
      change (((x : U) : Kˣ) : FieldTorsionFreeQuotient K) = 1
      rw [QuotientGroup.eq_one_iff]
      exact U.subtype.isOfFinOrder hx)

theorem integerUnitTorsionFreeToFieldTorsionFree_injective
    (K : PointedMixedCharLocalField.{u}) :
    Function.Injective (integerUnitTorsionFreeToFieldTorsionFree K) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext q
  simp only [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · intro hq
    let U := (valuation K).valuationSubring.unitGroup
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective
      (CommGroup.torsion U) q
    change (((u : U) : Kˣ) : FieldTorsionFreeQuotient K) = 1 at hq
    have hufield : IsOfFinOrder ((u : U) : Kˣ) := by
      exact (QuotientGroup.eq_one_iff _).mp hq
    have hu : IsOfFinOrder u := by
      obtain ⟨n, hn, hpow⟩ := hufield.exists_pow_eq_one
      apply isOfFinOrder_iff_pow_eq_one.mpr
      refine ⟨n, hn, ?_⟩
      apply Subtype.ext
      exact hpow
    exact (QuotientGroup.eq_one_iff _).mpr hu
  · intro hq
    rw [hq, map_one]

abbrev IntegerUnitTorsionFreeModPowerQuotient
    (K : PointedMixedCharLocalField.{u}) :=
  IntegerUnitTorsionFreeQuotient K ⧸
    (powMonoidHom (α := IntegerUnitTorsionFreeQuotient K)
      K.residueChar).range

noncomputable def integerUnitModPowerToFieldModPowerTorsionFree
    (K : PointedMixedCharLocalField.{u}) :
    IntegerUnitTorsionFreeModPowerQuotient K →*
      FieldTorsionFreeModPowerQuotient K K.residueChar :=
  QuotientGroup.map
    (powMonoidHom (α := IntegerUnitTorsionFreeQuotient K)
      K.residueChar).range
    (powMonoidHom (α := FieldTorsionFreeQuotient K)
      K.residueChar).range
    (integerUnitTorsionFreeToFieldTorsionFree K) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨integerUnitTorsionFreeToFieldTorsionFree K x, by simp⟩)

theorem integerUnitModPowerToFieldModPowerTorsionFree_injective
    (K : PointedMixedCharLocalField.{u}) :
    Function.Injective
      (integerUnitModPowerToFieldModPowerTorsionFree K) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext q
  simp only [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · intro hq
    let U := (valuation K).valuationSubring.unitGroup
    let UQ := IntegerUnitTorsionFreeQuotient K
    let FQ := FieldTorsionFreeQuotient K
    let qU : U →* UQ := QuotientGroup.mk' (CommGroup.torsion U)
    let qF : Kˣ →* FQ := QuotientGroup.mk' (CommGroup.torsion Kˣ)
    obtain ⟨uq, rfl⟩ := QuotientGroup.mk'_surjective
      (powMonoidHom (α := UQ) K.residueChar).range q
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective
      (CommGroup.torsion U) uq
    change (((qF (u : Kˣ)) : FQ) :
      FieldTorsionFreeModPowerQuotient K K.residueChar) = 1 at hq
    have hpowmem : qF (u : Kˣ) ∈
        (powMonoidHom (α := FQ) K.residueChar).range := by
      rwa [← QuotientGroup.eq_one_iff]
    obtain ⟨xq, hxq⟩ := hpowmem
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (CommGroup.torsion Kˣ) xq
    change qF (x ^ K.residueChar) = qF (u : Kˣ) at hxq
    have htorField : x ^ K.residueChar * (u : Kˣ)⁻¹ ∈
        CommGroup.torsion Kˣ := by
      have hdiv : x ^ K.residueChar / (u : Kˣ) ∈
          CommGroup.torsion Kˣ := by
        rw [← QuotientGroup.eq_iff_div_mem]
        exact hxq
      simpa [div_eq_mul_inv] using hdiv
    have hvaltor := valuation_eq_one_of_isOfFinOrder K _ htorField
    have huval : valuation K ((u : U) : Kˣ) = 1 :=
      (Valuation.mem_unitGroup_iff K (valuation K) (u : Kˣ)).mp u.property
    simp only [Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_inv_eq_inv_val] at hvaltor
    rw [map_mul, map_pow] at hvaltor
    have huinv : valuation K ((((u : U) : Kˣ) : K)⁻¹) = 1 := by
      rw [(valuation K).map_inv, huval, inv_one]
    rw [huinv, mul_one] at hvaltor
    have hxval : valuation K (x : K) = 1 := by
      apply pow_left_injective (Fact.out : K.residueChar.Prime).ne_zero
      simpa using hvaltor
    let xu : U :=
      ⟨x, (Valuation.mem_unitGroup_iff K (valuation K) x).mpr hxval⟩
    have htorUnit : xu ^ K.residueChar * u⁻¹ ∈ CommGroup.torsion U := by
      obtain ⟨n, hn, hpow⟩ := htorField.exists_pow_eq_one
      apply isOfFinOrder_iff_pow_eq_one.mpr
      refine ⟨n, hn, ?_⟩
      apply Subtype.ext
      exact hpow
    have heqUQ : qU (xu ^ K.residueChar) = qU u := by
      change ((xu ^ K.residueChar : U) : UQ) = (u : UQ)
      rw [QuotientGroup.eq_iff_div_mem]
      simpa [div_eq_mul_inv] using htorUnit
    have huPow : qU u ∈
        (powMonoidHom (α := UQ) K.residueChar).range := by
      refine ⟨qU xu, ?_⟩
      change (qU xu) ^ K.residueChar = qU u
      rw [← map_pow]
      exact heqUQ
    change ((qU u : UQ) : IntegerUnitTorsionFreeModPowerQuotient K) = 1
    exact (QuotientGroup.eq_one_iff _).mpr huPow
  · intro hq
    rw [hq, map_one]

noncomputable def fieldDiscreteValuationModRaw
    (K : PointedMixedCharLocalField.{u}) :
    Kˣ →* Multiplicative (ZMod K.residueChar) :=
  (Int.castAddHom (ZMod K.residueChar)).toMultiplicative.comp
    (fieldUnitDiscreteValuation K)

noncomputable def fieldTorsionFreeDiscreteValuationMod
    (K : PointedMixedCharLocalField.{u}) :
    FieldTorsionFreeQuotient K →* Multiplicative (ZMod K.residueChar) :=
  QuotientGroup.lift (CommGroup.torsion Kˣ)
    (fieldDiscreteValuationModRaw K) (by
      intro x hx
      rw [MonoidHom.mem_ker]
      simp only [fieldDiscreteValuationModRaw, MonoidHom.coe_comp,
        Function.comp_apply]
      rw [fieldUnitDiscreteValuation_eq_one_of_isOfFinOrder K x hx, map_one])

noncomputable def fieldModPowerDiscreteValuationMod
    (K : PointedMixedCharLocalField.{u}) :
    FieldTorsionFreeModPowerQuotient K K.residueChar →*
      Multiplicative (ZMod K.residueChar) :=
  QuotientGroup.lift
    (powMonoidHom (α := FieldTorsionFreeQuotient K) K.residueChar).range
    (fieldTorsionFreeDiscreteValuationMod K) (by
      intro x hx
      obtain ⟨y, rfl⟩ := hx
      rw [MonoidHom.mem_ker]
      change fieldTorsionFreeDiscreteValuationMod K
        (y ^ K.residueChar) = 1
      rw [map_pow]
      apply Multiplicative.toAdd.injective
      change K.residueChar •
        (fieldTorsionFreeDiscreteValuationMod K y).toAdd = 0
      change K.residueChar •
        ((fieldTorsionFreeDiscreteValuationMod K y).toAdd :
          ZMod K.residueChar) = 0
      simpa [nsmul_eq_mul])

theorem fieldModPowerDiscreteValuationMod_surjective
    (K : PointedMixedCharLocalField.{u}) :
    Function.Surjective (fieldModPowerDiscreteValuationMod K) := by
  intro y
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective y.toAdd
  let Q := FieldTorsionFreeQuotient K
  let QP := FieldTorsionFreeModPowerQuotient K K.residueChar
  refine ⟨((((uniformizerUnit K) ^ (-z) : Kˣ) : Q) : QP), ?_⟩
  change fieldDiscreteValuationModRaw K
    ((uniformizerUnit K) ^ (-z)) = y
  apply Multiplicative.toAdd.injective
  simp only [fieldDiscreteValuationModRaw, MonoidHom.coe_comp,
    Function.comp_apply, map_zpow,
    fieldUnitDiscreteValuation_uniformizer]
  rw [toAdd_zpow]
  change (-z) • ((-1 : ℤ) : ZMod K.residueChar) = y.toAdd
  simpa [zsmul_eq_mul] using hz

theorem fieldModPowerDiscreteValuationMod_integerUnit
    (K : PointedMixedCharLocalField.{u})
    (q : IntegerUnitTorsionFreeModPowerQuotient K) :
    fieldModPowerDiscreteValuationMod K
      (integerUnitModPowerToFieldModPowerTorsionFree K q) = 1 := by
  let U := (valuation K).valuationSubring.unitGroup
  let UQ := IntegerUnitTorsionFreeQuotient K
  obtain ⟨uq, rfl⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom (α := UQ) K.residueChar).range q
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective
    (CommGroup.torsion U) uq
  change fieldDiscreteValuationModRaw K (u : Kˣ) = 1
  have huval : valuation K (((u : U) : Kˣ) : K) = 1 :=
    (Valuation.mem_unitGroup_iff K (valuation K) (u : Kˣ)).mp u.property
  have hfieldVal : fieldUnitValuation K (u : Kˣ) = 1 := by
    apply Units.ext
    exact huval
  simp only [fieldDiscreteValuationModRaw, MonoidHom.coe_comp,
    Function.comp_apply, fieldUnitDiscreteValuation]
  rw [hfieldVal, map_one, map_one]

theorem integerUnitTorsionFreeModPowerQuotient_card_ge_residueChar
    (K : PointedMixedCharLocalField.{u}) :
    K.residueChar ≤
      Nat.card (IntegerUnitTorsionFreeModPowerQuotient K) := by
  let UMP := IntegerUnitTorsionFreeModPowerQuotient K
  let FMP := FieldTorsionFreeModPowerQuotient K K.residueChar
  haveI : Finite FMP :=
    fieldTorsionFreeModPowerQuotient_residueChar_finite K
  haveI : Finite UMP := Finite.of_injective
    (integerUnitModPowerToFieldModPowerTorsionFree K)
    (integerUnitModPowerToFieldModPowerTorsionFree_injective K)
  haveI : Nontrivial UMP :=
    integerUnitTorsionFreeModPowerQuotient_residueChar_nontrivial K
  obtain ⟨g : UMP, hg⟩ := exists_ne (1 : UMP)
  have hgpow : g ^ K.residueChar = 1 := by
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective
      (powMonoidHom (α := IntegerUnitTorsionFreeQuotient K)
        K.residueChar).range g
    change (((q ^ K.residueChar : IntegerUnitTorsionFreeQuotient K) :
      UMP)) = 1
    rw [QuotientGroup.eq_one_iff]
    exact ⟨q, rfl⟩
  have horddvd : orderOf g ∣ K.residueChar :=
    orderOf_dvd_of_pow_eq_one hgpow
  have hord : orderOf g = K.residueChar := by
    rcases (Nat.dvd_prime (Fact.out : K.residueChar.Prime)).mp horddvd with
      hone | hp
    · exact (hg (orderOf_eq_one_iff.mp hone)).elim
    · exact hp
  rw [← hord]
  exact orderOf_le_card

theorem fieldTorsionFreeModPowerQuotient_card_ge_residueChar_sq
    (K : PointedMixedCharLocalField.{u}) :
    K.residueChar ^ 2 ≤
      Nat.card (FieldTorsionFreeModPowerQuotient K K.residueChar) := by
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
  have hs : Function.Surjective f :=
    fieldModPowerDiscreteValuationMod_surjective K
  let iKer : UMP → f.ker := fun q ↦
    ⟨i q, fieldModPowerDiscreteValuationMod_integerUnit K q⟩
  have hiKer : Function.Injective iKer := by
    intro a b hab
    apply hi
    exact congrArg Subtype.val hab
  have hunitKer : Nat.card UMP ≤ Nat.card f.ker :=
    Finite.card_le_of_embedding ⟨iKer, hiKer⟩
  have hker : K.residueChar ≤ Nat.card f.ker :=
    (integerUnitTorsionFreeModPowerQuotient_card_ge_residueChar K).trans
      hunitKer
  have hrange : Nat.card f.range = K.residueChar := by
    rw [f.range_eq_top_of_surjective hs, Subgroup.card_top]
    exact (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod _)
  rw [pow_two]
  calc
    K.residueChar * K.residueChar ≤ Nat.card f.ker * K.residueChar :=
      Nat.mul_le_mul_right K.residueChar hker
    _ = Nat.card f.ker * Nat.card f.range := by rw [hrange]
    _ = Nat.card FMP := by
      rw [← Subgroup.index_ker f]
      exact f.ker.card_mul_index


end Anabelian.LCFT

