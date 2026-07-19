import Otriangle.MonoAnabelian.ResidueCharacteristicFieldRank
import Otriangle.MonoAnabelian.ReciprocityRank
import Otriangle.MonoAnabelian.ResidueTorsionFree
import Mathlib.GroupTheory.Index

/-!
# Residue-characteristic rank transported by local reciprocity

The unit direction in the torsion-free mod-`p` quotient remains nontrivial after applying local
reciprocity.  Torsion-freeness of the residue absolute Galois group is the key point: a putative
root of an inertial class has torsion unramified projection, hence is itself inertial and comes
from a local unit.
-/

noncomputable section

namespace Anabelian.LCFT

open OTriangle ValuativeRel

universe u

/-- The residue-characteristic unit quotient mapped into the corresponding abelianized Galois
quotient by local reciprocity. -/
noncomputable def integerUnitModPowerToAbelianizedModPower
    {K : PointedMixedCharLocalField.{u}} (rec : LocalReciprocityMap K) :
    IntegerUnitTorsionFreeModPowerQuotient K →*
      AbelianizedTorsionFreeModPowerQuotient K K.residueChar :=
  (reciprocityModPowerMap rec K.residueChar).comp
    (integerUnitModPowerToFieldModPowerTorsionFree K)

/-- Local reciprocity does not collapse the residue-characteristic unit direction modulo
torsion and `p`th powers. -/
theorem integerUnitModPowerToAbelianizedModPower_injective
    {K : PointedMixedCharLocalField.{u}} (rec : LocalReciprocityMap K) :
    Function.Injective (integerUnitModPowerToAbelianizedModPower rec) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext q
  simp only [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · intro hq
    let A := (valuation K).valuationSubring
    let U := A.unitGroup
    let UQ := IntegerUnitTorsionFreeQuotient K
    let B := AbelianizedAbsoluteGaloisGroup K
    let BT := AbelianizedTorsionFreeQuotient K
    let qU : U →* UQ := QuotientGroup.mk' (CommGroup.torsion U)
    let qB : B →* BT := QuotientGroup.mk' (CommGroup.torsion B)
    obtain ⟨uq, rfl⟩ := QuotientGroup.mk'_surjective
      (powMonoidHom (α := UQ) K.residueChar).range q
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective
      (CommGroup.torsion U) uq
    change ((((qB (rec.toMonoidHom (u : Kˣ)) : BT) : BT) :
      AbelianizedTorsionFreeModPowerQuotient K K.residueChar)) = 1 at hq
    have hpowmem : qB (rec.toMonoidHom (u : Kˣ)) ∈
        (powMonoidHom (α := BT) K.residueChar).range := by
      rwa [← QuotientGroup.eq_one_iff]
    obtain ⟨bq, hbq⟩ := hpowmem
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective
      (CommGroup.torsion B) bq
    change qB (b ^ K.residueChar) =
      qB (rec.toMonoidHom (u : Kˣ)) at hbq
    have htorB : b ^ K.residueChar *
        (rec.toMonoidHom (u : Kˣ))⁻¹ ∈ CommGroup.torsion B := by
      rw [← QuotientGroup.eq_one_iff]
      change qB (b ^ K.residueChar *
        (rec.toMonoidHom (u : Kˣ))⁻¹) = 1
      rw [map_mul, map_inv, hbq, mul_inv_cancel]
    have hrecUnit : rec.toMonoidHom (u : Kˣ) ∈ inertiaSubgroup K := by
      let uA : Aˣ := A.unitGroupMulEquiv u
      apply integerUnitSubgroup_le_comap_inertia rec.mapsUnits
      refine ⟨uA, ?_⟩
      apply Units.ext
      rfl
    have hrecProj : unramifiedProjection K
        (rec.toMonoidHom (u : Kˣ)) = 1 :=
      (unramifiedProjection_eq_one_iff K _).mpr hrecUnit
    have hprojPowFinite : IsOfFinOrder
        ((unramifiedProjection K b) ^ K.residueChar) := by
      have hmap := (unramifiedProjection K).isOfFinOrder htorB
      simpa [map_mul, map_pow, map_inv, hrecProj] using hmap
    have hprojFinite : IsOfFinOrder (unramifiedProjection K b) :=
      hprojPowFinite.of_pow (Fact.out : K.residueChar.Prime).ne_zero
    have hproj : unramifiedProjection K b = 1 :=
      residueAbsoluteGaloisGroup_isOfFinOrder_eq_one K _ hprojFinite
    have hbInertia : b ∈ inertiaSubgroup K :=
      (unramifiedProjection_eq_one_iff K b).mp hproj
    obtain ⟨vA, hv⟩ := rec.mapsUnits.unitsEquiv.surjective ⟨b, hbInertia⟩
    let v : U := A.unitGroupMulEquiv.symm vA
    have hvField : integerUnitsToFieldUnits K vA = (v : Kˣ) := by
      apply Units.ext
      rfl
    have hrecV : rec.toMonoidHom (v : Kˣ) = b := by
      calc
        rec.toMonoidHom (v : Kˣ) =
            rec.toMonoidHom (integerUnitsToFieldUnits K vA) :=
          congrArg rec.toMonoidHom hvField.symm
        _ = b := by
          have hcompat := DFunLike.congr_fun rec.mapsUnits.compatibility vA
          exact hcompat.symm.trans (congrArg Subtype.val hv)
    let z : Kˣ := (v : Kˣ) ^ K.residueChar * (u : Kˣ)⁻¹
    have hrecZFinite : IsOfFinOrder (rec.toMonoidHom z) := by
      change IsOfFinOrder
        (rec.toMonoidHom ((v : Kˣ) ^ K.residueChar * (u : Kˣ)⁻¹))
      rw [map_mul, map_pow, map_inv, hrecV]
      exact htorB
    have hzFinite : IsOfFinOrder z := by
      obtain ⟨m, hm, hpow⟩ := hrecZFinite.exists_pow_eq_one
      apply isOfFinOrder_iff_pow_eq_one.mpr
      refine ⟨m, hm, rec.injective ?_⟩
      rw [map_pow, hpow, map_one]
    let zu : U := ⟨z, by
      rw [Valuation.mem_unitGroup_iff]
      have hvval : valuation K ((v : U) : Kˣ) = 1 :=
        (Valuation.mem_unitGroup_iff K (valuation K) (v : Kˣ)).mp v.property
      have huval : valuation K ((u : U) : Kˣ) = 1 :=
        (Valuation.mem_unitGroup_iff K (valuation K) (u : Kˣ)).mp u.property
      change valuation K
        ((((v : Kˣ) ^ K.residueChar * (u : Kˣ)⁻¹ : Kˣ) : K)) = 1
      simp only [Units.val_mul, Units.val_pow_eq_pow_val,
        Units.val_inv_eq_inv_val]
      rw [map_mul, map_pow]
      rw [hvval, (valuation K).map_inv, huval]
      simp⟩
    have hzuFinite : IsOfFinOrder zu := by
      obtain ⟨m, hm, hpow⟩ := hzFinite.exists_pow_eq_one
      apply isOfFinOrder_iff_pow_eq_one.mpr
      refine ⟨m, hm, ?_⟩
      apply Subtype.ext
      exact hpow
    have heqUQ : qU (v ^ K.residueChar) = qU u := by
      change ((v ^ K.residueChar : U) : UQ) = (u : UQ)
      rw [QuotientGroup.eq_iff_div_mem]
      rw [div_eq_mul_inv]
      have hzuEq : zu = v ^ K.residueChar * u⁻¹ := by
        apply Subtype.ext
        rfl
      rw [← hzuEq]
      exact hzuFinite
    change ((qU u : UQ) : IntegerUnitTorsionFreeModPowerQuotient K) = 1
    rw [QuotientGroup.eq_one_iff]
    refine ⟨qU v, ?_⟩
    change qU v ^ K.residueChar = qU u
    rw [← map_pow, heqUQ]
  · intro hq
    rw [hq, map_one]

/-- The residue-characteristic unramified projection on the abelianized mod-power quotient is
surjective. -/
theorem abelianizedModPowerToResidue_residueChar_surjective
    {K : PointedMixedCharLocalField.{u}} (rec : LocalReciprocityMap K) :
    Function.Surjective
      (abelianizedModPowerToResidue K K.residueChar) := by
  let RMP := ResidueTorsionFreeModPowerQuotient K K.residueChar
  let g : RMP := residueFrobeniusModPower K K.residueChar
  have hcard : Nat.card RMP = K.residueChar :=
    residueTorsionFreeModPowerQuotient_card_eq_prime K K.residueChar Fact.out
  have htop : Subgroup.zpowers g = ⊤ :=
    zpowers_eq_top_of_prime_card hcard
      (residueFrobeniusModPower_ne_one K K.residueChar Fact.out)
  intro y
  have hy : y ∈ Subgroup.zpowers g := by
    rw [htop]
    exact Subgroup.mem_top y
  obtain ⟨n, hn⟩ := hy
  refine ⟨(abelianizedUniformizerModPower rec K.residueChar) ^ n, ?_⟩
  rw [map_zpow, abelianizedModPowerToResidue_uniformizer]
  exact hn

/-- Local-unit classes lie in the kernel of the residue projection after applying local
reciprocity. -/
theorem abelianizedModPowerToResidue_integerUnit
    {K : PointedMixedCharLocalField.{u}} (rec : LocalReciprocityMap K)
    (q : IntegerUnitTorsionFreeModPowerQuotient K) :
    abelianizedModPowerToResidue K K.residueChar
      (integerUnitModPowerToAbelianizedModPower rec q) = 1 := by
  let A := (valuation K).valuationSubring
  let U := A.unitGroup
  let UQ := IntegerUnitTorsionFreeQuotient K
  obtain ⟨uq, rfl⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom (α := UQ) K.residueChar).range q
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective
    (CommGroup.torsion U) uq
  change (((unramifiedProjection K (rec.toMonoidHom (u : Kˣ)) :
    ResidueAbsoluteGaloisGroup K) : ResidueTorsionFreeQuotient K) :
      ResidueTorsionFreeModPowerQuotient K K.residueChar) = 1
  have hrecUnit : rec.toMonoidHom (u : Kˣ) ∈ inertiaSubgroup K := by
    let uA : Aˣ := A.unitGroupMulEquiv u
    apply integerUnitSubgroup_le_comap_inertia rec.mapsUnits
    refine ⟨uA, ?_⟩
    apply Units.ext
    rfl
  rw [(unramifiedProjection_eq_one_iff K _).mpr hrecUnit]
  simp

/-- At the residue characteristic, the torsion-free abelianized Galois quotient has at least
two mod-power directions. -/
theorem abelianizedTorsionFreeModPowerQuotient_card_ge_residueChar_sq
    {K : PointedMixedCharLocalField.{u}} (rec : LocalReciprocityMap K) :
    K.residueChar ^ 2 ≤ Nat.card
      (AbelianizedTorsionFreeModPowerQuotient K K.residueChar) := by
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
  have hs : Function.Surjective f :=
    abelianizedModPowerToResidue_residueChar_surjective rec
  haveI : Finite UMP := Finite.of_injective i hi
  let iKer : UMP → f.ker := fun q =>
    ⟨i q, abelianizedModPowerToResidue_integerUnit rec q⟩
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
    exact residueTorsionFreeModPowerQuotient_card_eq_prime
      K K.residueChar Fact.out
  rw [pow_two]
  calc
    K.residueChar * K.residueChar ≤ Nat.card f.ker * K.residueChar :=
      Nat.mul_le_mul_right K.residueChar hker
    _ = Nat.card f.ker * Nat.card f.range := by rw [hrange]
    _ = Nat.card BMP := by
      rw [← Subgroup.index_ker f]
      exact f.ker.card_mul_index

end Anabelian.LCFT
