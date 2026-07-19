import Otriangle.MonoAnabelian.PrimeToTorsionUnits
import Otriangle.MonoAnabelian.OneField
import Otriangle.MonoAnabelian.ResidueTorsionFree

/-!
# Prime-to-residue-characteristic torsion after reciprocity

Finite-order classes in the abelianized absolute Galois group have trivial unramified
projection, hence lie in inertia.  The unit part of local reciprocity therefore identifies all
abelianized torsion with local-unit torsion.  Combined with the reduction calculation, this is
Hoshi's formula `1 + |(G_K^ab)_tors/(p-primary)| = p^f`.
-/

noncomputable section

namespace Anabelian.LCFT

open OTriangle ValuativeRel

universe u

/-- Local reciprocity restricted from torsion units to torsion in the abelianized Galois group. -/
noncomputable def integerUnitTorsionToAbelianizedTorsion
    {K : PointedMixedCharLocalField.{u}} (rec : LocalReciprocityMap K) :
    CommGroup.torsion (valuation K).valuationSubring.unitGroup →*
      CommGroup.torsion (AbelianizedAbsoluteGaloisGroup K) where
  toFun t := ⟨rec.toMonoidHom (t.1 : Kˣ),
    rec.toMonoidHom.isOfFinOrder
      ((valuation K).valuationSubring.unitGroup.subtype.isOfFinOrder t.2)⟩
  map_one' := by
    apply Subtype.ext
    exact map_one rec.toMonoidHom
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul rec.toMonoidHom (x.1 : Kˣ) (y.1 : Kˣ)

/-- Reciprocity gives an equivalence between torsion local units and all torsion in the
abelianized absolute Galois group. -/
noncomputable def integerUnitTorsionEquivAbelianizedTorsion
    {K : PointedMixedCharLocalField.{u}} (rec : LocalReciprocityMap K) :
    CommGroup.torsion (valuation K).valuationSubring.unitGroup ≃*
      CommGroup.torsion (AbelianizedAbsoluteGaloisGroup K) := by
  let A := (valuation K).valuationSubring
  let U := A.unitGroup
  let B := AbelianizedAbsoluteGaloisGroup K
  let f := integerUnitTorsionToAbelianizedTorsion rec
  apply MulEquiv.ofBijective f
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply rec.injective
    exact congrArg (fun z : CommGroup.torsion B ↦ z.1) hxy
  · intro b
    have hprojFinite : IsOfFinOrder (unramifiedProjection K b.1) :=
      (unramifiedProjection K).isOfFinOrder b.2
    have hproj : unramifiedProjection K b.1 = 1 :=
      residueAbsoluteGaloisGroup_isOfFinOrder_eq_one K _ hprojFinite
    have hbInertia : b.1 ∈ inertiaSubgroup K :=
      (unramifiedProjection_eq_one_iff K b.1).mp hproj
    obtain ⟨a, ha⟩ := rec.mapsUnits.unitsEquiv.surjective ⟨b.1, hbInertia⟩
    let u : U := A.unitGroupMulEquiv.symm a
    have huField : integerUnitsToFieldUnits K a = (u : Kˣ) := by
      apply Units.ext
      rfl
    have hrec : rec.toMonoidHom (u : Kˣ) = b.1 := by
      calc
        rec.toMonoidHom (u : Kˣ) =
            rec.toMonoidHom (integerUnitsToFieldUnits K a) :=
          congrArg rec.toMonoidHom huField.symm
        _ = b.1 := by
          have hcompat := DFunLike.congr_fun rec.mapsUnits.compatibility a
          exact hcompat.symm.trans (congrArg Subtype.val ha)
    have huFinite : IsOfFinOrder u := by
      obtain ⟨n, hn, hbn⟩ := b.2.exists_pow_eq_one
      apply isOfFinOrder_iff_pow_eq_one.mpr
      refine ⟨n, hn, ?_⟩
      apply Subtype.ext
      apply rec.injective
      change rec.toMonoidHom ((u : Kˣ) ^ n) = rec.toMonoidHom (1 : Kˣ)
      rw [map_pow, hrec, hbn, map_one]
    refine ⟨⟨u, huFinite⟩, ?_⟩
    apply Subtype.ext
    exact hrec

/-- The prime-to-`p` torsion quotients of units and abelianized Galois are equivalent. -/
noncomputable def integerUnitPrimeToTorsionQuotientEquivAbelianized
    {K : PointedMixedCharLocalField.{u}} (rec : LocalReciprocityMap K) :
    OTriangle.GroupTheoreticInvariants.primeToTorsionQuotient
        (valuation K).valuationSubring.unitGroup K.residueChar ≃*
      OTriangle.GroupTheoreticInvariants.primeToTorsionQuotient
        (AbelianizedAbsoluteGaloisGroup K) K.residueChar :=
  let e := integerUnitTorsionEquivAbelianizedTorsion rec
  QuotientGroup.congr
    (CommGroup.primaryComponent
      (CommGroup.torsion (valuation K).valuationSubring.unitGroup) K.residueChar)
    (CommGroup.primaryComponent
      (CommGroup.torsion (AbelianizedAbsoluteGaloisGroup K)) K.residueChar)
    e (OTriangle.GroupTheoreticInvariants.map_primaryComponent e K.residueChar)

/-- Hoshi's exact prime-to-residue-characteristic torsion formula on the abelianized local
Galois group. -/
theorem one_add_abelianizedPrimeToTorsionQuotient_card_eq_residueChar_pow_residueDegree
    {K : PointedMixedCharLocalField.{u}} (rec : LocalReciprocityMap K) :
    1 + Nat.card
        (OTriangle.GroupTheoreticInvariants.primeToTorsionQuotient
          (AbelianizedAbsoluteGaloisGroup K) K.residueChar) =
      K.residueChar ^ localResidueDegree K := by
  rw [← Nat.card_congr
    (integerUnitPrimeToTorsionQuotientEquivAbelianized rec).toEquiv]
  exact one_add_integerUnitPrimeToTorsionQuotient_card K

end Anabelian.LCFT
