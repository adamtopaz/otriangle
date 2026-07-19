import Otriangle.MonoAnabelian.ExactUnitRank
import Otriangle.MonoAnabelian.PrincipalUnits
import Mathlib.Data.Nat.Factors
import Mathlib.FieldTheory.Perfect

/-!
# Prime-to-residue-characteristic torsion of local units

Hoshi's residue-degree invariant is the cardinality of the prime-to-`p` part of torsion in
the abelianized Galois group.  This file performs the local-unit calculation behind that
invariant.  Reduction identifies prime-to-`p` torsion in the valuation-ring unit group with
the multiplicative group of the residue field.
-/

noncomputable section

namespace Anabelian.LCFT

open OTriangle ValuativeRel

universe u

/-- Torsion in the principal-unit group is finite. -/
theorem principalUnitGroup_torsion_finite
    (K : PointedMixedCharLocalField.{u}) :
    Finite (CommGroup.torsion
      (valuation K).valuationSubring.principalUnitGroup) := by
  let A := (valuation K).valuationSubring
  let P := A.principalUnitGroup
  let U := A.unitGroup
  let i : CommGroup.torsion P → CommGroup.torsion U := fun t ↦
    ⟨⟨t.1, A.principal_units_le_units t.1.property⟩, by
      obtain ⟨n, hn, ht⟩ := t.2.exists_pow_eq_one
      apply isOfFinOrder_iff_pow_eq_one.mpr
      refine ⟨n, hn, ?_⟩
      apply Subtype.ext
      exact congrArg (fun z : P ↦ (z : Kˣ)) ht⟩
  have hi : Function.Injective i := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : CommGroup.torsion U ↦ ((z.1 : U) : Kˣ)) hab
  let eU : U ≃* (LocalIntegerRing K)ˣ := A.unitGroupMulEquiv
  haveI : Finite (CommGroup.torsion (LocalIntegerRing K)ˣ) :=
    integerRingUnits_torsion_finite K
  haveI : Finite (CommGroup.torsion U) :=
    Finite.of_equiv (CommGroup.torsion (LocalIntegerRing K)ˣ)
      (OTriangle.GroupTheoreticInvariants.torsionEquiv eU).symm.toEquiv
  exact Finite.of_injective i hi

/-- On finite-order principal units, every prime-to-`p` prime-power map is injective. -/
theorem principalUnitTorsion_pow_injective_of_ne_residueChar
    (K : PointedMixedCharLocalField.{u}) (l : ℕ) (hl : l.Prime)
    (hne : l ≠ K.residueChar) :
    Function.Injective
      (powMonoidHom
        (α := CommGroup.torsion
          (valuation K).valuationSubring.principalUnitGroup) l) := by
  let A := (valuation K).valuationSubring
  let P := A.principalUnitGroup
  let T := CommGroup.torsion P
  haveI : Finite T := principalUnitGroup_torsion_finite K
  rw [Finite.injective_iff_surjective]
  intro t
  obtain ⟨z, hz⟩ := principalUnit_pow_surjective_of_ne_residueChar K l hl hne t.1
  have hzfin : IsOfFinOrder z := by
    change z ^ l = t.1 at hz
    have : IsOfFinOrder (z ^ l) := by rw [hz]; exact t.2
    exact this.of_pow hl.ne_zero
  refine ⟨⟨z, hzfin⟩, ?_⟩
  apply Subtype.ext
  exact hz

/-- Every torsion principal unit has `p`-power order. -/
theorem principalUnitTorsion_orderOf_eq_residueChar_pow
    (K : PointedMixedCharLocalField.{u})
    (t : CommGroup.torsion
      (valuation K).valuationSubring.principalUnitGroup) :
    ∃ n : ℕ, orderOf t = K.residueChar ^ n := by
  have ht0 : orderOf t ≠ 0 :=
    orderOf_ne_zero_iff.mpr (CommMonoid.torsion.isTorsion t)
  refine ⟨(orderOf t).primeFactorsList.length,
    Nat.eq_prime_pow_of_unique_prime_dvd ht0 ?_⟩
  intro l hl hldvd
  by_contra hne
  let y : CommGroup.torsion
      (valuation K).valuationSubring.principalUnitGroup :=
    t ^ (orderOf t / l)
  have hyorder : orderOf y = l := orderOf_pow_orderOf_div ht0 hldvd
  have hinj := principalUnitTorsion_pow_injective_of_ne_residueChar K l hl hne
  have hyl : y ^ l = 1 := by
    rw [← hyorder]
    exact pow_orderOf_eq_one y
  have hy : y = 1 := hinj (by simpa using hyl)
  have : l = 1 := by rw [← hyorder, hy, orderOf_one]
  exact hl.ne_one this

/-- A torsion principal unit belongs to the residue-characteristic primary component. -/
theorem principalUnitTorsion_mem_primaryComponent
    (K : PointedMixedCharLocalField.{u})
    (t : CommGroup.torsion
      (valuation K).valuationSubring.principalUnitGroup) :
    t ∈ CommGroup.primaryComponent
      (CommGroup.torsion
        (valuation K).valuationSubring.principalUnitGroup) K.residueChar := by
  rw [CommGroup.mem_primaryComponent_iff_orderOf]
  exact principalUnitTorsion_orderOf_eq_residueChar_pow K t

/-- Reduction of valuation-ring units, restricted to their torsion subgroup. -/
noncomputable def integerUnitTorsionReduction
    (K : PointedMixedCharLocalField.{u}) :
    CommGroup.torsion (valuation K).valuationSubring.unitGroup →*
      (LocalResidueField K)ˣ :=
  (valuation K).valuationSubring.unitGroupToResidueFieldUnits.comp
    (CommGroup.torsion (valuation K).valuationSubring.unitGroup).subtype

/-- Every nonzero residue class is the reduction of a torsion unit. -/
theorem integerUnitTorsionReduction_surjective
    (K : PointedMixedCharLocalField.{u}) :
    Function.Surjective (integerUnitTorsionReduction K) := by
  intro b
  obtain ⟨t, ht, hred⟩ := residueUnit_has_torsion_lift K b
  exact ⟨⟨t, ht⟩, hred⟩

/-- A residue-field unit killed by a power of the residue characteristic is trivial. -/
theorem residueUnit_eq_one_of_residueChar_pow_eq_one
    (K : PointedMixedCharLocalField.{u})
    (b : (LocalResidueField K)ˣ) (n : ℕ)
    (hb : b ^ K.residueChar ^ n = 1) : b = 1 := by
  apply Units.ext
  apply (injective_frobenius (LocalResidueField K) K.residueChar).iterate n
  simpa only [iterate_frobenius, Units.val_pow_eq_pow_val, Units.val_one, one_pow] using
    congrArg Units.val hb

/-- The kernel of torsion-unit reduction is exactly its residue-characteristic primary
component. -/
theorem integerUnitTorsionReduction_ker
    (K : PointedMixedCharLocalField.{u}) :
    (integerUnitTorsionReduction K).ker =
      CommGroup.primaryComponent
        (CommGroup.torsion (valuation K).valuationSubring.unitGroup)
        K.residueChar := by
  let A := (valuation K).valuationSubring
  let U := A.unitGroup
  let P := A.principalUnitGroup
  let T := CommGroup.torsion U
  ext t
  constructor
  · intro ht
    rw [MonoidHom.mem_ker] at ht
    have htKer : t.1 ∈ A.unitGroupToResidueFieldUnits.ker := ht
    rw [A.ker_unitGroupToResidueFieldUnits] at htKer
    let v : P := ⟨(t.1 : Kˣ), htKer⟩
    let vt : CommGroup.torsion P := ⟨v, by
        obtain ⟨m, hm, htm⟩ := t.2.exists_pow_eq_one
        apply isOfFinOrder_iff_pow_eq_one.mpr
        refine ⟨m, hm, ?_⟩
        apply Subtype.ext
        exact congrArg (fun z : U ↦ (z : Kˣ)) htm⟩
    have hvt := principalUnitTorsion_mem_primaryComponent K vt
    rw [CommGroup.mem_primaryComponent] at hvt
    obtain ⟨n, hvpow⟩ := hvt
    rw [CommGroup.mem_primaryComponent]
    refine ⟨n, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : CommGroup.torsion P ↦ ((z.1 : P) : Kˣ)) hvpow
  · intro ht
    rw [CommGroup.mem_primaryComponent] at ht
    obtain ⟨n, hn⟩ := ht
    rw [MonoidHom.mem_ker]
    apply residueUnit_eq_one_of_residueChar_pow_eq_one K _ n
    rw [← map_pow]
    exact congrArg (integerUnitTorsionReduction K) hn

/-- Reduction identifies the prime-to-`p` torsion quotient of local units with the residue
field's multiplicative group. -/
noncomputable def integerUnitPrimeToTorsionQuotientEquivResidueUnits
    (K : PointedMixedCharLocalField.{u}) :
    OTriangle.GroupTheoreticInvariants.primeToTorsionQuotient
        (valuation K).valuationSubring.unitGroup K.residueChar ≃*
      (LocalResidueField K)ˣ := by
  let f := integerUnitTorsionReduction K
  have hs : Function.Surjective f := integerUnitTorsionReduction_surjective K
  let T := CommGroup.torsion (valuation K).valuationSubring.unitGroup
  let eKer : T ⧸
        CommGroup.primaryComponent T K.residueChar ≃* T ⧸ f.ker :=
    QuotientGroup.congr _ _ (MulEquiv.refl T) (by
      rw [show ((MulEquiv.refl T : T ≃* T) : T →* T) = MonoidHom.id T by rfl,
        Subgroup.map_id]
      change CommGroup.primaryComponent T K.residueChar = f.ker
      exact (integerUnitTorsionReduction_ker K).symm)
  exact eKer.trans (QuotientGroup.quotientKerEquivOfSurjective f hs)

/-- Hoshi's prime-to-residue-characteristic torsion formula for valuation-ring units. -/
theorem one_add_integerUnitPrimeToTorsionQuotient_card
    (K : PointedMixedCharLocalField.{u}) :
    1 + Nat.card
        (OTriangle.GroupTheoreticInvariants.primeToTorsionQuotient
          (valuation K).valuationSubring.unitGroup K.residueChar) =
      K.residueChar ^ localResidueDegree K := by
  rw [Nat.card_congr
    (integerUnitPrimeToTorsionQuotientEquivResidueUnits K).toEquiv]
  rw [Nat.card_units, residueField_card_eq_residueChar_pow_residueDegree]
  simpa [Nat.add_comm] using
    (Nat.sub_add_cancel (show 1 ≤ K.residueChar ^ localResidueDegree K by
      exact (pow_pos (Fact.out : K.residueChar.Prime).pos _)))

end Anabelian.LCFT
