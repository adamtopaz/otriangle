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

/-- A unit congruent to one cannot have prime-to-characteristic finite order.  This elementary
geometric-sum form of the unramifiedness of prime-to-`p` roots works in any local domain. -/
theorem unit_eq_one_of_pow_eq_one_of_residue_eq_one_of_coprime
    (R : Type*) [CommRing R] [IsDomain R] [IsLocalRing R]
    (p n : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]
    (u : Rˣ) (hpow : u ^ n = 1)
    (hres : Units.map (IsLocalRing.residue R).toMonoidHom u = 1)
    (hcop : Nat.Coprime n p) : u = 1 := by
  let s : R := ∑ i ∈ Finset.range n, (u : R) ^ i
  have hresu : IsLocalRing.residue R (u : R) = 1 :=
    congrArg Units.val hres
  have hress : IsLocalRing.residue R s = (n : IsLocalRing.ResidueField R) := by
    simp only [s, map_sum, map_pow, hresu, one_pow, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
  have hncast : (n : IsLocalRing.ResidueField R) ≠ 0 := by
    intro hnzero
    have hpn : p ∣ n :=
      (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField R) p n).mp hnzero
    exact (Fact.out : p.Prime).ne_one (hcop.symm.eq_one_of_dvd hpn)
  have hsunit : IsUnit s :=
    (IsLocalRing.residue_ne_zero_iff_isUnit s).mp (hress.symm ▸ hncast)
  have hgeom : ((u : R) - 1) * s = 0 := by
    rw [mul_geom_sum]
    have huval : (u : R) ^ n = 1 := congrArg Units.val hpow
    rw [huval, sub_self]
  have huval : (u : R) = 1 := sub_eq_zero.mp
    ((mul_eq_zero.mp hgeom).resolve_right hsunit.ne_zero)
  exact Units.ext huval

/-- Reduction preserves the exact order of any unit whose order is prime to the residue
characteristic. -/
theorem orderOf_unitsMap_residue_eq_of_coprime
    (R : Type*) [CommRing R] [IsDomain R] [IsLocalRing R]
    (p n : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]
    (zeta : Rˣ) (hn : 0 < n) (hzeta : orderOf zeta = n)
    (hcop : Nat.Coprime n p) :
    orderOf (Units.map (IsLocalRing.residue R).toMonoidHom zeta) = n := by
  let d := orderOf (Units.map (IsLocalRing.residue R).toMonoidHom zeta)
  have hdn : d ∣ n := by
    calc
      d ∣ orderOf zeta :=
        orderOf_map_dvd (Units.map (IsLocalRing.residue R).toMonoidHom) zeta
      _ = n := hzeta
  have hrespow : Units.map (IsLocalRing.residue R).toMonoidHom (zeta ^ d) = 1 := by
    rw [map_pow, pow_orderOf_eq_one]
  have hzetapow : zeta ^ n = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hzeta]
  have hpow : (zeta ^ d) ^ n = 1 := by
    rw [pow_right_comm, hzetapow, one_pow]
  have hzone : zeta ^ d = 1 :=
    unit_eq_one_of_pow_eq_one_of_residue_eq_one_of_coprime
      R p n (zeta ^ d) hpow hrespow hcop
  have hnd : n ∣ d := by
    rw [← hzeta]
    exact orderOf_dvd_of_pow_eq_one hzone
  exact Nat.dvd_antisymm hdn hnd

/-- Reduction preserves the exact order of a torsion unit whose order is prime to the residue
characteristic.  Equivalently, prime-to-`p` roots of unity do not collide modulo the maximal
ideal. -/
theorem orderOf_unitGroupToResidueFieldUnits_eq_of_coprime
    (K : PointedMixedCharLocalField.{u})
    (zeta : (valuation K).valuationSubring.unitGroup) (n : ℕ)
    (hn : 0 < n) (hzeta : orderOf zeta = n)
    (hcop : Nat.Coprime n K.residueChar) :
    orderOf
        ((valuation K).valuationSubring.unitGroupToResidueFieldUnits zeta) = n := by
  let A := (valuation K).valuationSubring
  let T := CommGroup.torsion A.unitGroup
  let t : T := ⟨zeta, orderOf_pos_iff.mp (hzeta.symm ▸ hn)⟩
  let d := orderOf (integerUnitTorsionReduction K t)
  have hdn : d ∣ n := by
    calc
      d ∣ orderOf t := orderOf_map_dvd (integerUnitTorsionReduction K) t
      _ = orderOf zeta := (Subgroup.orderOf_coe t).symm
      _ = n := hzeta
  have htker : t ^ d ∈ (integerUnitTorsionReduction K).ker := by
    rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
  rw [integerUnitTorsionReduction_ker K,
    CommGroup.mem_primaryComponent] at htker
  obtain ⟨a, ha⟩ := htker
  have hpow : t ^ (d * K.residueChar ^ a) = 1 := by
    simpa only [pow_mul] using ha
  have hndmul : n ∣ d * K.residueChar ^ a := by
    calc
      n = orderOf zeta := hzeta.symm
      _ = orderOf t := Subgroup.orderOf_coe t
      _ ∣ d * K.residueChar ^ a := orderOf_dvd_of_pow_eq_one hpow
  have hnd : n ∣ d :=
    (hcop.pow_right a).dvd_mul_right.mp hndmul
  apply Nat.dvd_antisymm hdn hnd

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
