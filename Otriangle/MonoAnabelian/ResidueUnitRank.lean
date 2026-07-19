import Otriangle.MonoAnabelian.ResiduePowerQuotientFinite

/-!
# The local-unit direction in residue characteristic

An explicit deep principal unit is nontorsion.  Krull intersection then shows that the
residue-characteristic power map on valuation-ring units modulo torsion cannot be surjective.
This isolates the unit direction needed in addition to the uniformizer direction.
-/

noncomputable section

namespace Anabelian.LCFT

open OTriangle ValuativeRel

universe u

theorem exists_integerUnit_not_isOfFinOrder
    (K : PointedMixedCharLocalField.{u}) :
    ∃ u : (valuation K).valuationSubring.unitGroup, ¬ IsOfFinOrder u := by
  have hp0 : (K.residueChar : K) ≠ 0 := by
    exact_mod_cast (Fact.out : K.residueChar.Prime).ne_zero
  have hvp0 : 0 < valuation K (K.residueChar : K) :=
    ((map_ne_zero (valuation K)).mpr hp0).bot_lt
  have hvp := residueChar_cast_valuation_lt_one K
  have hvp2 : valuation K ((K.residueChar : K) ^ 2) <
      valuation K (K.residueChar : K) := by
    rw [map_pow, pow_two]
    exact mul_lt_of_lt_one_right hvp0 hvp
  have honep2 : (1 + (K.residueChar : K) ^ 2) ≠ 0 := by
    intro hzero
    have heq : (K.residueChar : K) ^ 2 = -1 := by
      rw [eq_neg_iff_add_eq_zero]
      simpa [add_comm] using hzero
    have hval := congrArg (valuation K) heq
    have : valuation K ((K.residueChar : K) ^ 2) = 1 := by
      simpa using hval
    exact (ne_of_lt (hvp2.trans hvp)) this
  let d : Kˣ := Units.mk0 (1 + (K.residueChar : K) ^ 2) honep2
  have hdval : valuation K (d : K) = 1 := by
    change valuation K (1 + (K.residueChar : K) ^ 2) = 1
    exact (valuation K).map_one_add_of_lt (hvp2.trans hvp)
  let du : (valuation K).valuationSubring.unitGroup :=
    ⟨d, (Valuation.mem_unitGroup_iff K (valuation K) d).mpr hdval⟩
  refine ⟨du, ?_⟩
  intro hdu
  have hd : IsOfFinOrder d := by
    obtain ⟨n, hn, hpow⟩ := hdu.exists_pow_eq_one
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨n, hn, ?_⟩
    exact congrArg Subtype.val hpow
  let dd : deepPrincipalUnitGroup K := ⟨d, by
    change valuation K ((d : K) - 1) < valuation K (K.residueChar : K)
    change valuation K ((1 + (K.residueChar : K) ^ 2) - 1) <
      valuation K (K.residueChar : K)
    simpa only [add_sub_cancel_left] using hvp2⟩
  have hdd : IsOfFinOrder dd := by
    obtain ⟨n, hn, hpow⟩ := hd.exists_pow_eq_one
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨n, hn, ?_⟩
    apply Subtype.ext
    exact hpow
  have hdone := deepPrincipalUnit_eq_one_of_isOfFinOrder K dd hdd
  have hdvalone := congrArg (fun z : deepPrincipalUnitGroup K ↦ ((z : Kˣ) : K)) hdone
  change 1 + (K.residueChar : K) ^ 2 = 1 at hdvalone
  have hp2zero : (K.residueChar : K) ^ 2 = 0 := by
    apply add_left_cancel (a := (1 : K))
    simpa using hdvalone
  exact (pow_ne_zero 2 hp0) hp2zero

theorem integerUnitTorsionFree_pow_not_surjective_residueChar
    (K : PointedMixedCharLocalField.{u}) :
    ¬ Function.Surjective
      (powMonoidHom (α := IntegerUnitTorsionFreeQuotient K)
        K.residueChar) := by
  intro hsurj
  let U := (valuation K).valuationSubring.unitGroup
  let Q := IntegerUnitTorsionFreeQuotient K
  let qT : U →* Q := QuotientGroup.mk' (CommGroup.torsion U)
  have hall : ∀ q : Q, q = 1 := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (CommGroup.torsion U) q
    have hfactor : ∀ n : ℕ, ∃ (t y : Kˣ), IsOfFinOrder t ∧
        (x : Kˣ) = t * y ^ (K.residueChar ^ n) := by
      intro n
      obtain ⟨yq, hyq⟩ := pow_surjective_iterated
        K.residueChar hsurj n (qT x)
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
        (CommGroup.torsion U) yq
      change qT (y ^ (K.residueChar ^ n)) = qT x at hyq
      have htor : x * (y ^ (K.residueChar ^ n))⁻¹ ∈
          CommGroup.torsion U := by
        rw [← QuotientGroup.eq_one_iff]
        change qT x * (qT (y ^ (K.residueChar ^ n)))⁻¹ = 1
        rw [hyq, mul_inv_cancel]
      let tU : U := x * (y ^ (K.residueChar ^ n))⁻¹
      let t : Kˣ := tU
      let yK : Kˣ := y
      have ht : IsOfFinOrder t := by
        exact ((valuation K).valuationSubring.unitGroup.subtype).isOfFinOrder htor
      refine ⟨t, yK, ht, ?_⟩
      have heqU : x = tU * y ^ (K.residueChar ^ n) := by
        simp only [tU]
        group
      exact congrArg Subtype.val heqU
    have hxfin :=
      isOfFinOrder_of_all_residueChar_power_factorizations K (x : Kˣ) hfactor
    have hxfinU : IsOfFinOrder x := by
      obtain ⟨n, hn, hpow⟩ := hxfin.exists_pow_eq_one
      apply isOfFinOrder_iff_pow_eq_one.mpr
      refine ⟨n, hn, ?_⟩
      apply Subtype.ext
      exact hpow
    change ((x : U) : Q) = 1
    rw [QuotientGroup.eq_one_iff]
    exact hxfinU
  obtain ⟨u, hu⟩ := exists_integerUnit_not_isOfFinOrder K
  have huone : qT u = 1 := hall _
  have hutorsion : u ∈ CommGroup.torsion U := by
    rwa [← QuotientGroup.eq_one_iff]
  exact hu hutorsion

theorem integerUnitTorsionFreeModPowerQuotient_residueChar_nontrivial
    (K : PointedMixedCharLocalField.{u}) :
    Nontrivial (IntegerUnitTorsionFreeQuotient K ⧸
      (powMonoidHom (α := IntegerUnitTorsionFreeQuotient K)
        K.residueChar).range) := by
  rw [QuotientGroup.nontrivial_iff]
  intro htop
  apply integerUnitTorsionFree_pow_not_surjective_residueChar K
  exact MonoidHom.range_eq_top.mp htop

end Anabelian.LCFT

