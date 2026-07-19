import Otriangle.MonoAnabelian.PrincipalCongruence
import Otriangle.MonoAnabelian.FiniteIndexTorsionFree
import Otriangle.MonoAnabelian.ResidueCharacteristicRank
import Otriangle.MonoAnabelian.ResidueCharacteristicFieldRank
import Otriangle.MonoAnabelian.GroupInvariants
import Mathlib.RingTheory.Ideal.Quotient.Index

/-!
# Exact residue-characteristic rank of local units

The subgroup `1 + p^2 O_K` is torsion-free, has finite index in the full unit group, and its
quotient by `p`th powers has cardinality `p^(e f)`.  The finite-index torsion cancellation lemma
therefore gives the same exact cardinality for all local units modulo torsion and `p`th powers.
-/

noncomputable section

namespace Anabelian.LCFT

open OTriangle ValuativeRel

universe u

/-- The square principal-congruence subgroup is contained in the valuation-theoretic deep
principal-unit subgroup and is therefore torsion-free. -/
theorem squarePrincipalCongruence_isMulTorsionFree
    (K : PointedMixedCharLocalField.{u})
    (d : residueCharPrincipalCongruenceGroup K 2)
    (hd : IsOfFinOrder d) :
    d = 1 := by
  let p : LocalIntegerRing K := residueCharInteger K
  let c := principalCongruenceCoefficient K 2 d
  have hdA := principalCongruenceUnit_eq_one_add K 2 d
  change (d.1 : LocalIntegerRing K) = 1 + p ^ 2 * c at hdA
  have hp0 : (K.residueChar : K) ≠ 0 := by
    exact_mod_cast (Fact.out : K.residueChar.Prime).ne_zero
  have hvp0 : 0 < valuation K (K.residueChar : K) :=
    ((map_ne_zero (valuation K)).mpr hp0).bot_lt
  have hvp : valuation K (K.residueChar : K) < 1 :=
    residueChar_cast_valuation_lt_one K
  have hvp2 : valuation K ((K.residueChar : K) ^ 2) <
      valuation K (K.residueChar : K) := by
    rw [map_pow, pow_two]
    exact mul_lt_of_lt_one_right hvp0 hvp
  have hdiff :
      (((d.1 : LocalIntegerRing K) : K) - 1) =
        (K.residueChar : K) ^ 2 * (c : K) := by
    have h := congrArg Subtype.val hdA
    change (((d.1 : LocalIntegerRing K) : K)) =
      1 + (K.residueChar : K) ^ 2 * (c : K) at h
    rw [h]
    ring
  have hc : valuation K (c : K) ≤ 1 := c.2
  have hdeep : valuation K ((((d.1 : LocalIntegerRing K) : K)) - 1) <
      valuation K (K.residueChar : K) := by
    rw [hdiff, map_mul]
    exact (mul_le_mul_left' hc _).trans_lt (by simpa using hvp2)
  let x : deepPrincipalUnitGroup K :=
    ⟨integerRingUnitsToFieldUnits K d.1, hdeep⟩
  have hxfin : IsOfFinOrder x := by
    obtain ⟨n, hn, hpow⟩ := hd.exists_pow_eq_one
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨n, hn, ?_⟩
    apply Subtype.ext
    apply Units.ext
    exact congrArg (fun z : residueCharPrincipalCongruenceGroup K 2 ↦
      (((z.1 : LocalIntegerRing K) : K))) hpow
  have hx := deepPrincipalUnit_eq_one_of_isOfFinOrder K x hxfin
  apply Subtype.ext
  apply Units.ext
  have hxval := congrArg (fun z : deepPrincipalUnitGroup K ↦ ((z.1 : Kˣ) : K)) hx
  exact Subtype.coe_injective hxval

/-- In the ambient valuation-ring unit group, the `p`th powers from `1 + p^2 O_K` are exactly
`1 + p^3 O_K`. -/
theorem subgroupPowerRange_squarePrincipal
    (K : PointedMixedCharLocalField.{u}) :
    subgroupPowerRange (residueCharPrincipalCongruenceGroup K 2) K.residueChar =
      residueCharPrincipalCongruenceGroup K 3 := by
  ext u
  constructor
  · rintro ⟨d, hd, rfl⟩
    have hd' :
        d ∈
          (powMonoidHom
            (α := residueCharPrincipalCongruenceGroup K 2)
            K.residueChar).range := hd
    rw [squarePrincipal_pow_range K] at hd'
    exact hd'
  · intro hu
    have hu2 := residueCharPrincipalCongruenceGroup_mono K (by omega : 2 ≤ 3) hu
    let d : residueCharPrincipalCongruenceGroup K 2 := ⟨u, hu2⟩
    have hd : d ∈ cubePrincipalInsideSquare K := hu
    rw [← squarePrincipal_pow_range K] at hd
    exact ⟨d, hd, rfl⟩

/-- Quotients of the valuation ring by powers of `p` are finite. -/
theorem residueCharPowerIdeal_quotient_finite
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) :
    Finite (LocalIntegerRing K ⧸ residueCharPowerIdeal K n) := by
  haveI : Finite (LocalIntegerRing K ⧸ localMaximalIdeal K) := by
    change Finite (LocalResidueField K)
    infer_instance
  have hfg : (localMaximalIdeal K).FG := Ideal.fg_of_isNoetherianRing _
  haveI : Finite (LocalIntegerRing K ⧸ localMaximalIdeal K ^
      (absoluteRamificationIndex K * n)) :=
    Ideal.finite_quotient_pow hfg _
  rw [residueCharPowerIdeal, residueCharIdeal_eq_maximalIdeal_pow, ← pow_mul]
  infer_instance

/-- The quotient of all valuation-ring units by `1 + p^3 O_K` is finite. -/
theorem residueCharCubePrincipal_ambientQuotient_finite
    (K : PointedMixedCharLocalField.{u}) :
    Finite ((LocalIntegerRing K)ˣ ⧸
      residueCharPrincipalCongruenceGroup K 3) := by
  let f := integerUnitReduction K 3
  haveI : Finite (LocalIntegerRing K ⧸ residueCharPowerIdeal K 3) :=
    residueCharPowerIdeal_quotient_finite K 3
  haveI : Finite (LocalIntegerRing K ⧸ residueCharPowerIdeal K 3)ˣ :=
    inferInstance
  haveI : Finite f.range := inferInstance
  exact Finite.of_equiv f.range
    (QuotientGroup.quotientKerEquivRange f).symm.toEquiv

/-- Torsion in the valuation-ring unit group is finite. -/
theorem integerRingUnits_torsion_finite
    (K : PointedMixedCharLocalField.{u}) :
    Finite (CommGroup.torsion (LocalIntegerRing K)ˣ) := by
  let i : CommGroup.torsion (LocalIntegerRing K)ˣ →
      CommGroup.torsion Kˣ := fun t ↦
    ⟨integerRingUnitsToFieldUnits K t.1,
      (integerRingUnitsToFieldUnits K).isOfFinOrder t.2⟩
  have hi : Function.Injective i := by
    intro a b hab
    apply Subtype.ext
    apply Units.ext
    have hval := congrArg (fun z : CommGroup.torsion Kˣ ↦ ((z.1 : Kˣ) : K)) hab
    exact Subtype.coe_injective hval
  exact @Finite.of_injective _ _ (fieldTorsion_finite K) i hi

/-- The exact local-unit contribution to Hoshi's residue-characteristic degree calculation. -/
theorem integerUnitTorsionFreeModPowerQuotient_card_eq_residueDegreeProduct
    (K : PointedMixedCharLocalField.{u}) :
    Nat.card (IntegerUnitTorsionFreeModPowerQuotient K) =
      K.residueChar ^
        (absoluteRamificationIndex K * localResidueDegree K) := by
  let A := LocalIntegerRing K
  let D := residueCharPrincipalCongruenceGroup K 2
  haveI : Finite (CommGroup.torsion Aˣ) := integerRingUnits_torsion_finite K
  haveI : Finite (SubgroupPowerAmbientQuotient D K.residueChar) := by
    change Finite ((LocalIntegerRing K)ˣ ⧸
      subgroupPowerRange
        (residueCharPrincipalCongruenceGroup K 2) K.residueChar)
    rw [subgroupPowerRange_squarePrincipal K]
    exact residueCharCubePrincipal_ambientQuotient_finite K
  have hdeep := torsionFreeModPower_card_eq_subgroupModPower D K.residueChar
    (Fact.out : K.residueChar.Prime).pos
    (squarePrincipalCongruence_isMulTorsionFree K)
  let U := (valuation K).valuationSubring.unitGroup
  let eU : U ≃* Aˣ :=
    (valuation K).valuationSubring.unitGroupMulEquiv
  let eT :=
    OTriangle.GroupTheoreticInvariants.torsionFreeQuotientEquiv eU
  let eP :=
    OTriangle.GroupTheoreticInvariants.modPowerQuotientEquiv eT K.residueChar
  calc
    Nat.card (IntegerUnitTorsionFreeModPowerQuotient K) =
        Nat.card (TorsionFreeModPowerQuotient Aˣ K.residueChar) :=
      Nat.card_congr eP.toEquiv
    _ = Nat.card
        (D ⧸ (powMonoidHom (α := D) K.residueChar).range) := hdeep
    _ = K.residueChar ^
        (absoluteRamificationIndex K * localResidueDegree K) :=
      squarePrincipalModPowerQuotient_card K

end Anabelian.LCFT
