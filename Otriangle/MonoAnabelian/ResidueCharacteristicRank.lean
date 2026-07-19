import Otriangle.MonoAnabelian.DeepUnits
import Otriangle.MonoAnabelian.OneField
import Otriangle.MonoAnabelian.MultiplicativeRank
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.RingTheory.Filtration

/-!
# The residue-characteristic multiplicative direction

This module proves that the torsion-free local multiplicative group is not divisible by the
residue characteristic.  Deep principal units first make the full local torsion subgroup finite.
A geometric-sum filtration then sends `p ^ n` powers of principal units into the `(n + 1)`st
power of the maximal ideal.  Krull intersection rules out nontrivial infinitely `p`-divisible
classes modulo torsion.
-/

noncomputable section

namespace Anabelian.LCFT

open OTriangle ValuativeRel

universe u

noncomputable def integerRingUnitsToFieldUnits
    (K : PointedMixedCharLocalField.{u}) :
    (valuation K).integerˣ →* Kˣ :=
  Units.map (valuation K).integer.subtype.toMonoidHom

def deepIntegerUnitGroup (K : PointedMixedCharLocalField.{u}) :
    Subgroup (valuation K).integerˣ :=
  (deepPrincipalUnitGroup K).comap (integerRingUnitsToFieldUnits K)

theorem deepIntegerUnitGroup_isOpen
    (K : PointedMixedCharLocalField.{u}) :
    IsOpen (deepIntegerUnitGroup K : Set (valuation K).integerˣ) := by
  letI := K.nontriviallyNormedField
  letI := K.isUltrametricDist
  letI := K.completeSpace
  change IsOpen {x : (valuation K).integerˣ |
    valuation K ((((x : (valuation K).integer) : K)) - 1) <
      valuation K (K.residueChar : K)}
  have hopen : IsOpen {z : K |
      valuation K z < valuation K (K.residueChar : K)} := by
    simpa only [Valuation.restrict_lt_iff_lt_embedding,
      Valuation.embedding_restrict] using
      (Valuation.isOpen_ball
        ((valuation K).restrict (K.residueChar : K)))
  exact hopen.preimage (by fun_prop)

theorem deepIntegerUnitGroup_quotient_finite
    (K : PointedMixedCharLocalField.{u}) :
    Finite ((valuation K).integerˣ ⧸ deepIntegerUnitGroup K) := by
  letI := K.nontriviallyNormedField
  letI := K.isUltrametricDist
  letI := K.completeSpace
  let A := (valuation K).integer
  haveI : CompactSpace A := by
    change CompactSpace 𝒪[K]
    infer_instance
  exact Subgroup.quotient_finite_of_isOpen _
    (deepIntegerUnitGroup_isOpen K)

theorem valuation_eq_one_of_isOfFinOrder
    (K : PointedMixedCharLocalField.{u}) (x : Kˣ) (hx : IsOfFinOrder x) :
    valuation K (x : K) = 1 := by
  have hfin : IsOfFinOrder (fieldUnitValuation K x) :=
    (fieldUnitValuation K).isOfFinOrder hx
  exact congrArg Units.val hfin.eq_one'

noncomputable def torsionToIntegerRingUnits
    (K : PointedMixedCharLocalField.{u}) :
    CommGroup.torsion Kˣ →* (valuation K).integerˣ :=
  (valuation K).valuationSubring.unitGroupMulEquiv.toMonoidHom.comp
    { toFun := fun x ↦ ⟨(x : Kˣ),
        (Valuation.mem_unitGroup_iff K (valuation K) (x : Kˣ)).mpr
          (valuation_eq_one_of_isOfFinOrder K x x.property)⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }

noncomputable def torsionToDeepIntegerUnitQuotient
    (K : PointedMixedCharLocalField.{u}) :
    CommGroup.torsion Kˣ →*
      ((valuation K).integerˣ ⧸ deepIntegerUnitGroup K) :=
  (QuotientGroup.mk' (deepIntegerUnitGroup K)).comp
    (torsionToIntegerRingUnits K)

theorem torsionToDeepIntegerUnitQuotient_injective
    (K : PointedMixedCharLocalField.{u}) :
    Function.Injective (torsionToDeepIntegerUnitQuotient K) := by
  rw [← (torsionToDeepIntegerUnitQuotient K).ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hdeep : torsionToIntegerRingUnits K x ∈ deepIntegerUnitGroup K :=
    (QuotientGroup.eq_one_iff _).mp hx
  have hfield : (x : Kˣ) ∈ deepPrincipalUnitGroup K := hdeep
  let y : deepPrincipalUnitGroup K := ⟨x, hfield⟩
  have hyfin : IsOfFinOrder y := by
    obtain ⟨n, hn, hpow⟩ := x.property.exists_pow_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, Subtype.ext hpow⟩
  have hyone := deepPrincipalUnit_eq_one_of_isOfFinOrder K y hyfin
  apply Subtype.ext
  change (x : Kˣ) = 1
  change ((y : deepPrincipalUnitGroup K) : Kˣ) = 1
  exact congrArg Subtype.val hyone

noncomputable instance fieldTorsion_finite
    (K : PointedMixedCharLocalField.{u}) : Finite (CommGroup.torsion Kˣ) :=
  @Finite.of_injective _ _ (deepIntegerUnitGroup_quotient_finite K)
    (torsionToDeepIntegerUnitQuotient K)
    (torsionToDeepIntegerUnitQuotient_injective K)

theorem pow_residueChar_sub_one_mem_maximalIdeal_pow_succ
    (K : PointedMixedCharLocalField.{u})
    (a : (valuation K).integer) (n : ℕ) (hn : n ≠ 0)
    (ha : a - 1 ∈
      (IsLocalRing.maximalIdeal (valuation K).integer) ^ n) :
    a ^ K.residueChar - 1 ∈
      (IsLocalRing.maximalIdeal (valuation K).integer) ^ (n + 1) := by
  let I := IsLocalRing.maximalIdeal (valuation K).integer
  let q := IsLocalRing.residue (valuation K).integer
  let S : (valuation K).integer :=
    ∑ i ∈ Finset.range K.residueChar, a ^ i
  have haI : a - 1 ∈ I := Ideal.pow_le_self hn ha
  have hamod : q a = 1 := by
    rw [← sub_eq_zero]
    calc
      q a - 1 = q (a - 1) := by rw [map_sub, map_one]
      _ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr haI
  have hS : S ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    calc
      q S = ∑ i ∈ Finset.range K.residueChar, (q a) ^ i := by simp [S]
      _ = (K.residueChar :
          IsLocalRing.ResidueField (valuation K).integer) := by simp [hamod]
      _ = 0 := CharP.cast_eq_zero _ K.residueChar
  have hmul : (a - 1) * S ∈ I ^ n * I := Ideal.mul_mem_mul ha hS
  rw [pow_succ']
  rw [← geom_sum_mul a K.residueChar]
  simpa [S, mul_comm] using hmul

theorem principalUnit_pow_residueChar_pow_sub_one_mem
    (K : PointedMixedCharLocalField.{u})
    (a : (valuation K).integer)
    (ha : a - 1 ∈
      IsLocalRing.maximalIdeal (valuation K).integer)
    (n : ℕ) :
    a ^ (K.residueChar ^ n) - 1 ∈
      (IsLocalRing.maximalIdeal (valuation K).integer) ^ (n + 1) := by
  induction n with
  | zero => simpa using ha
  | succ n ih =>
      simpa only [pow_succ, pow_mul] using
        (pow_residueChar_sub_one_mem_maximalIdeal_pow_succ K
          (a ^ (K.residueChar ^ n)) (n + 1) (Nat.succ_ne_zero n) ih)

theorem fieldUnitDiscreteValuation_eq_one_iff
    (K : PointedMixedCharLocalField.{u}) (x : Kˣ) :
    fieldUnitDiscreteValuation K x = 1 ↔ valuation K (x : K) = 1 := by
  let e : (ValueGroupWithZero K)ˣ ≃* Multiplicative ℤ :=
    (Units.mapEquiv
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toMulEquiv).trans
      WithZero.unitsWithZeroEquiv
  change e (fieldUnitValuation K x) = 1 ↔ valuation K (x : K) = 1
  constructor
  · intro h
    have hu : fieldUnitValuation K x = 1 := by
      apply e.injective
      simpa using h
    exact congrArg Units.val hu
  · intro h
    have hu : fieldUnitValuation K x = 1 := Units.ext h
    simpa using congrArg e hu

theorem fieldUnitDiscreteValuation_eq_one_of_all_residueChar_pow_dvd
    (K : PointedMixedCharLocalField.{u}) (x : Kˣ)
    (hdiv : ∀ n : ℕ, ((K.residueChar : ℤ) ^ n) ∣
      (fieldUnitDiscreteValuation K x).toAdd) :
    fieldUnitDiscreteValuation K x = 1 := by
  let z := (fieldUnitDiscreteValuation K x).toAdd
  have hz : z = 0 := by
    by_contra hz0
    let n := z.natAbs + 1
    have hle : ((K.residueChar : ℤ) ^ n).natAbs ≤ z.natAbs :=
      Int.natAbs_le_of_dvd_ne_zero (hdiv n) hz0
    have hlt : z.natAbs < ((K.residueChar : ℤ) ^ n).natAbs := by
      rw [Int.natAbs_pow, Int.natAbs_natCast]
      exact z.natAbs.lt_succ_self.trans
        (Nat.lt_pow_self (Fact.out : K.residueChar.Prime).one_lt)
    exact (not_lt_of_ge hle) hlt
  apply Multiplicative.toAdd.injective
  simpa [z] using hz

theorem isOfFinOrder_of_all_residueChar_power_factorizations
    (K : PointedMixedCharLocalField.{u}) (x : Kˣ)
    (hfactor : ∀ n : ℕ, ∃ (t y : Kˣ), IsOfFinOrder t ∧
      x = t * y ^ (K.residueChar ^ n)) :
    IsOfFinOrder x := by
  classical
  let A : ValuationSubring K := (valuation K).valuationSubring
  let T := CommGroup.torsion Kˣ
  let M := Nat.card T
  have hdiv : ∀ n : ℕ, ((K.residueChar : ℤ) ^ n) ∣
      (fieldUnitDiscreteValuation K x).toAdd := by
    intro n
    obtain ⟨t, y, ht, hxy⟩ := hfactor n
    have htval := fieldUnitDiscreteValuation_eq_one_of_isOfFinOrder K t ht
    have heq := congrArg (fieldUnitDiscreteValuation K) hxy
    rw [map_mul, map_pow, htval, one_mul] at heq
    have heqadd := congrArg Multiplicative.toAdd heq
    change (fieldUnitDiscreteValuation K x).toAdd =
      (K.residueChar ^ n) • (fieldUnitDiscreteValuation K y).toAdd at heqadd
    refine ⟨(fieldUnitDiscreteValuation K y).toAdd, ?_⟩
    simpa only [Nat.cast_pow, nsmul_eq_mul] using heqadd
  have hxdisc : fieldUnitDiscreteValuation K x = 1 :=
    fieldUnitDiscreteValuation_eq_one_of_all_residueChar_pow_dvd K x hdiv
  have hxval : valuation K (x : K) = 1 :=
    (fieldUnitDiscreteValuation_eq_one_iff K x).mp hxdisc
  let xU : A.unitGroup := ⟨x,
    (Valuation.mem_unitGroup_iff K (valuation K) x).mpr hxval⟩
  let xA : A := A.unitGroupMulEquiv xU
  have hMpos : 0 < M := Nat.card_pos
  letI : IsNoetherianRing A := by
    change IsNoetherianRing (valuation K).integer
    infer_instance
  have hxMmem : ∀ n : ℕ, xA ^ M - 1 ∈
      (IsLocalRing.maximalIdeal A) ^ (n + 1) := by
    intro n
    obtain ⟨t, y, ht, hxy⟩ := hfactor n
    have hydisc : fieldUnitDiscreteValuation K y = 1 := by
      have heq := congrArg (fieldUnitDiscreteValuation K) hxy
      rw [map_mul, map_pow,
        fieldUnitDiscreteValuation_eq_one_of_isOfFinOrder K t ht, one_mul] at heq
      have heqadd := congrArg Multiplicative.toAdd heq
      change (fieldUnitDiscreteValuation K x).toAdd =
        (K.residueChar ^ n) • (fieldUnitDiscreteValuation K y).toAdd at heqadd
      rw [hxdisc] at heqadd
      change 0 = (K.residueChar ^ n) •
        (fieldUnitDiscreteValuation K y).toAdd at heqadd
      have hp0 : (K.residueChar : ℤ) ^ n ≠ 0 := by
        exact pow_ne_zero _ (by exact_mod_cast
          (Fact.out : K.residueChar.Prime).ne_zero)
      have hyzero : (fieldUnitDiscreteValuation K y).toAdd = 0 := by
        apply (mul_eq_zero.mp ?_).resolve_left hp0
        simpa only [Nat.cast_pow, nsmul_eq_mul] using heqadd.symm
      apply Multiplicative.toAdd.injective
      simpa using hyzero
    have hyval : valuation K (y : K) = 1 :=
      (fieldUnitDiscreteValuation_eq_one_iff K y).mp hydisc
    let yU : A.unitGroup := ⟨y,
      (Valuation.mem_unitGroup_iff K (valuation K) y).mpr hyval⟩
    obtain ⟨sU, hsfin, hsres⟩ :=
      residueUnit_has_torsion_lift K (A.unitGroupToResidueFieldUnits yU)
    let zU : A.unitGroup := yU * sU⁻¹
    have hzker : zU ∈ A.unitGroupToResidueFieldUnits.ker := by
      rw [MonoidHom.mem_ker]
      simp only [zU, map_mul, map_inv]
      rw [← hsres]
      exact mul_inv_cancel _
    have hzprincipal : (zU : Kˣ) ∈ A.principalUnitGroup := by
      rw [A.coe_mem_principalUnitGroup_iff, MonoidHom.mem_ker]
      exact (show A.unitGroupToResidueFieldUnits zU = 1 by
        rwa [← MonoidHom.mem_ker])
    let zA : A := A.unitGroupMulEquiv zU
    have hzAmod : IsLocalRing.residue A zA = 1 := by
      have := hzker
      rw [MonoidHom.mem_ker] at this
      exact Units.ext_iff.mp this
    have hzApowmod : IsLocalRing.residue A (zA ^ M) = 1 := by
      rw [map_pow, hzAmod, one_pow]
    have hzApowPrincipal : zA ^ M - 1 ∈ IsLocalRing.maximalIdeal A := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change IsLocalRing.residue A (zA ^ M - 1) = 0
      rw [map_sub, map_one, hzApowmod, sub_self]
    have hfiltration :=
      principalUnit_pow_residueChar_pow_sub_one_mem K
        (zA ^ M) hzApowPrincipal n
    have hsK : IsOfFinOrder (sU : Kˣ) :=
      Submonoid.isOfFinOrder_coe.mpr hsfin
    let t' : T := ⟨t * (sU : Kˣ) ^ (K.residueChar ^ n),
      ht.mul (hsK.pow)⟩
    have ht'M : ((t' : T) ^ M : T) = 1 := pow_card_eq_one'
    have ht'MK : (t * (sU : Kˣ) ^ (K.residueChar ^ n)) ^ M = 1 :=
      congrArg Subtype.val ht'M
    have hxyz : x = (t' : Kˣ) * (zU : Kˣ) ^ (K.residueChar ^ n) := by
      rw [hxy]
      change t * y ^ (K.residueChar ^ n) =
        (t * (sU : Kˣ) ^ (K.residueChar ^ n)) *
          (y * (sU : Kˣ)⁻¹) ^ (K.residueChar ^ n)
      symm
      calc
        (t * (sU : Kˣ) ^ (K.residueChar ^ n)) *
            (y * (sU : Kˣ)⁻¹) ^ (K.residueChar ^ n) =
            (t * (sU : Kˣ) ^ (K.residueChar ^ n)) *
              (y ^ (K.residueChar ^ n) *
                ((sU : Kˣ)⁻¹) ^ (K.residueChar ^ n)) := by rw [mul_pow]
        _ = (t * y ^ (K.residueChar ^ n)) *
            ((sU : Kˣ) ^ (K.residueChar ^ n) *
              ((sU : Kˣ)⁻¹) ^ (K.residueChar ^ n)) := by ac_rfl
        _ = t * y ^ (K.residueChar ^ n) := by rw [← mul_pow]; simp
    have hxM : x ^ M = ((zU : Kˣ) ^ M) ^ (K.residueChar ^ n) := by
      rw [hxyz, mul_pow, ht'MK, one_mul]
      calc
        ((zU : Kˣ) ^ (K.residueChar ^ n)) ^ M =
            (zU : Kˣ) ^ ((K.residueChar ^ n) * M) :=
          (pow_mul _ _ _).symm
        _ = (zU : Kˣ) ^ (M * (K.residueChar ^ n)) := by rw [Nat.mul_comm]
        _ = ((zU : Kˣ) ^ M) ^ (K.residueChar ^ n) := pow_mul _ _ _
    have hxMA : xA ^ M - 1 = (zA ^ M) ^ (K.residueChar ^ n) - 1 := by
      apply Subtype.ext
      exact congrArg (fun w : Kˣ ↦ (w : K) - 1) hxM
    rw [hxMA]
    exact hfiltration
  have hxMzero : xA ^ M - 1 = 0 := by
    have hall : xA ^ M - 1 ∈ ⨅ n : ℕ, (IsLocalRing.maximalIdeal A) ^ n := by
      rw [Ideal.mem_iInf]
      intro n
      cases n with
      | zero => simp
      | succ n => simpa only [Nat.succ_eq_add_one] using hxMmem n
    have hintersection : (⨅ n : ℕ, (IsLocalRing.maximalIdeal A) ^ n) = ⊥ :=
      Ideal.iInf_pow_eq_bot_of_isLocalRing
        (IsLocalRing.maximalIdeal A)
        (inferInstance : (IsLocalRing.maximalIdeal A).IsMaximal).ne_top
    rw [hintersection] at hall
    exact hall
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨M, hMpos, ?_⟩
  apply Units.ext
  exact sub_eq_zero.mp (congrArg Subtype.val hxMzero)

theorem pow_surjective_iterated {B : Type*} [CommGroup B]
    (p : ℕ) (h : Function.Surjective (powMonoidHom (α := B) p)) :
    ∀ n : ℕ, Function.Surjective (powMonoidHom (α := B) (p ^ n)) := by
  intro n x
  induction n with
  | zero => exact ⟨x, by simp⟩
  | succ n ih =>
      obtain ⟨a, ha⟩ := ih
      obtain ⟨b, hb⟩ := h a
      change a ^ (p ^ n) = x at ha
      change b ^ p = a at hb
      refine ⟨b, ?_⟩
      change b ^ (p ^ (n + 1)) = x
      calc
        b ^ (p ^ (n + 1)) = (b ^ p) ^ (p ^ n) := by
          rw [pow_succ, ← pow_mul, Nat.mul_comm]
        _ = a ^ (p ^ n) := by rw [hb]
        _ = x := ha

theorem fieldTorsionFree_pow_not_surjective_residueChar
    (K : PointedMixedCharLocalField.{u}) :
    ¬ Function.Surjective
      (powMonoidHom (α := FieldTorsionFreeQuotient K) K.residueChar) := by
  intro hsurj
  let Q := FieldTorsionFreeQuotient K
  let qT : Kˣ →* Q := QuotientGroup.mk' (CommGroup.torsion Kˣ)
  have hall : ∀ q : Q, q = 1 := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (CommGroup.torsion Kˣ) q
    have hfactor : ∀ n : ℕ, ∃ (t y : Kˣ), IsOfFinOrder t ∧
        x = t * y ^ (K.residueChar ^ n) := by
      intro n
      obtain ⟨yq, hyq⟩ := pow_surjective_iterated
        K.residueChar hsurj n (qT x)
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
        (CommGroup.torsion Kˣ) yq
      change qT (y ^ (K.residueChar ^ n)) = qT x at hyq
      have htor : x * (y ^ (K.residueChar ^ n))⁻¹ ∈
          CommGroup.torsion Kˣ := by
        rw [← QuotientGroup.eq_one_iff]
        change qT x * (qT (y ^ (K.residueChar ^ n)))⁻¹ = 1
        rw [hyq, mul_inv_cancel]
      let t : Kˣ := x * (y ^ (K.residueChar ^ n))⁻¹
      refine ⟨t, y, htor, ?_⟩
      simp only [t]
      group
    have hxfin :=
      isOfFinOrder_of_all_residueChar_power_factorizations K x hfactor
    change ((x : Kˣ) : Q) = 1
    rw [QuotientGroup.eq_one_iff]
    exact hxfin
  have hu : ((uniformizerUnit K : Kˣ) : Q) = 1 := hall _
  have hutorsion : uniformizerUnit K ∈ CommGroup.torsion Kˣ := by
    rwa [← QuotientGroup.eq_one_iff]
  exact uniformizer_not_pow_mod_torsion K K.residueChar
    (Fact.out : K.residueChar.Prime) 1 (by simpa using hutorsion)

theorem fieldTorsionFreeModPowerQuotient_residueChar_nontrivial
    (K : PointedMixedCharLocalField.{u}) :
    Nontrivial (FieldTorsionFreeModPowerQuotient K K.residueChar) := by
  rw [QuotientGroup.nontrivial_iff]
  intro htop
  apply fieldTorsionFree_pow_not_surjective_residueChar K
  exact MonoidHom.range_eq_top.mp htop

end Anabelian.LCFT
