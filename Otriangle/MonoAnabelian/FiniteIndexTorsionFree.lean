import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Torsion

/-!
# Mod-power cardinality from a finite-index torsion-free subgroup

This file isolates the elementary abelian-group argument used in the exact local
multiplicative-rank calculation.  If a commutative group contains a torsion-free subgroup `D`
of finite index, its quotient modulo torsion and `n`th powers has the same cardinality as
`D / D^n`.  The proof keeps track of the `n`-torsion which appears in the raw power quotient
and is then removed by quotienting by all torsion.
-/

noncomputable section

namespace Anabelian.LCFT

universe u

variable {U : Type u} [CommGroup U]

/-- The `n`th powers of a subgroup, regarded as a subgroup of the ambient group. -/
def subgroupPowerRange (D : Subgroup U) (n : ℕ) : Subgroup U :=
  (powMonoidHom (α := D) n).range.map D.subtype

theorem subgroupPowerRange_le (D : Subgroup U) (n : ℕ) :
    subgroupPowerRange D n ≤ D := by
  rintro _ ⟨d, _, rfl⟩
  exact d.2

theorem subgroupPowerRange_le_ambientPowerRange (D : Subgroup U) (n : ℕ) :
    subgroupPowerRange D n ≤ (powMonoidHom (α := U) n).range := by
  rintro _ ⟨_, ⟨d, rfl⟩, rfl⟩
  exact ⟨d.1, rfl⟩

/-- The quotient of an ambient group by the `n`th powers coming from `D`. -/
abbrev SubgroupPowerAmbientQuotient (D : Subgroup U) (n : ℕ) :=
  U ⧸ subgroupPowerRange D n

/-- The `n`-torsion maps into the kernel of the power map after quotienting by `D^n`. -/
noncomputable def powerTorsionToSubgroupPowerQuotientKernel
    (D : Subgroup U) (n : ℕ) :
    (powMonoidHom (α := U) n).ker →*
      (powMonoidHom (α := SubgroupPowerAmbientQuotient D n) n).ker where
  toFun t := ⟨(t.1 : SubgroupPowerAmbientQuotient D n), by
    rw [MonoidHom.mem_ker]
    change ((t.1 ^ n : U) : SubgroupPowerAmbientQuotient D n) = 1
    have ht := t.2
    rw [MonoidHom.mem_ker] at ht
    change t.1 ^ n = 1 at ht
    rw [ht]
    rfl⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The quotient `D / D^n` also maps into the kernel of the ambient quotient's power map. -/
noncomputable def subgroupModPowerToSubgroupPowerQuotientKernel
    (D : Subgroup U) (n : ℕ) :
    (D ⧸ (powMonoidHom (α := D) n).range) →*
      (powMonoidHom (α := SubgroupPowerAmbientQuotient D n) n).ker :=
  QuotientGroup.lift (powMonoidHom (α := D) n).range
    ({
      toFun := fun d ↦ ⟨(d.1 : SubgroupPowerAmbientQuotient D n), by
        rw [MonoidHom.mem_ker]
        change ((d.1 ^ n : U) : SubgroupPowerAmbientQuotient D n) = 1
        rw [QuotientGroup.eq_one_iff]
        exact ⟨d ^ n, ⟨d, rfl⟩, rfl⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
    } : D →*
      (powMonoidHom (α := SubgroupPowerAmbientQuotient D n) n).ker) (by
        intro d hd
        obtain ⟨a, rfl⟩ := hd
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        change (((a.1 ^ n : U) : SubgroupPowerAmbientQuotient D n)) = 1
        rw [QuotientGroup.eq_one_iff]
        exact ⟨a ^ n, ⟨a, rfl⟩, rfl⟩)

/-- Multiplication combines the `n`-torsion and deep-subgroup factors in the kernel. -/
noncomputable def torsionTimesSubgroupModPowerToPowerKernel
    (D : Subgroup U) (n : ℕ) :
    (powMonoidHom (α := U) n).ker ×
        (D ⧸ (powMonoidHom (α := D) n).range) →*
      (powMonoidHom (α := SubgroupPowerAmbientQuotient D n) n).ker where
  toFun x :=
    powerTorsionToSubgroupPowerQuotientKernel D n x.1 *
      subgroupModPowerToSubgroupPowerQuotientKernel D n x.2
  map_one' := by
    change
      powerTorsionToSubgroupPowerQuotientKernel D n 1 *
        subgroupModPowerToSubgroupPowerQuotientKernel D n 1 = 1
    rw [map_one, map_one, one_mul]
  map_mul' := by
    intro x y
    change
      powerTorsionToSubgroupPowerQuotientKernel D n (x.1 * y.1) *
          subgroupModPowerToSubgroupPowerQuotientKernel D n (x.2 * y.2) =
        (powerTorsionToSubgroupPowerQuotientKernel D n x.1 *
            subgroupModPowerToSubgroupPowerQuotientKernel D n x.2) *
          (powerTorsionToSubgroupPowerQuotientKernel D n y.1 *
            subgroupModPowerToSubgroupPowerQuotientKernel D n y.2)
    rw [map_mul, map_mul]
    ac_rfl

/-- The kernel decomposition underlying the finite-index calculation. -/
theorem torsionTimesSubgroupModPowerToPowerKernel_bijective
    (D : Subgroup U) (n : ℕ) (hn : 0 < n)
    (hD : ∀ d : D, IsOfFinOrder d → d = 1) :
    Function.Bijective (torsionTimesSubgroupModPowerToPowerKernel D n) := by
  constructor
  · rintro ⟨t₁, d₁⟩ ⟨t₂, d₂⟩ h
    obtain ⟨a₁, rfl⟩ := QuotientGroup.mk'_surjective
      (powMonoidHom (α := D) n).range d₁
    obtain ⟨a₂, rfl⟩ := QuotientGroup.mk'_surjective
      (powMonoidHom (α := D) n).range d₂
    have hq := congrArg Subtype.val h
    change ((t₁.1 * a₁.1 : U) : SubgroupPowerAmbientQuotient D n) =
      ((t₂.1 * a₂.1 : U) : SubgroupPowerAmbientQuotient D n) at hq
    rw [QuotientGroup.eq_iff_div_mem] at hq
    have htmem : t₁.1 * t₂.1⁻¹ ∈ D := by
      have hprod : (t₁.1 * a₁.1) * (t₂.1 * a₂.1)⁻¹ ∈ D :=
        (subgroupPowerRange_le D n) (by simpa [div_eq_mul_inv] using hq)
      have hm := D.mul_mem (D.mul_mem hprod a₂.2) (D.inv_mem a₁.2)
      simpa [mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using hm
    let td : D := ⟨t₁.1 * t₂.1⁻¹, htmem⟩
    have ht₁pow := t₁.2
    rw [MonoidHom.mem_ker] at ht₁pow
    change t₁.1 ^ n = 1 at ht₁pow
    have ht₂pow := t₂.2
    rw [MonoidHom.mem_ker] at ht₂pow
    change t₂.1 ^ n = 1 at ht₂pow
    have htdpow : td ^ n = 1 := by
      apply Subtype.ext
      change (t₁.1 * t₂.1⁻¹) ^ n = 1
      rw [mul_pow, inv_pow, ht₁pow, ht₂pow, inv_one, mul_one]
    have htdfin : IsOfFinOrder td :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, htdpow⟩
    have htd := hD td htdfin
    have ht : t₁ = t₂ := by
      apply Subtype.ext
      have hval := congrArg Subtype.val htd
      change t₁.1 * t₂.1⁻¹ = 1 at hval
      exact mul_inv_eq_one.mp hval
    refine Prod.ext ht ?_
    subst t₂
    change
      ((a₁ : D) : D ⧸ (powMonoidHom (α := D) n).range) =
        ((a₂ : D) : D ⧸ (powMonoidHom (α := D) n).range)
    rw [QuotientGroup.eq_iff_div_mem]
    have hprod : (t₁.1 * a₁.1) * (t₁.1 * a₂.1)⁻¹ ∈
        subgroupPowerRange D n := by
      simpa [div_eq_mul_inv] using hq
    have ha : a₁.1 * a₂.1⁻¹ ∈ subgroupPowerRange D n := by
      have heq : (t₁.1 * a₁.1) * (t₁.1 * a₂.1)⁻¹ =
          a₁.1 * a₂.1⁻¹ := by
        rw [mul_inv_rev]
        calc
          t₁.1 * a₁.1 * (a₂.1⁻¹ * t₁.1⁻¹) =
              (t₁.1 * t₁.1⁻¹) * (a₁.1 * a₂.1⁻¹) := by ac_rfl
          _ = a₁.1 * a₂.1⁻¹ := by rw [mul_inv_cancel, one_mul]
      rwa [heq] at hprod
    obtain ⟨b, hb, heq⟩ := ha
    have hba : b = a₁ * a₂⁻¹ := by
      apply Subtype.ext
      exact heq
    rw [div_eq_mul_inv]
    rw [← hba]
    exact hb
  · intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
      (subgroupPowerRange D n) y.1
    have hy := y.2
    rw [MonoidHom.mem_ker] at hy
    change y.1 ^ n = 1 at hy
    rw [← hx, ← map_pow] at hy
    change ((x ^ n : U) : SubgroupPowerAmbientQuotient D n) = 1 at hy
    rw [QuotientGroup.eq_one_iff] at hy
    obtain ⟨_, ⟨d, hd⟩, hdn⟩ := hy
    let t : (powMonoidHom (α := U) n).ker := ⟨x * d.1⁻¹, by
      rw [MonoidHom.mem_ker]
      change (x * d.1⁻¹) ^ n = 1
      rw [mul_pow, inv_pow]
      have hdn' : d.1 ^ n = x ^ n := by
        change ((powMonoidHom (α := D) n d).1 : U) = x ^ n
        rw [hd]
        exact hdn
      rw [← hdn', mul_inv_cancel]
    ⟩
    refine ⟨(t, (d : D ⧸ (powMonoidHom (α := D) n).range)), ?_⟩
    apply Subtype.ext
    change (((x * d.1⁻¹) * d.1 : U) : SubgroupPowerAmbientQuotient D n) = y.1
    have heq : (x * d.1⁻¹) * d.1 = x := by group
    rw [heq]
    exact hx

/-- Before quotienting by torsion, the ambient mod-power quotient consists of the deep
torsion-free factor together with the ambient `n`-torsion. -/
theorem ambientModPower_card_eq_powerTorsion_mul_subgroupModPower
    (D : Subgroup U) (n : ℕ) (hn : 0 < n)
    (hD : ∀ d : D, IsOfFinOrder d → d = 1)
    [Finite (SubgroupPowerAmbientQuotient D n)] :
    Nat.card (U ⧸ (powMonoidHom (α := U) n).range) =
      Nat.card (powMonoidHom (α := U) n).ker *
        Nat.card (D ⧸ (powMonoidHom (α := D) n).range) := by
  let R := subgroupPowerRange D n
  let P := (powMonoidHom (α := U) n).range
  let Q := SubgroupPowerAmbientQuotient D n
  let q : U →* Q := QuotientGroup.mk' R
  let f : Q →* Q := powMonoidHom n
  have hRP : R ≤ P := subgroupPowerRange_le_ambientPowerRange D n
  have hmap : P.map q = f.range := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨(x : Q), by
        change ((x ^ n : U) : Q) = ((x : Q) ^ n)
        exact map_pow q x n⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R z
      refine ⟨x ^ n, ⟨x, rfl⟩, ?_⟩
      exact map_pow q x n
  have hkerFiniteIndex : f.ker.FiniteIndex := by
    rw [Subgroup.finiteIndex_iff_finite_quotient]
    infer_instance
  let e :
      (powMonoidHom (α := U) n).ker ×
          (D ⧸ (powMonoidHom (α := D) n).range) ≃ f.ker :=
    Equiv.ofBijective (torsionTimesSubgroupModPowerToPowerKernel D n)
      (torsionTimesSubgroupModPowerToPowerKernel_bijective D n hn hD)
  calc
    Nat.card (U ⧸ P) = Nat.card (Q ⧸ P.map q) :=
      Nat.card_congr
        (QuotientGroup.quotientQuotientEquivQuotient R P hRP).toEquiv.symm
    _ = Nat.card (Q ⧸ f.range) := by rw [← hmap]
    _ = f.range.index := (Subgroup.index_eq_card f.range).symm
    _ = Nat.card f.ker := Subgroup.index_range
    _ = Nat.card
        ((powMonoidHom (α := U) n).ker ×
          (D ⧸ (powMonoidHom (α := D) n).range)) :=
      Nat.card_congr e.symm
    _ = Nat.card (powMonoidHom (α := U) n).ker *
        Nat.card (D ⧸ (powMonoidHom (α := D) n).range) :=
      Nat.card_prod _ _

/-- Ambient `n`-torsion is the same as `n`-torsion inside the full torsion subgroup. -/
noncomputable def ambientPowerTorsionEquivTorsionPowerTorsion
    (n : ℕ) (hn : 0 < n) :
    (powMonoidHom (α := U) n).ker ≃*
      (powMonoidHom (α := CommGroup.torsion U) n).ker where
  toFun x := by
    have hx := x.2
    rw [MonoidHom.mem_ker] at hx
    change x.1 ^ n = 1 at hx
    let xt : CommGroup.torsion U :=
      ⟨x.1, isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hx⟩⟩
    exact ⟨xt, by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      exact hx⟩
  invFun x := ⟨x.1.1, by
    rw [MonoidHom.mem_ker]
    have hx := x.2
    rw [MonoidHom.mem_ker] at hx
    exact congrArg Subtype.val hx⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Intersecting ambient `n`th powers with torsion gives exactly the `n`th powers within the
torsion subgroup. -/
theorem ambientPowerRange_inf_torsion_subgroupOf
    (n : ℕ) (hn : 0 < n) :
    ((powMonoidHom (α := U) n).range.subgroupOf
      (CommGroup.torsion U)) =
        (powMonoidHom (α := CommGroup.torsion U) n).range := by
  ext t
  constructor
  · rintro ⟨x, hx⟩
    let xt : CommGroup.torsion U := by
      refine ⟨x, ?_⟩
      obtain ⟨m, hm, htm⟩ := t.2.exists_pow_eq_one
      apply isOfFinOrder_iff_pow_eq_one.mpr
      refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
      change x ^ n = t.1 at hx
      rw [pow_mul, hx]
      exact htm
    refine ⟨xt, ?_⟩
    apply Subtype.ext
    exact hx
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, rfl⟩

/-- The torsion-free quotient modulo `n`th powers. -/
abbrev TorsionFreeModPowerQuotient (U : Type u) [CommGroup U] (n : ℕ) :=
  (U ⧸ CommGroup.torsion U) ⧸
    (powMonoidHom (α := U ⧸ CommGroup.torsion U) n).range

/-- A finite-index torsion-free subgroup computes the exact mod-power cardinality after all
ambient torsion is removed. -/
theorem torsionFreeModPower_card_eq_subgroupModPower
    (D : Subgroup U) (n : ℕ) (hn : 0 < n)
    (hD : ∀ d : D, IsOfFinOrder d → d = 1)
    [Finite (SubgroupPowerAmbientQuotient D n)]
    [Finite (CommGroup.torsion U)] :
    Nat.card (TorsionFreeModPowerQuotient U n) =
      Nat.card (D ⧸ (powMonoidHom (α := D) n).range) := by
  let T := CommGroup.torsion U
  let P := (powMonoidHom (α := U) n).range
  let M := T ⊔ P
  let qT : U →* U ⧸ T := QuotientGroup.mk' T
  have hTP : T ≤ M := le_sup_left
  have hPM : P ≤ M := le_sup_right
  have hmapT : T.map qT = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    exact QuotientGroup.ker_mk' T |>.ge
  have hmapP : P.map qT =
      (powMonoidHom (α := U ⧸ T) n).range := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨(x : U ⧸ T), map_pow qT x n⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective T z
      exact ⟨x ^ n, ⟨x, rfl⟩, map_pow qT x n⟩
  have hmapM : M.map qT =
      (powMonoidHom (α := U ⧸ T) n).range := by
    change (T ⊔ P).map qT = _
    rw [Subgroup.map_sup, hmapT, hmapP]
    simp
  let e : TorsionFreeModPowerQuotient U n ≃* U ⧸ M :=
    (QuotientGroup.quotientMulEquivOfEq hmapM.symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient T M hTP)
  have hrel : P.relIndex M = Nat.card (powMonoidHom (α := U) n).ker := by
    change P.relIndex (T ⊔ P) = _
    rw [Subgroup.relIndex_sup_right]
    unfold Subgroup.relIndex
    rw [ambientPowerRange_inf_torsion_subgroupOf n hn]
    have hkerFiniteIndex :
        (powMonoidHom (α := T) n).ker.FiniteIndex := by
      rw [Subgroup.finiteIndex_iff_finite_quotient]
      infer_instance
    rw [Subgroup.index_range]
    exact Nat.card_congr
      (ambientPowerTorsionEquivTorsionPowerTorsion n hn).symm.toEquiv
  have hraw :=
    ambientModPower_card_eq_powerTorsion_mul_subgroupModPower D n hn hD
  have hindex : P.index =
      Nat.card (powMonoidHom (α := U) n).ker *
        Nat.card (D ⧸ (powMonoidHom (α := D) n).range) := by
    rw [Subgroup.index_eq_card]
    exact hraw
  have hfactor := Subgroup.relIndex_mul_index hPM
  rw [hrel, hindex] at hfactor
  have hpositive : 0 < Nat.card (powMonoidHom (α := U) n).ker := by
    rw [Nat.card_congr
      (ambientPowerTorsionEquivTorsionPowerTorsion n hn).toEquiv]
    exact Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hpositive
  calc
    Nat.card (powMonoidHom (α := U) n).ker *
        Nat.card (TorsionFreeModPowerQuotient U n) =
        Nat.card (powMonoidHom (α := U) n).ker * M.index := by
      rw [Nat.card_congr e.toEquiv, ← Subgroup.index_eq_card]
    _ = Nat.card (powMonoidHom (α := U) n).ker *
        Nat.card (D ⧸ (powMonoidHom (α := D) n).range) := hfactor

end Anabelian.LCFT
