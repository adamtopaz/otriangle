import Otriangle.MonoAnabelian.ResidueProcyclic
import Mathlib.GroupTheory.Torsion

/-!
# The unramified factor modulo torsion and prime powers

The Frobenius direction in the residue absolute Galois group survives quotienting by torsion.
For every prime `p`, its torsion-free quotient still has exactly `p` classes modulo `p`th powers.
This isolates the rank-one unramified summand in Hoshi's calculation of the torsion-free
abelianization.
-/

noncomputable section

namespace Anabelian
namespace LCFT

open OTriangle

universe u

theorem residueFrobenius_not_pow_mod_torsion
    (K : PointedMixedCharLocalField.{u}) (p : ℕ) (hp : p.Prime)
    (sigma : ResidueAbsoluteGaloisGroup K) :
    residueFrobenius K * (sigma ^ p)⁻¹ ∉
      CommGroup.torsion (ResidueAbsoluteGaloisGroup K) := by
  intro ht
  have htfin : IsOfFinOrder (residueFrobenius K * (sigma ^ p)⁻¹) := ht
  obtain ⟨m, hm, htm⟩ := htfin.exists_pow_eq_one
  let d := p * m
  have hd : 0 < d := Nat.mul_pos hp.pos hm
  letI : NeZero d := ⟨Nat.ne_zero_of_lt hd⟩
  letI := Fintype.ofFinite (ResidueField K)
  let L := residueFiniteGaloisIntermediateField K d
  letI : Finite L := Module.finite_of_finite (ResidueField K)
  letI : Fintype (L ≃ₐ[ResidueField K] L) := Fintype.ofFinite _
  letI : IsCyclic (L ≃ₐ[ResidueField K] L) := inferInstance
  let t : ResidueAbsoluteGaloisGroup K :=
    residueFrobenius K * (sigma ^ p)⁻¹
  have hrelation : residueFrobenius K = t * sigma ^ p := by
    simp [t]
  have hres := congrArg (AlgEquiv.restrictNormalHom L) hrelation
  have hres' : finiteResidueFrobenius K L =
      t.restrictNormal L * (sigma.restrictNormal L) ^ p := by
    rw [map_mul, map_pow] at hres
    change (residueFrobenius K).restrictNormal L =
      t.restrictNormal L * (sigma.restrictNormal L) ^ p at hres
    rw [residueFrobenius_restrictNormal] at hres
    exact hres
  have htres : (t.restrictNormal L) ^ m = 1 := by
    have h := congrArg (AlgEquiv.restrictNormalHom L) htm
    rw [map_pow, map_one] at h
    exact h
  have hcard : Fintype.card (L ≃ₐ[ResidueField K] L) = d := by
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank,
      residueFiniteGaloisIntermediateField_finrank]
  have hsigres : (sigma.restrictNormal L) ^ d = 1 := by
    rw [← hcard]
    exact pow_card_eq_one
  have hcomm : Commute (t.restrictNormal L) ((sigma.restrictNormal L) ^ p) :=
    IsMulCommutative.is_comm.comm _ _
  have hfrobm : (finiteResidueFrobenius K L) ^ m = 1 := by
    rw [hres', hcomm.mul_pow, htres, one_mul,
      ← pow_mul, show p * m = d from rfl,
      hsigres]
  have hfrob_order : orderOf (finiteResidueFrobenius K L) = d := by
    change orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic (ResidueField K) L) = d
    rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
      residueFiniteGaloisIntermediateField_finrank]
  have hdvd : d ∣ m := by
    rw [← hfrob_order]
    exact orderOf_dvd_of_pow_eq_one hfrobm
  have hle : d ≤ m := Nat.le_of_dvd hm hdvd
  dsimp [d] at hle
  nlinarith [hp.two_le]

abbrev ResidueTorsionFreeQuotient (K : PointedMixedCharLocalField.{u}) :=
  ResidueAbsoluteGaloisGroup K ⧸ CommGroup.torsion (ResidueAbsoluteGaloisGroup K)

abbrev ResidueTorsionFreeModPowerQuotient
    (K : PointedMixedCharLocalField.{u}) (p : ℕ) :=
  ResidueTorsionFreeQuotient K ⧸
    (powMonoidHom (α := ResidueTorsionFreeQuotient K) p).range

noncomputable def residueModPowerToTorsionFreeModPower
    (K : PointedMixedCharLocalField.{u}) (p : ℕ) :
    (ResidueAbsoluteGaloisGroup K ⧸
      (powMonoidHom (α := ResidueAbsoluteGaloisGroup K) p).range) →*
      ResidueTorsionFreeModPowerQuotient K p := by
  let T := CommGroup.torsion (ResidueAbsoluteGaloisGroup K)
  let H := (powMonoidHom (α := ResidueAbsoluteGaloisGroup K) p).range
  let qT : ResidueAbsoluteGaloisGroup K →*
      ResidueTorsionFreeQuotient K := QuotientGroup.mk' T
  let HT := (powMonoidHom (α := ResidueTorsionFreeQuotient K) p).range
  exact QuotientGroup.map H HT qT (by
    rintro _ ⟨x, rfl⟩
    exact ⟨qT x, by simp [qT]⟩)

theorem residueModPowerToTorsionFreeModPower_surjective
    (K : PointedMixedCharLocalField.{u}) (p : ℕ) :
    Function.Surjective (residueModPowerToTorsionFreeModPower K p) := by
  intro y
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective
    ((powMonoidHom (α := ResidueTorsionFreeQuotient K) p).range) y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
    (CommGroup.torsion (ResidueAbsoluteGaloisGroup K)) z
  exact ⟨(x : ResidueAbsoluteGaloisGroup K ⧸
    (powMonoidHom (α := ResidueAbsoluteGaloisGroup K) p).range), rfl⟩

theorem residueTorsionFreeModPowerQuotient_card_eq_prime
    (K : PointedMixedCharLocalField.{u}) (p : ℕ) (hp : p.Prime) :
    Nat.card (ResidueTorsionFreeModPowerQuotient K p) = p := by
  letI := Fintype.ofFinite (ResidueField K)
  letI : IsGalois (ResidueField K) (AlgebraicClosureResidueField K) := ⟨⟩
  let source := ResidueAbsoluteGaloisGroup K ⧸
    (powMonoidHom (α := ResidueAbsoluteGaloisGroup K) p).range
  let f : source →* ResidueTorsionFreeModPowerQuotient K p :=
    residueModPowerToTorsionFreeModPower K p
  letI : Finite source :=
    OTriangle.TopologicalProcyclic.modPower_finite
      (residueFrobenius K) (residueFrobenius_zpowers_topologicalClosure K)
      p hp.pos
  letI : Finite (ResidueTorsionFreeModPowerQuotient K p) :=
    Finite.of_surjective f (residueModPowerToTorsionFreeModPower_surjective K p)
  let sourceGenerator : source := residueFrobenius K
  let g : ResidueTorsionFreeModPowerQuotient K p := f sourceGenerator
  have hgpow : g ^ p = 1 := by
    rw [← map_pow]
    change f ((residueFrobenius K ^ p : ResidueAbsoluteGaloisGroup K) : source) = 1
    rw [show ((residueFrobenius K ^ p : ResidueAbsoluteGaloisGroup K) : source) = 1 by
      rw [QuotientGroup.eq_one_iff]
      exact ⟨residueFrobenius K, rfl⟩, map_one]
  have hg_ne : g ≠ 1 := by
    intro hg
    let qT : ResidueAbsoluteGaloisGroup K →*
        ResidueTorsionFreeQuotient K :=
      QuotientGroup.mk' (CommGroup.torsion (ResidueAbsoluteGaloisGroup K))
    have hmem : qT (residueFrobenius K) ∈
        (powMonoidHom (α := ResidueTorsionFreeQuotient K) p).range := by
      rw [← QuotientGroup.eq_one_iff]
      exact hg
    obtain ⟨z, hz⟩ := hmem
    obtain ⟨sigma, rfl⟩ := QuotientGroup.mk'_surjective
      (CommGroup.torsion (ResidueAbsoluteGaloisGroup K)) z
    change qT (sigma ^ p) = qT (residueFrobenius K) at hz
    change ((sigma ^ p : ResidueAbsoluteGaloisGroup K) :
      ResidueTorsionFreeQuotient K) =
      ((residueFrobenius K : ResidueAbsoluteGaloisGroup K) :
        ResidueTorsionFreeQuotient K) at hz
    rw [QuotientGroup.eq_iff_div_mem] at hz
    apply residueFrobenius_not_pow_mod_torsion K p hp sigma
    have hinv := (CommGroup.torsion (ResidueAbsoluteGaloisGroup K)).inv_mem hz
    simpa [div_eq_mul_inv, mul_comm] using hinv
  have hord_ne : orderOf g ≠ 1 := by
    intro h
    exact hg_ne (orderOf_eq_one_iff.mp h)
  have hord : orderOf g = p :=
    (hp.eq_one_or_self_of_dvd (orderOf g)
      (orderOf_dvd_of_pow_eq_one hgpow)).resolve_left hord_ne
  have hsourceTop : Subgroup.zpowers sourceGenerator = ⊤ :=
    OTriangle.TopologicalProcyclic.quotient_zpowers_eq_top
      (residueFrobenius K) (residueFrobenius_zpowers_topologicalClosure K)
      p hp.pos
  have htargetTop : Subgroup.zpowers g = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := residueModPowerToTorsionFreeModPower_surjective K p y
    have hx : x ∈ Subgroup.zpowers sourceGenerator := by rw [hsourceTop]; exact Subgroup.mem_top x
    obtain ⟨z, hz⟩ := hx
    refine ⟨z, ?_⟩
    rw [← hz, map_zpow]
  rw [← orderOf_eq_card_of_zpowers_eq_top htargetTop, hord]

end LCFT
end Anabelian
