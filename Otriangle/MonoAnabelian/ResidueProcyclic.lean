import Otriangle.MonoAnabelian.ProcyclicPowerQuotient
import Otriangle.MonoAnabelian.ResidueFiniteExtensions
import Mathlib.FieldTheory.Galois.Profinite

/-!
# Procyclicity of the residue absolute Galois group

For the finite residue field of a mixed-characteristic local field, arithmetic Frobenius
restricts to the usual Frobenius on every finite Galois subextension of the chosen algebraic
closure.  Consequently its integral powers are dense in the residue absolute Galois group.
This is the finite-field input behind the unramified factor in Hoshi's local multiplicative-group
calculation.
-/

open scoped Topology

noncomputable section

namespace Anabelian
namespace LCFT

open OTriangle

universe u

/-- The residue absolute Galois group is commutative. -/
instance residueAbsoluteGaloisGroupCommGroup
    (K : PointedMixedCharLocalField.{u}) :
    CommGroup (ResidueAbsoluteGaloisGroup K) :=
  { (inferInstance : Group (ResidueAbsoluteGaloisGroup K)) with
    mul_comm := K.residueGaloisMap_commutes }

/-- The standard Frobenius automorphism of a finite residue extension. -/
noncomputable def finiteResidueFrobenius
    (K : PointedMixedCharLocalField.{u})
    (L : FiniteGaloisIntermediateField (ResidueField K)
      (AlgebraicClosureResidueField K)) : L ≃ₐ[ResidueField K] L := by
  letI := Fintype.ofFinite (ResidueField K)
  exact FiniteField.frobeniusAlgEquivOfAlgebraic (ResidueField K) L

/-- Arithmetic Frobenius on the residue algebraic closure restricts to the standard Frobenius
on each finite Galois intermediate field. -/
theorem residueFrobenius_restrictNormal
    (K : PointedMixedCharLocalField.{u})
    (L : FiniteGaloisIntermediateField (ResidueField K)
      (AlgebraicClosureResidueField K)) :
    (residueFrobenius K).restrictNormal L = finiteResidueFrobenius K L := by
  letI := Fintype.ofFinite (ResidueField K)
  apply AlgEquiv.ext
  intro x
  apply (algebraMap L (AlgebraicClosureResidueField K)).injective
  rw [AlgEquiv.restrictNormal_commutes]
  change residueFrobenius K (x : AlgebraicClosureResidueField K) = _
  rw [residueFrobenius_apply]
  change (x : AlgebraicClosureResidueField K) ^ Nat.card (ResidueField K) =
    algebraMap L (AlgebraicClosureResidueField K)
      (x ^ Fintype.card (ResidueField K))
  rw [show Nat.card (ResidueField K) = Fintype.card (ResidueField K) from
    Fintype.card_eq_nat_card.symm]
  rfl

/-- The integral powers of arithmetic Frobenius are dense in the residue absolute Galois group.

The proof uses the Krull neighborhood basis.  On every finite Galois residue extension, every
automorphism is a power of Frobenius; choosing such a power places it in any prescribed coset of
the corresponding fixing subgroup. -/
theorem residueFrobenius_zpowers_topologicalClosure
    (K : PointedMixedCharLocalField.{u}) :
    (Subgroup.zpowers (residueFrobenius K)).topologicalClosure = ⊤ := by
  apply top_unique
  intro σ _
  change σ ∈ closure (Subgroup.zpowers (residueFrobenius K) :
    Set (AlgebraicClosureResidueField K ≃ₐ[ResidueField K]
      AlgebraicClosureResidueField K))
  rw [mem_closure_iff_nhds]
  intro t ht
  let e := Homeomorph.mulLeft σ
  have hpre : e ⁻¹' t ∈ 𝓝 1 := by
    rw [← Filter.mem_map, e.map_nhds_eq]
    simpa [e] using ht
  letI := Fintype.ofFinite (ResidueField K)
  letI : IsGalois (ResidueField K) (AlgebraicClosureResidueField K) := ⟨⟩
  obtain ⟨L, hL⟩ :=
    (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois
      (k := ResidueField K) (K := AlgebraicClosureResidueField K) (e ⁻¹' t)).mp hpre
  letI : Finite L := Module.finite_of_finite (ResidueField K)
  obtain ⟨n, hn⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
      (ResidueField K) L).2 (σ.restrictNormal L)
  have hpow :
      (residueFrobenius K ^ n.1).restrictNormalHom L = σ.restrictNormalHom L := by
    rw [map_pow]
    change ((residueFrobenius K).restrictNormal L) ^ n.1 = σ.restrictNormal L
    rw [residueFrobenius_restrictNormal]
    simpa [finiteResidueFrobenius] using hn
  have hxfix : σ⁻¹ * residueFrobenius K ^ n.1 ∈ L.fixingSubgroup := by
    rw [FiniteGaloisIntermediateField.mem_fixingSubgroup_iff]
    rw [map_mul, map_inv, hpow, inv_mul_cancel]
  have hpower_mem : residueFrobenius K ^ n.1 ∈ t := by
    have hx := hL hxfix
    change σ * (σ⁻¹ * residueFrobenius K ^ n.1) ∈ t at hx
    simpa [mul_assoc] using hx
  exact ⟨residueFrobenius K ^ n.1, hpower_mem,
    Subgroup.npow_mem_zpowers (residueFrobenius K) n.1⟩

/-- The residue absolute Galois group has at most `n` classes modulo `n`th powers. -/
theorem residueModPowerQuotient_card_le
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) (hn : 0 < n) :
    Nat.card (ResidueAbsoluteGaloisGroup K ⧸
      (powMonoidHom (α := ResidueAbsoluteGaloisGroup K) n).range) ≤ n := by
  letI := Fintype.ofFinite (ResidueField K)
  letI : IsGalois (ResidueField K) (AlgebraicClosureResidueField K) := ⟨⟩
  exact OTriangle.TopologicalProcyclic.modPower_card_le
    (residueFrobenius K) (residueFrobenius_zpowers_topologicalClosure K) n hn

/-- Arithmetic Frobenius is not an `n`th power when `n > 1`.

Restrict a hypothetical `n`th root to the explicit degree-`n` residue extension.  Every
automorphism of that extension has `n`th power one, whereas its Frobenius generator has order
exactly `n`. -/
theorem residueFrobenius_not_mem_powRange
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) (hn : 1 < n) :
    residueFrobenius K ∉
      (powMonoidHom (α := ResidueAbsoluteGaloisGroup K) n).range := by
  letI : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  letI := Fintype.ofFinite (ResidueField K)
  intro hmem
  obtain ⟨σ, hσ⟩ := hmem
  change σ ^ n = residueFrobenius K at hσ
  let L := residueFiniteGaloisIntermediateField K n
  have hres := congrArg (AlgEquiv.restrictNormalHom L) hσ
  have hres' : (σ.restrictNormal L) ^ n = finiteResidueFrobenius K L := by
    rw [map_pow] at hres
    change (σ.restrictNormal L) ^ n = (residueFrobenius K).restrictNormal L at hres
    rw [residueFrobenius_restrictNormal] at hres
    exact hres
  letI : Finite L := Module.finite_of_finite (ResidueField K)
  letI : Fintype (L ≃ₐ[ResidueField K] L) := Fintype.ofFinite _
  have hcard : Fintype.card (L ≃ₐ[ResidueField K] L) = n := by
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank,
      residueFiniteGaloisIntermediateField_finrank]
  have hσpow : (σ.restrictNormal L) ^ n = 1 := by
    rw [← hcard]
    exact pow_card_eq_one
  have hfrob_one : finiteResidueFrobenius K L = 1 := hres'.symm.trans hσpow
  have hfrob_order : orderOf (finiteResidueFrobenius K L) = n := by
    change orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic (ResidueField K) L) = n
    rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
      residueFiniteGaloisIntermediateField_finrank]
  have : n = 1 := by
    rw [← hfrob_order, hfrob_one, orderOf_one]
  omega

/-- At a prime `p`, the residue absolute Galois group has exactly `p` classes modulo `p`th
powers. -/
theorem residueModPowerQuotient_card_eq_prime
    (K : PointedMixedCharLocalField.{u}) (p : ℕ) (hp : p.Prime) :
    Nat.card (ResidueAbsoluteGaloisGroup K ⧸
      (powMonoidHom (α := ResidueAbsoluteGaloisGroup K) p).range) = p := by
  letI := Fintype.ofFinite (ResidueField K)
  letI : IsGalois (ResidueField K) (AlgebraicClosureResidueField K) := ⟨⟩
  letI : Finite (ResidueAbsoluteGaloisGroup K ⧸
      (powMonoidHom (α := ResidueAbsoluteGaloisGroup K) p).range) :=
    OTriangle.TopologicalProcyclic.modPower_finite
      (residueFrobenius K) (residueFrobenius_zpowers_topologicalClosure K)
      p hp.pos
  let H : Subgroup (ResidueAbsoluteGaloisGroup K) :=
    (powMonoidHom (α := ResidueAbsoluteGaloisGroup K) p).range
  let Q := ResidueAbsoluteGaloisGroup K ⧸ H
  let q : ResidueAbsoluteGaloisGroup K →* Q := QuotientGroup.mk' H
  let g : Q := q (residueFrobenius K)
  have hgpow : g ^ p = 1 := by
    change q (residueFrobenius K ^ p) = 1
    change ((residueFrobenius K ^ p : ResidueAbsoluteGaloisGroup K) :
      ResidueAbsoluteGaloisGroup K ⧸ H) = 1
    rw [QuotientGroup.eq_one_iff]
    exact ⟨residueFrobenius K, rfl⟩
  have hg_ne : g ≠ 1 := by
    intro hg
    apply residueFrobenius_not_mem_powRange K p hp.one_lt
    change residueFrobenius K ∈ H
    change ((residueFrobenius K : ResidueAbsoluteGaloisGroup K) :
      ResidueAbsoluteGaloisGroup K ⧸ H) = 1 at hg
    rw [QuotientGroup.eq_one_iff] at hg
    exact hg
  have hord_ne : orderOf g ≠ 1 := by
    intro h
    exact hg_ne (orderOf_eq_one_iff.mp h)
  have hord : orderOf g = p :=
    (hp.eq_one_or_self_of_dvd (orderOf g)
      (orderOf_dvd_of_pow_eq_one hgpow)).resolve_left hord_ne
  have htop : Subgroup.zpowers g = ⊤ :=
    OTriangle.TopologicalProcyclic.quotient_zpowers_eq_top
      (residueFrobenius K) (residueFrobenius_zpowers_topologicalClosure K)
      p hp.pos
  rw [← orderOf_eq_card_of_zpowers_eq_top htop, hord]

end LCFT
end Anabelian
