import Otriangle.MonoAnabelian.OneField
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

end LCFT
end Anabelian
