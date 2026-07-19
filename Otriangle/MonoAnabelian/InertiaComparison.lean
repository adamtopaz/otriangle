import Otriangle.MonoAnabelian.FiniteInertiaRestriction
import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# Identification of intrinsic and classical inertia

At a normal open subgroup, Hoshi's equal-index condition is equivalent to containment of the
classical inertia subgroup.  Profinite separation by open normal subgroups then identifies the
intersection of all such neighborhoods with the closed classical inertia subgroup itself.
-/

noncomputable section

namespace Anabelian.OTriangle.LocalGaloisGroup

open LCFT
open scoped Pointwise

universe u

/-- A normal open subgroup is an intrinsic inertia neighborhood exactly when it contains
classical inertia. -/
theorem classicalInertiaSubgroup_le_iff_isInertiaNeighborhood
    (G : LocalGaloisGroup.{u}) (reciprocity : LocalReciprocityFamily.{u})
    (U : OpenSubgroup G.toProfiniteGrp) (hN : U.toSubgroup.Normal) :
    G.classicalInertiaSubgroup ≤ U.toSubgroup ↔
      IntrinsicRamification.IsInertiaNeighborhood G.toProfiniteGrp
        G.presentation.residueChar U := by
  rw [G.classicalInertiaSubgroup_eq_spectral reciprocity,
    G.spectralInertiaSubgroup_le_iff_relativeRamificationIndex_eq_one U hN,
    G.isInertiaNeighborhood_iff_relativeRamificationIndex_eq_one reciprocity U]
  simp only [hN, true_and]

/-- Hoshi's intrinsic inertia intersection agrees with the kernel of the local-field residue
action. -/
theorem intrinsicInertiaSubgroup_eq_classicalInertiaSubgroup
    (G : LocalGaloisGroup.{u}) (reciprocity : LocalReciprocityFamily.{u}) :
    G.intrinsicInertiaSubgroup G.presentation.residueChar =
      G.classicalInertiaSubgroup := by
  let H := G.classicalInertiaSubgroup
  apply le_antisymm
  · intro x hx
    by_contra hxH
    have hHclosed : IsClosed (H : Set G.toProfiniteGrp) := by
      change IsClosed {x : G.toProfiniteGrp |
        G.classicalResidueGaloisMap x = 1}
      exact isClosed_eq G.presentation.residueGaloisMap_continuous continuous_const
    let W : Set G.toProfiniteGrp := (x • (H : Set G.toProfiniteGrp))ᶜ
    have hWopen : IsOpen W :=
      ((Homeomorph.mulLeft x).isClosedMap _ hHclosed).isOpen_compl
    have hWone : 1 ∈ W := by
      refine Set.mem_compl (fun ⟨l, hl, hxl⟩ => ?_)
      change x * l = 1 at hxl
      rw [← inv_eq_iff_mul_eq_one] at hxl
      exact hxH (inv_mem_iff.mp (hxl ▸ hl))
    obtain ⟨N, hNW⟩ :=
      ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWopen hWone
    let USub : Subgroup G.toProfiniteGrp := N.toSubgroup ⊔ H
    have hUopen : IsOpen (USub : Set G.toProfiniteGrp) :=
      Subgroup.isOpen_mono le_sup_left N.isOpen
    let U : OpenSubgroup G.toProfiniteGrp := ⟨USub, hUopen⟩
    letI : H.Normal := G.classicalInertiaSubgroupNormal
    have hUNormal : U.toSubgroup.Normal := by infer_instance
    have hHle : H ≤ U.toSubgroup := le_sup_right
    have hxU : x ∈ U := by
      rw [IntrinsicRamification.mem_inertiaSubgroup_iff] at hx
      apply hx U
      exact (G.classicalInertiaSubgroup_le_iff_isInertiaNeighborhood
        reciprocity U hUNormal).mp hHle
    have hxnot : x ∉ USub := by
      intro hx'
      obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp hx'
      rw [← eq_mul_inv_iff_mul_eq] at hyz
      exact hNW (hyz ▸ hy) (mem_leftCoset x (inv_mem_iff.mpr hz))
    exact hxnot hxU
  · intro x hx
    rw [IntrinsicRamification.mem_inertiaSubgroup_iff]
    intro U hU
    exact (G.classicalInertiaSubgroup_le_iff_isInertiaNeighborhood
      reciprocity U hU.1).mpr hU hx

end Anabelian.OTriangle.LocalGaloisGroup
