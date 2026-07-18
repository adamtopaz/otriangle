import Otriangle.MonoAnabelian.FiniteExtensionSystem

/-!
# Functoriality of open-subgroup indices

Hoshi's direct systems are indexed by open subgroups, ordered by reverse inclusion.  This module
formalizes the group-theoretic part of that construction: a continuous group equivalence carries
open subgroups order-isomorphically to open subgroups and restricts to a continuous equivalence on
each corresponding pair.
-/

noncomputable section

open CategoryTheory

namespace Anabelian
namespace OTriangle

universe u v

namespace OpenSubgroupIndex

variable {G : Type u} {H : Type v}
variable [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

/-- Transport an open subgroup along a continuous multiplicative equivalence. -/
noncomputable def map (e : G ≃ₜ* H) (U : OpenSubgroup G) : OpenSubgroup H :=
  U.comap e.symm.toMulEquiv.toMonoidHom e.symm.continuous

@[simp]
theorem mem_map (e : G ≃ₜ* H) (U : OpenSubgroup G) (y : H) :
    y ∈ map e U ↔ e.symm y ∈ U :=
  Iff.rfl

/-- A continuous group equivalence transports the poset of open subgroups. -/
noncomputable def orderIso (e : G ≃ₜ* H) : OpenSubgroup G ≃o OpenSubgroup H where
  toFun := map e
  invFun := map e.symm
  left_inv U := by
    apply OpenSubgroup.ext
    intro x
    change e.symm (e x) ∈ U ↔ x ∈ U
    rw [e.symm_apply_apply]
  right_inv V := by
    apply OpenSubgroup.ext
    intro y
    change e (e.symm y) ∈ V ↔ y ∈ V
    rw [e.apply_symm_apply]
  map_rel_iff' {U V} := by
    change (e.symm ⁻¹' (U : Set G) ⊆ e.symm ⁻¹' (V : Set G)) ↔
      (U : Set G) ⊆ V
    exact e.symm.surjective.preimage_subset_preimage_iff

@[simp]
theorem orderIso_apply (e : G ≃ₜ* H) (U : OpenSubgroup G) :
    orderIso e U = map e U :=
  rfl

/-- The equivalence restricted to a corresponding pair of open subgroups. -/
noncomputable def subgroupEquiv (e : G ≃ₜ* H) (U : OpenSubgroup G) :
    U.toSubgroup ≃ₜ* (map e U).toSubgroup where
  toFun x := ⟨e x, by
    change e.symm (e x) ∈ U
    simpa using x.property⟩
  invFun y := ⟨e.symm y, y.property⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x
  right_inv y := by
    apply Subtype.ext
    exact e.apply_symm_apply y
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul e x.1 y.1
  continuous_toFun :=
    (e.continuous.comp continuous_subtype_val).subtype_mk (fun x ↦ by
      change e.symm (e x) ∈ U
      simpa using x.property)
  continuous_invFun :=
    (e.symm.continuous.comp continuous_subtype_val).subtype_mk (fun y ↦ y.property)

@[simp]
theorem subgroupEquiv_apply_coe (e : G ≃ₜ* H) (U : OpenSubgroup G)
    (x : U.toSubgroup) :
    ((subgroupEquiv e U x : (map e U).toSubgroup) : H) = e x :=
  rfl

@[simp]
theorem subgroupEquiv_symm_apply_coe (e : G ≃ₜ* H) (U : OpenSubgroup G)
    (y : (map e U).toSubgroup) :
    (((subgroupEquiv e U).symm y : U.toSubgroup) : G) = e.symm y :=
  rfl

end OpenSubgroupIndex

namespace LocalGaloisGroup

/-- Open subgroups ordered by reverse inclusion, the filtered index used in Definition 4.1. -/
abbrev OpenSubgroupIndex (G : LocalGaloisGroup.{u}) :=
  (OpenSubgroup G.toProfiniteGrp)ᵒᵈ

/-- A group isomorphism transports the reverse-inclusion open-subgroup index. -/
noncomputable def openSubgroupIndexEquiv {G H : LocalGaloisGroup.{u}} (f : G ⟶ H) :
    G.OpenSubgroupIndex ≃o H.OpenSubgroupIndex :=
  (OpenSubgroupIndex.orderIso f.equiv).dual

@[simp]
theorem openSubgroupIndexEquiv_apply {G H : LocalGaloisGroup.{u}} (f : G ⟶ H)
    (U : G.OpenSubgroupIndex) :
    openSubgroupIndexEquiv f U =
      OrderDual.toDual (OpenSubgroupIndex.map f.equiv (OrderDual.ofDual U)) :=
  rfl

/-- Identity transport fixes the open-subgroup index. -/
theorem openSubgroupIndexEquiv_id (G : LocalGaloisGroup.{u}) :
    openSubgroupIndexEquiv (𝟙 G) = OrderIso.refl (G.OpenSubgroupIndex) := by
  apply OrderIso.ext
  funext U
  apply OpenSubgroup.ext
  intro x
  rfl

/-- Transport of open-subgroup indices respects composition of group isomorphisms. -/
theorem openSubgroupIndexEquiv_comp {G H I : LocalGaloisGroup.{u}}
    (f : G ⟶ H) (g : H ⟶ I) :
    openSubgroupIndexEquiv (f ≫ g) =
      (openSubgroupIndexEquiv f).trans (openSubgroupIndexEquiv g) := by
  apply OrderIso.ext
  funext U
  apply OpenSubgroup.ext
  intro x
  rfl

/-- The ambient group isomorphism restricts to the corresponding open subgroups. -/
noncomputable def openSubgroupEquiv {G H : LocalGaloisGroup.{u}} (f : G ⟶ H)
    (U : G.OpenSubgroupIndex) :
    (OrderDual.ofDual U).toSubgroup ≃ₜ*
      (OrderDual.ofDual (openSubgroupIndexEquiv f U)).toSubgroup :=
  Anabelian.OTriangle.OpenSubgroupIndex.subgroupEquiv f.equiv (OrderDual.ofDual U)

end LocalGaloisGroup
end OTriangle
end Anabelian
