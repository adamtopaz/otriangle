import Otriangle.MonoAnabelian.GroupInvariants

/-!
# Intrinsic ramification subgroups

This module formalizes the group-theoretic intersections in Hoshi's Definition 3.5.  For a
topological group `P` and a prime candidate `p`, the numerical ramification index is read from the
topological abelianization.  The intrinsic inertia subgroup is the intersection of the open normal
subgroups having the same index, and the intrinsic wild-inertia subgroup is the intersection of
the open normal subgroups whose relative index is positive and prime to `p`.

At this stage these are intrinsic group-theoretic constructions.  Their identification with the
classical inertia and wild-inertia subgroups of a mixed-characteristic local field is a separate
arithmetic theorem.
-/

noncomputable section

namespace Anabelian
namespace OTriangle

universe u v

namespace IntrinsicRamification

variable (P : Type u) [Group P] [TopologicalSpace P] [IsTopologicalGroup P]

/-- Hoshi's numerical ramification index, evaluated on the topological abelianization of a
topological group. -/
noncomputable def ramificationIndex (p : ℕ) : ℕ :=
  GroupTheoreticInvariants.ramificationIndex (_root_.TopologicalAbelianization P) p

/-- The numerical ramification index is invariant under continuous group equivalence. -/
theorem ramificationIndex_congr
    {Q : Type v} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (e : P ≃ₜ* Q) (p : ℕ) :
    ramificationIndex P p = ramificationIndex Q p :=
  GroupTheoreticInvariants.ramificationIndex_congr
    (TopologicalAbelianization.congr e) p

/-- An open subgroup belongs to the inertia intersection when it is normal and has the same
group-theoretic ramification index as the ambient group. -/
def IsInertiaNeighborhood (p : ℕ) (U : OpenSubgroup P) : Prop :=
  U.toSubgroup.Normal ∧
    ramificationIndex U.toSubgroup p = ramificationIndex P p

/-- An open subgroup belongs to the wild-inertia intersection when it is normal and its
group-theoretic ramification index differs from that of the ambient group by a positive factor
prime to `p`. -/
def IsWildInertiaNeighborhood (p : ℕ) (U : OpenSubgroup P) : Prop :=
  U.toSubgroup.Normal ∧
    ∃ q : ℕ, 0 < q ∧ Nat.Coprime q p ∧
      ramificationIndex U.toSubgroup p = ramificationIndex P p * q

/-- Hoshi's intrinsic inertia subgroup: the intersection of the equal-index open normal
subgroups. -/
def inertiaSubgroup (p : ℕ) : Subgroup P :=
  ⨅ (U : OpenSubgroup P) (_ : IsInertiaNeighborhood P p U), U.toSubgroup

/-- Hoshi's intrinsic wild-inertia subgroup: the intersection of the open normal subgroups with
positive prime-to-`p` relative ramification index. -/
def wildInertiaSubgroup (p : ℕ) : Subgroup P :=
  ⨅ (U : OpenSubgroup P) (_ : IsWildInertiaNeighborhood P p U), U.toSubgroup

theorem mem_inertiaSubgroup_iff (p : ℕ) (x : P) :
    x ∈ inertiaSubgroup P p ↔
      ∀ (U : OpenSubgroup P), IsInertiaNeighborhood P p U → x ∈ U := by
  simp only [inertiaSubgroup, Subgroup.mem_iInf]
  aesop

theorem mem_wildInertiaSubgroup_iff (p : ℕ) (x : P) :
    x ∈ wildInertiaSubgroup P p ↔
      ∀ (U : OpenSubgroup P), IsWildInertiaNeighborhood P p U → x ∈ U := by
  simp only [wildInertiaSubgroup, Subgroup.mem_iInf]
  aesop

/-- The intrinsic inertia intersection is normal. -/
theorem inertiaSubgroup_normal (p : ℕ) : (inertiaSubgroup P p).Normal := by
  apply Subgroup.normal_iInf_normal
  intro U
  apply Subgroup.normal_iInf_normal
  intro hU
  exact hU.1

/-- The intrinsic wild-inertia intersection is normal. -/
theorem wildInertiaSubgroup_normal (p : ℕ) : (wildInertiaSubgroup P p).Normal := by
  apply Subgroup.normal_iInf_normal
  intro U
  apply Subgroup.normal_iInf_normal
  intro hU
  exact hU.1

/-- Wild inertia is contained in inertia.  Indeed, every equal-index neighborhood occurs among
the prime-to-`p` relative-index neighborhoods with factor one. -/
theorem wildInertiaSubgroup_le_inertiaSubgroup (p : ℕ) :
    wildInertiaSubgroup P p ≤ inertiaSubgroup P p := by
  intro x hx
  rw [mem_inertiaSubgroup_iff]
  intro U hU
  rw [mem_wildInertiaSubgroup_iff] at hx
  apply hx U
  exact ⟨hU.1, 1, Nat.zero_lt_one, Nat.coprime_one_left p, by simpa using hU.2⟩

section Transport

variable {P : Type u} {Q : Type v}
variable [Group P] [Group Q] [TopologicalSpace P] [TopologicalSpace Q]
variable [IsTopologicalGroup P] [IsTopologicalGroup Q]

omit [IsTopologicalGroup P] [IsTopologicalGroup Q] in
/-- Normality of an open subgroup is preserved and reflected by transport along a continuous
group equivalence. -/
theorem map_normal_iff (e : P ≃ₜ* Q) (U : OpenSubgroup P) :
    (OpenSubgroupIndex.map e U).toSubgroup.Normal ↔ U.toSubgroup.Normal := by
  have hmap :
      Subgroup.map e.toMulEquiv.toMonoidHom U.toSubgroup =
        (OpenSubgroupIndex.map e U).toSubgroup := by
    exact Subgroup.map_equiv_eq_comap_symm e.toMulEquiv U.toSubgroup
  rw [← hmap]
  exact MulEquiv.normal_map_iff

/-- Equal-index open normal subgroups correspond under a continuous group equivalence. -/
theorem isInertiaNeighborhood_map_iff (e : P ≃ₜ* Q) (p : ℕ)
    (U : OpenSubgroup P) :
    IsInertiaNeighborhood Q p (OpenSubgroupIndex.map e U) ↔
      IsInertiaNeighborhood P p U := by
  constructor
  · rintro ⟨hnormal, hindex⟩
    refine ⟨(map_normal_iff e U).mp hnormal, ?_⟩
    calc
      ramificationIndex U.toSubgroup p =
          ramificationIndex (OpenSubgroupIndex.map e U).toSubgroup p :=
        ramificationIndex_congr U.toSubgroup (OpenSubgroupIndex.subgroupEquiv e U) p
      _ = ramificationIndex Q p := hindex
      _ = ramificationIndex P p := (ramificationIndex_congr P e p).symm
  · rintro ⟨hnormal, hindex⟩
    refine ⟨(map_normal_iff e U).mpr hnormal, ?_⟩
    calc
      ramificationIndex (OpenSubgroupIndex.map e U).toSubgroup p =
          ramificationIndex U.toSubgroup p :=
        (ramificationIndex_congr U.toSubgroup
          (OpenSubgroupIndex.subgroupEquiv e U) p).symm
      _ = ramificationIndex P p := hindex
      _ = ramificationIndex Q p := ramificationIndex_congr P e p

/-- Prime-to-`p` relative-index open normal subgroups correspond under a continuous group
equivalence. -/
theorem isWildInertiaNeighborhood_map_iff (e : P ≃ₜ* Q) (p : ℕ)
    (U : OpenSubgroup P) :
    IsWildInertiaNeighborhood Q p (OpenSubgroupIndex.map e U) ↔
      IsWildInertiaNeighborhood P p U := by
  constructor
  · rintro ⟨hnormal, q, hq, hcoprime, hindex⟩
    refine ⟨(map_normal_iff e U).mp hnormal, q, hq, hcoprime, ?_⟩
    calc
      ramificationIndex U.toSubgroup p =
          ramificationIndex (OpenSubgroupIndex.map e U).toSubgroup p :=
        ramificationIndex_congr U.toSubgroup (OpenSubgroupIndex.subgroupEquiv e U) p
      _ = ramificationIndex Q p * q := hindex
      _ = ramificationIndex P p * q := by rw [ramificationIndex_congr P e p]
  · rintro ⟨hnormal, q, hq, hcoprime, hindex⟩
    refine ⟨(map_normal_iff e U).mpr hnormal, q, hq, hcoprime, ?_⟩
    calc
      ramificationIndex (OpenSubgroupIndex.map e U).toSubgroup p =
          ramificationIndex U.toSubgroup p :=
        (ramificationIndex_congr U.toSubgroup
          (OpenSubgroupIndex.subgroupEquiv e U) p).symm
      _ = ramificationIndex P p * q := hindex
      _ = ramificationIndex Q p * q := by rw [ramificationIndex_congr P e p]

/-- Intrinsic inertia is carried exactly onto intrinsic inertia by every continuous group
equivalence. -/
theorem map_inertiaSubgroup (e : P ≃ₜ* Q) (p : ℕ) :
    (inertiaSubgroup P p).map e.toMulEquiv.toMonoidHom = inertiaSubgroup Q p := by
  ext y
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hy
    rw [mem_inertiaSubgroup_iff] at hy ⊢
    intro V hV
    let U := OpenSubgroupIndex.map e.symm V
    have hU : IsInertiaNeighborhood P p U :=
      (isInertiaNeighborhood_map_iff e.symm p V).mpr hV
    have hmem := hy U hU
    change e (e.symm y) ∈ V at hmem
    simpa using hmem
  · intro hy
    rw [mem_inertiaSubgroup_iff] at hy ⊢
    intro U hU
    have hmap : IsInertiaNeighborhood Q p (OpenSubgroupIndex.map e U) :=
      (isInertiaNeighborhood_map_iff e p U).mpr hU
    have hmem := hy (OpenSubgroupIndex.map e U) hmap
    exact hmem

/-- Intrinsic wild inertia is carried exactly onto intrinsic wild inertia by every continuous
group equivalence. -/
theorem map_wildInertiaSubgroup (e : P ≃ₜ* Q) (p : ℕ) :
    (wildInertiaSubgroup P p).map e.toMulEquiv.toMonoidHom =
      wildInertiaSubgroup Q p := by
  ext y
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hy
    rw [mem_wildInertiaSubgroup_iff] at hy ⊢
    intro V hV
    let U := OpenSubgroupIndex.map e.symm V
    have hU : IsWildInertiaNeighborhood P p U :=
      (isWildInertiaNeighborhood_map_iff e.symm p V).mpr hV
    have hmem := hy U hU
    change e (e.symm y) ∈ V at hmem
    simpa using hmem
  · intro hy
    rw [mem_wildInertiaSubgroup_iff] at hy ⊢
    intro U hU
    have hmap : IsWildInertiaNeighborhood Q p (OpenSubgroupIndex.map e U) :=
      (isWildInertiaNeighborhood_map_iff e p U).mpr hU
    have hmem := hy (OpenSubgroupIndex.map e U) hmap
    exact hmem

end Transport

end IntrinsicRamification

namespace LocalGaloisGroup

/-- The intrinsic inertia subgroup attached to a residue-characteristic candidate. -/
abbrev intrinsicInertiaSubgroup (G : LocalGaloisGroup.{u}) (p : ℕ) :
    Subgroup G.toProfiniteGrp :=
  IntrinsicRamification.inertiaSubgroup G.toProfiniteGrp p

/-- The intrinsic wild-inertia subgroup attached to a residue-characteristic candidate. -/
abbrev intrinsicWildInertiaSubgroup (G : LocalGaloisGroup.{u}) (p : ℕ) :
    Subgroup G.toProfiniteGrp :=
  IntrinsicRamification.wildInertiaSubgroup G.toProfiniteGrp p

/-- A local Galois-group morphism carries intrinsic inertia exactly onto intrinsic inertia. -/
theorem map_intrinsicInertiaSubgroup {G H : LocalGaloisGroup.{u}}
    (f : G ⟶ H) (p : ℕ) :
    (G.intrinsicInertiaSubgroup p).map f.equiv.toMulEquiv.toMonoidHom =
      H.intrinsicInertiaSubgroup p :=
  IntrinsicRamification.map_inertiaSubgroup f.equiv p

/-- A local Galois-group morphism carries intrinsic wild inertia exactly onto intrinsic wild
inertia. -/
theorem map_intrinsicWildInertiaSubgroup {G H : LocalGaloisGroup.{u}}
    (f : G ⟶ H) (p : ℕ) :
    (G.intrinsicWildInertiaSubgroup p).map f.equiv.toMulEquiv.toMonoidHom =
      H.intrinsicWildInertiaSubgroup p :=
  IntrinsicRamification.map_wildInertiaSubgroup f.equiv p

end LocalGaloisGroup
end OTriangle
end Anabelian
