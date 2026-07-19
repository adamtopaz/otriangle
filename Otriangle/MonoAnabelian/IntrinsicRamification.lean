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

instance inertiaSubgroupNormal (p : ℕ) : (inertiaSubgroup P p).Normal :=
  inertiaSubgroup_normal P p

instance wildInertiaSubgroupNormal (p : ℕ) : (wildInertiaSubgroup P p).Normal :=
  wildInertiaSubgroup_normal P p

/-- The intrinsic unramified quotient `G / I(G,p)`. -/
abbrev inertiaQuotient (p : ℕ) : Type u :=
  P ⧸ inertiaSubgroup P p

/-- The representative-level characterization of arithmetic Frobenius from Hoshi's Lemma 3.7:
conjugation on inertia modulo wild inertia is the `p ^ f` power map.  Expressing the condition in
the ambient group avoids choosing representatives in the quotient `I/P`. -/
def IsFrobeniusRepresentative (p f : ℕ) (g : P) : Prop :=
  ∀ (x : P), x ∈ inertiaSubgroup P p →
    g * x * g⁻¹ * (x ^ (p ^ f))⁻¹ ∈ wildInertiaSubgroup P p

/-- A class in `G / I(G,p)` satisfies the intrinsic Frobenius characterization if it has a
representative satisfying the conjugation condition.  Hoshi's Lemma 3.7 supplies existence and
uniqueness for groups of mixed-characteristic-local-field type. -/
def IsFrobeniusClass (p f : ℕ) (c : inertiaQuotient P p) : Prop :=
  ∃ g : P, (QuotientGroup.mk' (inertiaSubgroup P p)) g = c ∧
    IsFrobeniusRepresentative P p f g

/-- The existence-and-uniqueness assertion isolated in Hoshi's Lemma 3.7(ii). -/
def HasUniqueFrobeniusClass (p f : ℕ) : Prop :=
  ∃! c : inertiaQuotient P p, IsFrobeniusClass P p f c

/-- The unique intrinsic Frobenius class, conditional on the arithmetic existence-and-uniqueness
statement. -/
noncomputable def frobeniusClass (p f : ℕ) (h : HasUniqueFrobeniusClass P p f) :
    inertiaQuotient P p :=
  h.exists.choose

theorem frobeniusClass_spec (p f : ℕ) (h : HasUniqueFrobeniusClass P p f) :
    IsFrobeniusClass P p f (frobeniusClass P p f h) :=
  h.exists.choose_spec

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

theorem map_mem_inertiaSubgroup_iff (e : P ≃ₜ* Q) (p : ℕ) (x : P) :
    e x ∈ inertiaSubgroup Q p ↔ x ∈ inertiaSubgroup P p := by
  rw [← map_inertiaSubgroup e p, Subgroup.mem_map_equiv]
  simp

theorem map_mem_wildInertiaSubgroup_iff (e : P ≃ₜ* Q) (p : ℕ) (x : P) :
    e x ∈ wildInertiaSubgroup Q p ↔ x ∈ wildInertiaSubgroup P p := by
  rw [← map_wildInertiaSubgroup e p, Subgroup.mem_map_equiv]
  simp

/-- The representative-level Frobenius characterization is intrinsic under continuous group
equivalence. -/
theorem isFrobeniusRepresentative_map_iff (e : P ≃ₜ* Q) (p f : ℕ) (g : P) :
    IsFrobeniusRepresentative Q p f (e g) ↔
      IsFrobeniusRepresentative P p f g := by
  constructor
  · intro hg x hx
    apply (map_mem_wildInertiaSubgroup_iff e p _).mp
    simpa only [map_mul, map_inv, map_pow] using
      hg (e x) ((map_mem_inertiaSubgroup_iff e p x).mpr hx)
  · intro hg y hy
    have hy' : e.symm y ∈ inertiaSubgroup P p :=
      (map_mem_inertiaSubgroup_iff e p (e.symm y)).mp (by simpa using hy)
    have hwild := hg (e.symm y) hy'
    have hmapped := (map_mem_wildInertiaSubgroup_iff e p _).mpr hwild
    simpa only [map_mul, map_inv, map_pow, e.apply_symm_apply] using hmapped

/-- A continuous group equivalence induces the canonical equivalence of intrinsic unramified
quotients. -/
noncomputable def inertiaQuotientEquiv (e : P ≃ₜ* Q) (p : ℕ) :
    inertiaQuotient P p ≃* inertiaQuotient Q p :=
  QuotientGroup.congr (inertiaSubgroup P p) (inertiaSubgroup Q p)
    e.toMulEquiv (map_inertiaSubgroup e p)

@[simp]
theorem inertiaQuotientEquiv_mk (e : P ≃ₜ* Q) (p : ℕ) (g : P) :
    inertiaQuotientEquiv e p ((QuotientGroup.mk' (inertiaSubgroup P p)) g) =
      (QuotientGroup.mk' (inertiaSubgroup Q p)) (e g) :=
  QuotientGroup.congr_mk _ _ _ _ g

/-- The intrinsic Frobenius-class predicate is preserved and reflected on the intrinsic
unramified quotients. -/
theorem isFrobeniusClass_map_iff (e : P ≃ₜ* Q) (p f : ℕ)
    (c : inertiaQuotient P p) :
    IsFrobeniusClass Q p f (inertiaQuotientEquiv e p c) ↔
      IsFrobeniusClass P p f c := by
  constructor
  · rintro ⟨h, hh, hrep⟩
    refine ⟨e.symm h, ?_, ?_⟩
    · apply (inertiaQuotientEquiv e p).injective
      rw [inertiaQuotientEquiv_mk, e.apply_symm_apply, hh]
    · apply (isFrobeniusRepresentative_map_iff e p f (e.symm h)).mp
      simpa using hrep
  · rintro ⟨g, hg, hrep⟩
    refine ⟨e g, ?_, (isFrobeniusRepresentative_map_iff e p f g).mpr hrep⟩
    rw [← inertiaQuotientEquiv_mk, hg]

/-- Existence and uniqueness of the intrinsically characterized Frobenius class are invariant
under continuous group equivalence. -/
theorem hasUniqueFrobeniusClass_congr (e : P ≃ₜ* Q) (p f : ℕ) :
    HasUniqueFrobeniusClass P p f ↔ HasUniqueFrobeniusClass Q p f := by
  exact (inertiaQuotientEquiv e p).toEquiv.existsUnique_congr fun c ↦
    (isFrobeniusClass_map_iff e p f c).symm

/-- Once existence and uniqueness are known, the selected Frobenius class is transported by the
canonical equivalence of unramified quotients. -/
theorem frobeniusClass_map (e : P ≃ₜ* Q) (p f : ℕ)
    (hP : HasUniqueFrobeniusClass P p f) (hQ : HasUniqueFrobeniusClass Q p f) :
    inertiaQuotientEquiv e p (frobeniusClass P p f hP) =
      frobeniusClass Q p f hQ := by
  apply hQ.unique
  · apply (isFrobeniusClass_map_iff e p f _).mpr
    exact frobeniusClass_spec P p f hP
  · exact frobeniusClass_spec Q p f hQ

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

/-- The intrinsic unramified quotient attached to a residue-characteristic candidate. -/
abbrev intrinsicUnramifiedQuotient (G : LocalGaloisGroup.{u}) (p : ℕ) : Type u :=
  IntrinsicRamification.inertiaQuotient G.toProfiniteGrp p

/-- Hoshi's Frobenius existence-and-uniqueness assertion, using the residue degree reconstructed
from the group. -/
def HasUniqueIntrinsicFrobeniusClass (G : LocalGaloisGroup.{u}) (p : ℕ) : Prop :=
  IntrinsicRamification.HasUniqueFrobeniusClass G.toProfiniteGrp p
    (G.groupTheoreticResidueDegree p)

/-- The intrinsically characterized Frobenius class, conditional on Hoshi's arithmetic
existence-and-uniqueness assertion. -/
noncomputable def intrinsicFrobeniusClass (G : LocalGaloisGroup.{u}) (p : ℕ)
    (h : G.HasUniqueIntrinsicFrobeniusClass p) : G.intrinsicUnramifiedQuotient p :=
  IntrinsicRamification.frobeniusClass G.toProfiniteGrp p
    (G.groupTheoreticResidueDegree p) h

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

/-- The canonical equivalence of intrinsic unramified quotients induced by a local Galois-group
morphism. -/
noncomputable def intrinsicUnramifiedQuotientEquiv {G H : LocalGaloisGroup.{u}}
    (f : G ⟶ H) (p : ℕ) :
    G.intrinsicUnramifiedQuotient p ≃* H.intrinsicUnramifiedQuotient p :=
  IntrinsicRamification.inertiaQuotientEquiv f.equiv p

/-- Hoshi's Frobenius existence-and-uniqueness assertion is invariant under arbitrary local
Galois-group isomorphisms. -/
theorem hasUniqueIntrinsicFrobeniusClass_iff {G H : LocalGaloisGroup.{u}}
    (f : G ⟶ H) (p : ℕ) :
    G.HasUniqueIntrinsicFrobeniusClass p ↔ H.HasUniqueIntrinsicFrobeniusClass p := by
  unfold HasUniqueIntrinsicFrobeniusClass
  rw [G.groupTheoreticResidueDegree_eq f p]
  exact IntrinsicRamification.hasUniqueFrobeniusClass_congr f.equiv p
    (H.groupTheoreticResidueDegree p)

end LocalGaloisGroup
end OTriangle
end Anabelian
