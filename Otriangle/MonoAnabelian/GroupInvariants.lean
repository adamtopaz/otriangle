import Otriangle.MonoAnabelian.GroupTransport
import Mathlib.GroupTheory.Torsion

/-!
# Elementary group-theoretic local invariants

This module begins Hoshi's Definition 3.5 at the purely group-theoretic level.  It forms the
torsion-free quotient of a commutative group and measures its quotient by `n`th powers.  Both
constructions are functorial under group equivalences.  Applied to the topological abelianization
of a local absolute Galois group, this proves invariance of the numerical predicate that detects
the residue characteristic in Hoshi's Lemma 3.4.
-/

noncomputable section

open CategoryTheory

namespace Anabelian
namespace OTriangle
namespace GroupTheoreticInvariants

/-- The torsion-free quotient of a commutative group. -/
abbrev torsionFreeQuotient (A : Type*) [CommGroup A] : Type _ :=
  A ⧸ CommGroup.torsion A

/-- A group equivalence descends to the quotients by torsion. -/
noncomputable def torsionFreeQuotientEquiv
    {A B : Type*} [CommGroup A] [CommGroup B] (e : A ≃* B) :
    torsionFreeQuotient A ≃* torsionFreeQuotient B :=
  QuotientGroup.congr (CommGroup.torsion A) (CommGroup.torsion B) e e.map_torsion

/-- The quotient of a commutative group by its subgroup of `n`th powers. -/
abbrev modPowerQuotient (A : Type*) [CommGroup A] (n : ℕ) : Type _ :=
  A ⧸ (powMonoidHom (α := A) n).range

/-- An equivalence descends to quotients by `n`th powers. -/
noncomputable def modPowerQuotientEquiv
    {A B : Type*} [CommGroup A] [CommGroup B] (e : A ≃* B) (n : ℕ) :
    modPowerQuotient A n ≃* modPowerQuotient B n :=
  QuotientGroup.congr (powMonoidHom (α := A) n).range
    (powMonoidHom (α := B) n).range e (e.map_range_powMonoidHom n)

/-- The base-`n` logarithm of the cardinality of the quotient by `n`th powers.  For the
torsion-free abelianization of a local absolute Galois group and prime `n = p`, this is the
quantity used in Hoshi's Lemma 3.4. -/
noncomputable def modPowerRank (A : Type*) [CommGroup A] (n : ℕ) : ℕ :=
  Nat.log n (Nat.card (modPowerQuotient A n))

/-- The mod-power rank is invariant under group equivalence. -/
theorem modPowerRank_congr
    {A B : Type*} [CommGroup A] [CommGroup B] (e : A ≃* B) (n : ℕ) :
    modPowerRank A n = modPowerRank B n := by
  unfold modPowerRank
  rw [Nat.card_congr (modPowerQuotientEquiv e n).toEquiv]

/-- Hoshi's group-theoretic predicate for the residue-characteristic candidate: a prime for which
the torsion-free abelianization has mod-`p` rank at least two. -/
def IsResidueCharacteristicCandidate (A : Type*) [CommGroup A] (p : ℕ) : Prop :=
  p.Prime ∧ 2 ≤ modPowerRank (torsionFreeQuotient A) p

/-- The residue-characteristic candidate predicate is invariant under group equivalence. -/
theorem isResidueCharacteristicCandidate_congr
    {A B : Type*} [CommGroup A] [CommGroup B] (e : A ≃* B) (p : ℕ) :
    IsResidueCharacteristicCandidate A p ↔ IsResidueCharacteristicCandidate B p := by
  unfold IsResidueCharacteristicCandidate
  rw [modPowerRank_congr (torsionFreeQuotientEquiv e) p]

/-- An equivalence restricts to an equivalence between torsion subgroups. -/
noncomputable def torsionEquiv
    {A B : Type*} [CommGroup A] [CommGroup B] (e : A ≃* B) :
    CommGroup.torsion A ≃* CommGroup.torsion B :=
  (e.subgroupMap (CommGroup.torsion A)).trans
    (MulEquiv.subgroupCongr e.map_torsion)

/-- Equivalences carry `p`-primary components onto `p`-primary components. -/
theorem map_primaryComponent
    {A B : Type*} [CommGroup A] [CommGroup B] (e : A ≃* B) (p : ℕ) :
    (CommGroup.primaryComponent A p).map e = CommGroup.primaryComponent B p := by
  ext y
  constructor
  · rintro ⟨x, ⟨k, hk⟩, rfl⟩
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  · rintro ⟨k, hk⟩
    refine ⟨e.symm y, ⟨k, ?_⟩, e.apply_symm_apply y⟩
    apply e.injective
    rw [map_pow, e.apply_symm_apply, hk, map_one]

/-- The prime-to-`p` torsion quotient: torsion modulo its `p`-primary component. -/
abbrev primeToTorsionQuotient (A : Type*) [CommGroup A] (p : ℕ) : Type _ :=
  CommGroup.torsion A ⧸
    CommGroup.primaryComponent (CommGroup.torsion A) p

/-- The prime-to-`p` torsion quotients are invariant under group equivalence. -/
noncomputable def primeToTorsionQuotientEquiv
    {A B : Type*} [CommGroup A] [CommGroup B] (e : A ≃* B) (p : ℕ) :
    primeToTorsionQuotient A p ≃* primeToTorsionQuotient B p :=
  QuotientGroup.congr
    (CommGroup.primaryComponent (CommGroup.torsion A) p)
    (CommGroup.primaryComponent (CommGroup.torsion B) p)
    (torsionEquiv e) (map_primaryComponent (torsionEquiv e) p)

/-- Hoshi's group-theoretic absolute-degree integer at a candidate prime. -/
noncomputable def absoluteDegree (A : Type*) [CommGroup A] (p : ℕ) : ℕ :=
  modPowerRank (torsionFreeQuotient A) p - 1

/-- Hoshi's group-theoretic residue-degree integer at a candidate prime. -/
noncomputable def residueDegree (A : Type*) [CommGroup A] (p : ℕ) : ℕ :=
  Nat.log p (1 + Nat.card (primeToTorsionQuotient A p))

/-- Hoshi's group-theoretic ramification-index integer at a candidate prime. -/
noncomputable def ramificationIndex (A : Type*) [CommGroup A] (p : ℕ) : ℕ :=
  absoluteDegree A p / residueDegree A p

/-- The group-theoretic absolute degree is invariant under equivalence. -/
theorem absoluteDegree_congr
    {A B : Type*} [CommGroup A] [CommGroup B] (e : A ≃* B) (p : ℕ) :
    absoluteDegree A p = absoluteDegree B p := by
  unfold absoluteDegree
  rw [modPowerRank_congr (torsionFreeQuotientEquiv e) p]

/-- The group-theoretic residue degree is invariant under equivalence. -/
theorem residueDegree_congr
    {A B : Type*} [CommGroup A] [CommGroup B] (e : A ≃* B) (p : ℕ) :
    residueDegree A p = residueDegree B p := by
  unfold residueDegree
  rw [Nat.card_congr (primeToTorsionQuotientEquiv e p).toEquiv]

/-- The group-theoretic ramification index is invariant under equivalence. -/
theorem ramificationIndex_congr
    {A B : Type*} [CommGroup A] [CommGroup B] (e : A ≃* B) (p : ℕ) :
    ramificationIndex A p = ramificationIndex B p := by
  unfold ramificationIndex
  rw [absoluteDegree_congr e p, residueDegree_congr e p]

end GroupTheoreticInvariants

namespace LocalGaloisGroup

universe u

/-- The torsion-free topological abelianization of a local Galois group. -/
abbrev torsionFreeAbelianization (G : LocalGaloisGroup.{u}) : Type u :=
  GroupTheoreticInvariants.torsionFreeQuotient
    (LCFT.AbelianizedAbsoluteGaloisGroup G.presentation)

/-- A local Galois-group isomorphism transports torsion-free abelianizations. -/
noncomputable def torsionFreeAbelianizationEquiv
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H) :
    G.torsionFreeAbelianization ≃* H.torsionFreeAbelianization :=
  GroupTheoreticInvariants.torsionFreeQuotientEquiv (abelianizationEquiv f)

/-- The numerical mod-`n` rank of the torsion-free abelianization. -/
noncomputable def abelianizationModPowerRank (G : LocalGaloisGroup.{u}) (n : ℕ) : ℕ :=
  GroupTheoreticInvariants.modPowerRank G.torsionFreeAbelianization n

/-- The group-theoretic residue-characteristic candidate predicate for a local Galois group. -/
def IsResidueCharacteristicCandidate (G : LocalGaloisGroup.{u}) (p : ℕ) : Prop :=
  p.Prime ∧ 2 ≤ G.abelianizationModPowerRank p

/-- Arbitrary local Galois-group isomorphisms preserve the residue-characteristic candidate
predicate. -/
theorem isResidueCharacteristicCandidate_iff
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H) (p : ℕ) :
    G.IsResidueCharacteristicCandidate p ↔ H.IsResidueCharacteristicCandidate p := by
  unfold IsResidueCharacteristicCandidate abelianizationModPowerRank
  rw [GroupTheoreticInvariants.modPowerRank_congr
    (G.torsionFreeAbelianizationEquiv f) p]

/-- Hoshi's group-theoretic absolute degree evaluated on a local Galois group. -/
noncomputable def groupTheoreticAbsoluteDegree
    (G : LocalGaloisGroup.{u}) (p : ℕ) : ℕ :=
  GroupTheoreticInvariants.absoluteDegree
    (LCFT.AbelianizedAbsoluteGaloisGroup G.presentation) p

/-- Hoshi's group-theoretic residue degree evaluated on a local Galois group. -/
noncomputable def groupTheoreticResidueDegree
    (G : LocalGaloisGroup.{u}) (p : ℕ) : ℕ :=
  GroupTheoreticInvariants.residueDegree
    (LCFT.AbelianizedAbsoluteGaloisGroup G.presentation) p

/-- Hoshi's group-theoretic ramification index evaluated on a local Galois group. -/
noncomputable def groupTheoreticRamificationIndex
    (G : LocalGaloisGroup.{u}) (p : ℕ) : ℕ :=
  GroupTheoreticInvariants.ramificationIndex
    (LCFT.AbelianizedAbsoluteGaloisGroup G.presentation) p

/-- Arbitrary local Galois-group isomorphisms preserve Hoshi's group-theoretic absolute degree. -/
theorem groupTheoreticAbsoluteDegree_eq
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H) (p : ℕ) :
    G.groupTheoreticAbsoluteDegree p = H.groupTheoreticAbsoluteDegree p :=
  GroupTheoreticInvariants.absoluteDegree_congr (G.abelianizationEquiv f) p

/-- Arbitrary local Galois-group isomorphisms preserve Hoshi's group-theoretic residue degree. -/
theorem groupTheoreticResidueDegree_eq
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H) (p : ℕ) :
    G.groupTheoreticResidueDegree p = H.groupTheoreticResidueDegree p :=
  GroupTheoreticInvariants.residueDegree_congr (G.abelianizationEquiv f) p

/-- Arbitrary local Galois-group isomorphisms preserve Hoshi's group-theoretic ramification
index. -/
theorem groupTheoreticRamificationIndex_eq
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H) (p : ℕ) :
    G.groupTheoreticRamificationIndex p = H.groupTheoreticRamificationIndex p :=
  GroupTheoreticInvariants.ramificationIndex_congr (G.abelianizationEquiv f) p

end LocalGaloisGroup
end OTriangle
end Anabelian
