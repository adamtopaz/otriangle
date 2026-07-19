import Otriangle.MonoAnabelian.ClassicalRamification

/-!
# The Hoshi ramification comparison interface

Hoshi's Proposition 3.6 and Lemma 3.7 identify the intrinsic numerical constructions with the
classical ramification objects of a presented local field.  This module isolates that arithmetic
comparison as a structure and proves its formal consequences under arbitrary profinite-group
isomorphisms.  No instance of the comparison is assumed or asserted here.
-/

noncomputable section

open CategoryTheory

namespace Anabelian
namespace OTriangle

universe u

namespace LocalGaloisGroup

/-- Identification of an intrinsic inertia quotient at `p` with the classical quotient, given
equality of the two inertia subgroups. -/
noncomputable def intrinsicToClassicalInertiaQuotientAt
    (G : LocalGaloisGroup.{u}) (p : ℕ)
    (hI : G.intrinsicInertiaSubgroup p =
      G.classicalInertiaSubgroup) :
    G.intrinsicUnramifiedQuotient p ≃*
      G.classicalInertiaQuotient := by
  letI : (G.intrinsicInertiaSubgroup p).Normal :=
    IntrinsicRamification.inertiaSubgroup_normal G.toProfiniteGrp p
  letI : G.classicalInertiaSubgroup.Normal :=
    G.classicalInertiaSubgroupNormal
  exact QuotientGroup.quotientMulEquivOfEq hI

/-- The comparison at the presentation's residue characteristic. -/
noncomputable abbrev intrinsicToClassicalInertiaQuotient
    (G : LocalGaloisGroup.{u})
    (hI : G.intrinsicInertiaSubgroup G.presentation.residueChar =
      G.classicalInertiaSubgroup) :
    G.intrinsicUnramifiedQuotient G.presentation.residueChar ≃*
      G.classicalInertiaQuotient :=
  G.intrinsicToClassicalInertiaQuotientAt G.presentation.residueChar hI

/-- The exact arithmetic content needed from Hoshi's Proposition 3.6, Lemma 3.7, and
Proposition 3.9 for a presented local absolute Galois group. -/
structure HoshiRamificationComparison (G : LocalGaloisGroup.{u}) : Prop where
  /-- The intrinsic candidate predicate singles out the presentation's residue characteristic. -/
  residueCharacteristic_iff : ∀ p : ℕ,
    G.IsResidueCharacteristicCandidate p ↔ p = G.presentation.residueChar
  /-- Intrinsic inertia at that prime is classical inertia. -/
  inertia_eq : G.intrinsicInertiaSubgroup G.presentation.residueChar =
    G.classicalInertiaSubgroup
  /-- The intrinsically characterized Frobenius class exists uniquely. -/
  frobenius_unique : G.HasUniqueIntrinsicFrobeniusClass G.presentation.residueChar
  /-- The unique intrinsic class is the presentation's classical arithmetic Frobenius. -/
  frobenius_eq :
    G.intrinsicToClassicalInertiaQuotient inertia_eq
        (G.intrinsicFrobeniusClass G.presentation.residueChar frobenius_unique) =
      G.classicalFrobeniusClass

/-- A proof of Hoshi's arithmetic comparison uniformly for every presented local Galois group. -/
abbrev HoshiRamificationComparisonFamily : Prop :=
  ∀ G : LocalGaloisGroup.{u}, G.HoshiRamificationComparison

/-- Equality with intrinsic inertia at a common prime makes an arbitrary group isomorphism carry
classical inertia onto classical inertia. -/
theorem map_classicalInertiaSubgroup_of_intrinsic
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H) (p : ℕ)
    (hG : G.intrinsicInertiaSubgroup p = G.classicalInertiaSubgroup)
    (hH : H.intrinsicInertiaSubgroup p = H.classicalInertiaSubgroup) :
    G.classicalInertiaSubgroup.map f.equiv.toMulEquiv.toMonoidHom =
      H.classicalInertiaSubgroup := by
  rw [← hG, G.map_intrinsicInertiaSubgroup f, hH]

/-- The induced equivalence of classical unramified quotients, when both classical inertia
subgroups have been identified intrinsically at the same prime. -/
noncomputable def classicalInertiaQuotientEquivOfIntrinsic
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H) (p : ℕ)
    (hG : G.intrinsicInertiaSubgroup p = G.classicalInertiaSubgroup)
    (hH : H.intrinsicInertiaSubgroup p = H.classicalInertiaSubgroup) :
    G.classicalInertiaQuotient ≃* H.classicalInertiaQuotient :=
  QuotientGroup.congr G.classicalInertiaSubgroup H.classicalInertiaSubgroup
    f.equiv.toMulEquiv (map_classicalInertiaSubgroup_of_intrinsic f p hG hH)

/-- The intrinsic and classical quotient transports commute. -/
theorem classicalInertiaQuotientEquivOfIntrinsic_commutes
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H) (p : ℕ)
    (hG : G.intrinsicInertiaSubgroup p = G.classicalInertiaSubgroup)
    (hH : H.intrinsicInertiaSubgroup p = H.classicalInertiaSubgroup)
    (x : G.intrinsicUnramifiedQuotient p) :
    classicalInertiaQuotientEquivOfIntrinsic f p hG hH
        (G.intrinsicToClassicalInertiaQuotientAt p hG x) =
      H.intrinsicToClassicalInertiaQuotientAt p hH
        (IntrinsicRamification.inertiaQuotientEquiv f.equiv p x) := by
  induction x using Quotient.inductionOn with
  | _ σ => rfl

/-- Once the intrinsic characterizations agree with classical inertia and Frobenius at a common
`p` and `f`, arbitrary group isomorphisms preserve the classical arithmetic Frobenius class. -/
theorem classicalFrobeniusClass_map_of_intrinsic
    {G H : LocalGaloisGroup.{u}} (e : G ⟶ H) (p f : ℕ)
    (hIG : G.intrinsicInertiaSubgroup p = G.classicalInertiaSubgroup)
    (hIH : H.intrinsicInertiaSubgroup p = H.classicalInertiaSubgroup)
    (hUG : IntrinsicRamification.HasUniqueFrobeniusClass G.toProfiniteGrp p f)
    (hUH : IntrinsicRamification.HasUniqueFrobeniusClass H.toProfiniteGrp p f)
    (hFG : G.intrinsicToClassicalInertiaQuotientAt p hIG
        (IntrinsicRamification.frobeniusClass G.toProfiniteGrp p f hUG) =
      G.classicalFrobeniusClass)
    (hFH : H.intrinsicToClassicalInertiaQuotientAt p hIH
        (IntrinsicRamification.frobeniusClass H.toProfiniteGrp p f hUH) =
      H.classicalFrobeniusClass) :
    classicalInertiaQuotientEquivOfIntrinsic e p hIG hIH
        G.classicalFrobeniusClass = H.classicalFrobeniusClass := by
  rw [← hFG, classicalInertiaQuotientEquivOfIntrinsic_commutes,
    IntrinsicRamification.frobeniusClass_map e.equiv p f hUG hUH, hFH]

/-- Changing equal numerical parameters and proof witnesses does not change the classical image
of the selected intrinsic Frobenius class. -/
theorem intrinsicFrobeniusClass_classicalImage_congr
    (G : LocalGaloisGroup.{u}) {p q f d : ℕ} (hp : p = q) (hfd : f = d)
    (hIp : G.intrinsicInertiaSubgroup p = G.classicalInertiaSubgroup)
    (hIq : G.intrinsicInertiaSubgroup q = G.classicalInertiaSubgroup)
    (hUp : IntrinsicRamification.HasUniqueFrobeniusClass G.toProfiniteGrp p f)
    (hUq : IntrinsicRamification.HasUniqueFrobeniusClass G.toProfiniteGrp q d) :
    G.intrinsicToClassicalInertiaQuotientAt p hIp
        (IntrinsicRamification.frobeniusClass G.toProfiniteGrp p f hUp) =
      G.intrinsicToClassicalInertiaQuotientAt q hIq
        (IntrinsicRamification.frobeniusClass G.toProfiniteGrp q d hUq) := by
  subst q
  subst d
  rfl

/-- Once Hoshi's local comparison is available on source and target, an arbitrary group
isomorphism preserves the residue characteristic. -/
theorem residueChar_eq_of_hoshiComparison {G H : LocalGaloisGroup.{u}}
    (f : G ⟶ H) (hG : G.HoshiRamificationComparison)
    (hH : H.HoshiRamificationComparison) :
    G.presentation.residueChar = H.presentation.residueChar := by
  apply (hH.residueCharacteristic_iff G.presentation.residueChar).mp
  apply (G.isResidueCharacteristicCandidate_iff f G.presentation.residueChar).mp
  exact (hG.residueCharacteristic_iff G.presentation.residueChar).mpr rfl

/-- Once Hoshi's local comparison is available, an arbitrary group isomorphism maps classical
inertia exactly onto classical inertia. -/
theorem map_classicalInertiaSubgroup_of_hoshiComparison
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H)
    (hG : G.HoshiRamificationComparison)
    (hH : H.HoshiRamificationComparison) :
    G.classicalInertiaSubgroup.map
        f.equiv.toMulEquiv.toMonoidHom =
      H.classicalInertiaSubgroup := by
  rw [← hG.inertia_eq, G.map_intrinsicInertiaSubgroup f,
    residueChar_eq_of_hoshiComparison f hG hH, hH.inertia_eq]

/-- The quotient equivalence on the classical unramified quotients induced by an arbitrary group
isomorphism, conditional only on the two local arithmetic comparisons. -/
noncomputable def classicalInertiaQuotientEquivOfHoshiComparison
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H)
    (hG : G.HoshiRamificationComparison)
    (hH : H.HoshiRamificationComparison) :
    G.classicalInertiaQuotient ≃* H.classicalInertiaQuotient := by
  letI : G.classicalInertiaSubgroup.Normal := G.classicalInertiaSubgroupNormal
  letI : H.classicalInertiaSubgroup.Normal := H.classicalInertiaSubgroupNormal
  exact QuotientGroup.congr
    G.classicalInertiaSubgroup
    H.classicalInertiaSubgroup
    f.equiv.toMulEquiv
    (map_classicalInertiaSubgroup_of_hoshiComparison f hG hH)

/-- The full Hoshi comparison implies that arbitrary group isomorphisms preserve the classical
arithmetic Frobenius class. -/
theorem classicalFrobeniusClass_map_of_hoshiComparison
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H)
    (hG : G.HoshiRamificationComparison)
    (hH : H.HoshiRamificationComparison) :
    classicalInertiaQuotientEquivOfHoshiComparison f hG hH
        G.classicalFrobeniusClass = H.classicalFrobeniusClass := by
  let p := G.presentation.residueChar
  let d := G.groupTheoreticResidueDegree p
  have hp : p = H.presentation.residueChar :=
    residueChar_eq_of_hoshiComparison f hG hH
  have hd : d = H.groupTheoreticResidueDegree p :=
    G.groupTheoreticResidueDegree_eq f p
  have hIH : H.intrinsicInertiaSubgroup p = H.classicalInertiaSubgroup := by
    simpa only [hp] using hH.inertia_eq
  have hUH : IntrinsicRamification.HasUniqueFrobeniusClass H.toProfiniteGrp p d := by
    rw [hd, hp]
    exact hH.frobenius_unique
  have hdfinal : d =
      H.groupTheoreticResidueDegree H.presentation.residueChar := by
    calc
      d = H.groupTheoreticResidueDegree p := hd
      _ = H.groupTheoreticResidueDegree H.presentation.residueChar :=
        congrArg (H.groupTheoreticResidueDegree ·) hp
  have hFH : H.intrinsicToClassicalInertiaQuotientAt p hIH
        (IntrinsicRamification.frobeniusClass H.toProfiniteGrp p d hUH) =
      H.classicalFrobeniusClass := by
    calc
      _ = H.intrinsicToClassicalInertiaQuotient hH.inertia_eq
          (H.intrinsicFrobeniusClass H.presentation.residueChar
            hH.frobenius_unique) :=
        intrinsicFrobeniusClass_classicalImage_congr H hp hdfinal
          hIH hH.inertia_eq hUH hH.frobenius_unique
      _ = H.classicalFrobeniusClass := hH.frobenius_eq
  have htransport := classicalFrobeniusClass_map_of_intrinsic f p d
    hG.inertia_eq hIH hG.frobenius_unique hUH hG.frobenius_eq hFH
  simpa only [classicalInertiaQuotientEquivOfHoshiComparison,
    classicalInertiaQuotientEquivOfIntrinsic] using htransport

@[simp]
theorem abelianizationEquiv_toAbelianization
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H) (σ : G.toProfiniteGrp) :
    G.abelianizationEquiv f (G.toAbelianization σ) =
      H.toAbelianization (f.equiv σ) :=
  rfl

/-- Under Hoshi's comparison, abelianized inertia is intrinsic under arbitrary group
isomorphisms. -/
theorem map_abelianizedInertiaSubgroup_of_hoshiComparison
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H)
    (hG : G.HoshiRamificationComparison)
    (hH : H.HoshiRamificationComparison) :
    (LCFT.inertiaSubgroup G.presentation).map (G.abelianizationEquiv f) =
      LCFT.inertiaSubgroup H.presentation := by
  ext y
  change y ∈ (LCFT.inertiaSubgroup G.presentation).map
      (G.abelianizationEquiv f).toMonoidHom ↔
    y ∈ LCFT.inertiaSubgroup H.presentation
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hy
    have hy' : (G.abelianizationEquiv f).symm y ∈
        G.classicalInertiaSubgroup.map G.toAbelianization := by
      rwa [G.map_classicalInertiaSubgroup_toAbelianization]
    obtain ⟨σ, hσ, hσy⟩ := hy'
    have hfσ : f.equiv σ ∈ H.classicalInertiaSubgroup := by
      have := Subgroup.mem_map_of_mem f.equiv.toMulEquiv.toMonoidHom hσ
      rwa [map_classicalInertiaSubgroup_of_hoshiComparison f hG hH] at this
    rw [← H.map_classicalInertiaSubgroup_toAbelianization]
    refine ⟨f.equiv σ, hfσ, ?_⟩
    calc
      H.toAbelianization (f.equiv σ) =
          G.abelianizationEquiv f (G.toAbelianization σ) := rfl
      _ = G.abelianizationEquiv f ((G.abelianizationEquiv f).symm y) :=
        congrArg (G.abelianizationEquiv f) hσy
      _ = y := (G.abelianizationEquiv f).apply_symm_apply y
  · intro hy
    have hy' : y ∈ H.classicalInertiaSubgroup.map H.toAbelianization := by
      rwa [H.map_classicalInertiaSubgroup_toAbelianization]
    obtain ⟨τ, hτ, hτy⟩ := hy'
    let finv : H ⟶ G := ⟨f.equiv.symm⟩
    have hfτ : f.equiv.symm τ ∈ G.classicalInertiaSubgroup := by
      have := Subgroup.mem_map_of_mem finv.equiv.toMulEquiv.toMonoidHom hτ
      rwa [map_classicalInertiaSubgroup_of_hoshiComparison finv hH hG] at this
    rw [← G.map_classicalInertiaSubgroup_toAbelianization]
    refine ⟨f.equiv.symm τ, hfτ, ?_⟩
    calc
      G.toAbelianization (f.equiv.symm τ) =
          (G.abelianizationEquiv f).symm (H.toAbelianization τ) := rfl
      _ = (G.abelianizationEquiv f).symm y :=
        congrArg (G.abelianizationEquiv f).symm hτy

/-- The induced equivalence on the abelianized unramified quotients. -/
noncomputable def abelianizedInertiaQuotientEquivOfHoshiComparison
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H)
    (hG : G.HoshiRamificationComparison)
    (hH : H.HoshiRamificationComparison) :
    (LCFT.AbelianizedAbsoluteGaloisGroup G.presentation ⧸
        LCFT.inertiaSubgroup G.presentation) ≃*
      (LCFT.AbelianizedAbsoluteGaloisGroup H.presentation ⧸
        LCFT.inertiaSubgroup H.presentation) :=
  QuotientGroup.congr (LCFT.inertiaSubgroup G.presentation)
    (LCFT.inertiaSubgroup H.presentation) (G.abelianizationEquiv f)
    (map_abelianizedInertiaSubgroup_of_hoshiComparison f hG hH)

/-- Full and abelianized unramified quotient transport commute. -/
theorem abelianizedInertiaQuotientEquiv_commutes
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H)
    (hG : G.HoshiRamificationComparison)
    (hH : H.HoshiRamificationComparison)
    (x : G.classicalInertiaQuotient) :
    abelianizedInertiaQuotientEquivOfHoshiComparison f hG hH
        (G.classicalInertiaQuotientToAbelianized x) =
      H.classicalInertiaQuotientToAbelianized
        (classicalInertiaQuotientEquivOfHoshiComparison f hG hH x) := by
  induction x using Quotient.inductionOn with
  | _ σ => rfl

/-- The induced abelianized quotient equivalence preserves the image of arithmetic Frobenius. -/
theorem abelianizedFrobeniusClass_map_of_hoshiComparison
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H)
    (hG : G.HoshiRamificationComparison)
    (hH : H.HoshiRamificationComparison) :
    abelianizedInertiaQuotientEquivOfHoshiComparison f hG hH
        (G.classicalInertiaQuotientToAbelianized G.classicalFrobeniusClass) =
      H.classicalInertiaQuotientToAbelianized H.classicalFrobeniusClass := by
  rw [abelianizedInertiaQuotientEquiv_commutes,
    classicalFrobeniusClass_map_of_hoshiComparison]

/-- The image of classical arithmetic Frobenius in the abelianized unramified quotient. -/
noncomputable def abelianizedFrobeniusClass (G : LocalGaloisGroup.{u}) :
    LCFT.AbelianizedAbsoluteGaloisGroup G.presentation ⧸
      LCFT.inertiaSubgroup G.presentation :=
  G.classicalInertiaQuotientToAbelianized G.classicalFrobeniusClass

@[simp]
theorem unramifiedQuotientEquiv_abelianizedFrobeniusClass
    (G : LocalGaloisGroup.{u}) :
    LCFT.unramifiedQuotientEquiv G.presentation G.abelianizedFrobeniusClass =
      LCFT.residueFrobenius G.presentation :=
  G.unramifiedQuotientEquiv_classicalFrobeniusClass

/-- Membership in the one-field Frobenius-positive monoid can be stated entirely in the
abelianized unramified quotient. -/
theorem mem_intrinsicBaseIntegerMonoid_iff
    (G : LocalGaloisGroup.{u})
    (x : LCFT.AbelianizedAbsoluteGaloisGroup G.presentation) :
    x ∈ LCFT.intrinsicBaseIntegerMonoid G.presentation ↔
      ∃ n : ℕ,
        (QuotientGroup.mk' (LCFT.inertiaSubgroup G.presentation)) x =
          G.abelianizedFrobeniusClass ^ n := by
  rw [LCFT.intrinsicBaseIntegerMonoid, Submonoid.mem_comap,
    Submonoid.mem_powers_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, (LCFT.unramifiedQuotientEquiv G.presentation).injective ?_⟩
    rw [map_pow, G.unramifiedQuotientEquiv_abelianizedFrobeniusClass]
    exact hn.symm
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    calc
      LCFT.residueFrobenius G.presentation ^ n =
          LCFT.unramifiedQuotientEquiv G.presentation
            (G.abelianizedFrobeniusClass ^ n) := by
        rw [map_pow, G.unramifiedQuotientEquiv_abelianizedFrobeniusClass]
      _ = LCFT.unramifiedQuotientEquiv G.presentation
          ((QuotientGroup.mk' (LCFT.inertiaSubgroup G.presentation)) x) := by
        rw [hn]
      _ = LCFT.unramifiedProjection G.presentation x := rfl

@[simp]
theorem abelianizedInertiaQuotientEquiv_mk
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H)
    (hG : G.HoshiRamificationComparison)
    (hH : H.HoshiRamificationComparison)
    (x : LCFT.AbelianizedAbsoluteGaloisGroup G.presentation) :
    abelianizedInertiaQuotientEquivOfHoshiComparison f hG hH
        ((QuotientGroup.mk' (LCFT.inertiaSubgroup G.presentation)) x) =
      (QuotientGroup.mk' (LCFT.inertiaSubgroup H.presentation))
        (G.abelianizationEquiv f x) :=
  QuotientGroup.congr_mk _ _ _ _ x

/-- The one-field Frobenius-positive monoid is carried exactly onto its counterpart by an
arbitrary group isomorphism once Hoshi's local arithmetic comparison is available. -/
theorem map_intrinsicBaseIntegerMonoid_of_hoshiComparison
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H)
    (hG : G.HoshiRamificationComparison)
    (hH : H.HoshiRamificationComparison) :
    (LCFT.intrinsicBaseIntegerMonoid G.presentation).map
        (G.abelianizationEquiv f).toMonoidHom =
      LCFT.intrinsicBaseIntegerMonoid H.presentation := by
  ext y
  rw [Submonoid.mem_map_equiv]
  rw [G.mem_intrinsicBaseIntegerMonoid_iff,
    H.mem_intrinsicBaseIntegerMonoid_iff]
  have hF : abelianizedInertiaQuotientEquivOfHoshiComparison f hG hH
      G.abelianizedFrobeniusClass = H.abelianizedFrobeniusClass :=
    abelianizedFrobeniusClass_map_of_hoshiComparison f hG hH
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    calc
      (QuotientGroup.mk' (LCFT.inertiaSubgroup H.presentation)) y =
          (QuotientGroup.mk' (LCFT.inertiaSubgroup H.presentation))
            (G.abelianizationEquiv f ((G.abelianizationEquiv f).symm y)) :=
        congrArg (QuotientGroup.mk' (LCFT.inertiaSubgroup H.presentation))
          ((G.abelianizationEquiv f).apply_symm_apply y).symm
      _ = abelianizedInertiaQuotientEquivOfHoshiComparison f hG hH
          ((QuotientGroup.mk' (LCFT.inertiaSubgroup G.presentation))
            ((G.abelianizationEquiv f).symm y)) :=
        (abelianizedInertiaQuotientEquiv_mk f hG hH _).symm
      _ = abelianizedInertiaQuotientEquivOfHoshiComparison f hG hH
          (G.abelianizedFrobeniusClass ^ n) :=
        congrArg (abelianizedInertiaQuotientEquivOfHoshiComparison f hG hH) hn
      _ = (abelianizedInertiaQuotientEquivOfHoshiComparison f hG hH
          G.abelianizedFrobeniusClass) ^ n := map_pow _ _ _
      _ = H.abelianizedFrobeniusClass ^ n := congrArg (fun z ↦ z ^ n) hF
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply (abelianizedInertiaQuotientEquivOfHoshiComparison f hG hH).injective
    calc
      abelianizedInertiaQuotientEquivOfHoshiComparison f hG hH
          ((QuotientGroup.mk' (LCFT.inertiaSubgroup G.presentation))
            ((G.abelianizationEquiv f).symm y)) =
          (QuotientGroup.mk' (LCFT.inertiaSubgroup H.presentation)) y := by
        rw [abelianizedInertiaQuotientEquiv_mk,
          (G.abelianizationEquiv f).apply_symm_apply]
      _ = H.abelianizedFrobeniusClass ^ n := hn
      _ = (abelianizedInertiaQuotientEquivOfHoshiComparison f hG hH
          G.abelianizedFrobeniusClass) ^ n := congrArg (fun z ↦ z ^ n) hF.symm
      _ = abelianizedInertiaQuotientEquivOfHoshiComparison f hG hH
          (G.abelianizedFrobeniusClass ^ n) := (map_pow _ _ _).symm

/-- The corresponding multiplicative equivalence between the reconstructed one-field nodes. -/
noncomputable def intrinsicBaseIntegerMonoidEquivOfHoshiComparison
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H)
    (hG : G.HoshiRamificationComparison)
    (hH : H.HoshiRamificationComparison) :
    LCFT.intrinsicBaseIntegerMonoid G.presentation ≃*
      LCFT.intrinsicBaseIntegerMonoid H.presentation :=
  ((G.abelianizationEquiv f).submonoidMap
      (LCFT.intrinsicBaseIntegerMonoid G.presentation)).trans
    (MulEquiv.submonoidCongr
      (map_intrinsicBaseIntegerMonoid_of_hoshiComparison f hG hH))

/-- Nodewise transport of the fixed-field reconstruction diagram, conditional on the uniform
Hoshi arithmetic comparison. -/
noncomputable def fixedFieldReconstructedNodeEquiv
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H) (U : G.OpenSubgroupIndex)
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (hoshi : HoshiRamificationComparisonFamily.{u}) :
    reciprocity.reconstructedBaseIntegerMonoid (G.fixedFieldPointed U) ≃*
      reciprocity.reconstructedBaseIntegerMonoid
        (H.fixedFieldPointed (G.openSubgroupIndexEquiv f U)) :=
  intrinsicBaseIntegerMonoidEquivOfHoshiComparison
    (G.fixedFieldGroupHom f U)
    (hoshi (LocalGaloisGroup.mk (G.fixedFieldPointed U)))
    (hoshi (LocalGaloisGroup.mk
      (H.fixedFieldPointed (G.openSubgroupIndexEquiv f U))))

@[simp]
theorem fixedFieldReconstructedNodeEquiv_apply_coe
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H) (U : G.OpenSubgroupIndex)
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (hoshi : HoshiRamificationComparisonFamily.{u})
    (x : reciprocity.reconstructedBaseIntegerMonoid (G.fixedFieldPointed U)) :
    ((fixedFieldReconstructedNodeEquiv f U reciprocity hoshi x :
      reciprocity.reconstructedBaseIntegerMonoid
        (H.fixedFieldPointed (G.openSubgroupIndexEquiv f U))) :
      LCFT.AbelianizedAbsoluteGaloisGroup
        (H.fixedFieldPointed (G.openSubgroupIndexEquiv f U))) =
      G.fixedFieldAbelianizationEquiv f U x :=
  rfl

/-- Nodewise Hoshi transport along the identity ambient morphism is heterogeneously the
identity.  The heterogeneous statement records that the transported open-subgroup index is only
propositionally, rather than definitionally, equal to the original index. -/
theorem fixedFieldReconstructedNodeEquiv_id_apply_heq
    (G : LocalGaloisGroup.{u}) (U : G.OpenSubgroupIndex)
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (hoshi : HoshiRamificationComparisonFamily.{u})
    (x : reciprocity.reconstructedBaseIntegerMonoid (G.fixedFieldPointed U)) :
    HEq (fixedFieldReconstructedNodeEquiv (CategoryStruct.id G) U
      reciprocity hoshi x) x := by
  apply (Subtype.heq_iff_coe_heq
    (by rw [G.openSubgroupIndexEquiv_id_apply])
    (by rw [G.openSubgroupIndexEquiv_id_apply])).2
  exact G.fixedFieldAbelianizationEquiv_id_apply_heq U x.1

/-- Nodewise Hoshi transport respects composition of ambient group morphisms. -/
theorem fixedFieldReconstructedNodeEquiv_comp_apply_heq
    {G H I : LocalGaloisGroup.{u}} (f : G ⟶ H) (g : H ⟶ I)
    (U : G.OpenSubgroupIndex)
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (hoshi : HoshiRamificationComparisonFamily.{u})
    (x : reciprocity.reconstructedBaseIntegerMonoid (G.fixedFieldPointed U)) :
    HEq (fixedFieldReconstructedNodeEquiv (f ≫ g) U reciprocity hoshi x)
      (fixedFieldReconstructedNodeEquiv g
        (G.openSubgroupIndexEquiv f U) reciprocity hoshi
        (fixedFieldReconstructedNodeEquiv f U reciprocity hoshi x)) := by
  apply (Subtype.heq_iff_coe_heq
    (by rw [G.openSubgroupIndexEquiv_comp_apply f g U])
    (by rw [G.openSubgroupIndexEquiv_comp_apply f g U])).2
  exact G.fixedFieldAbelianizationEquiv_comp_apply_heq f g U x.1

@[simp]
theorem classicalInertiaQuotientEquivOfHoshiComparison_mk
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H)
    (hG : G.HoshiRamificationComparison)
    (hH : H.HoshiRamificationComparison)
    (σ : G.toProfiniteGrp) :
    classicalInertiaQuotientEquivOfHoshiComparison f hG hH
        ((QuotientGroup.mk'
          G.classicalInertiaSubgroup) σ) =
      (QuotientGroup.mk'
        H.classicalInertiaSubgroup) (f.equiv σ) :=
  by
    letI : G.classicalInertiaSubgroup.Normal := G.classicalInertiaSubgroupNormal
    letI : H.classicalInertiaSubgroup.Normal := H.classicalInertiaSubgroupNormal
    exact QuotientGroup.congr_mk _ _ _ _ σ

end LocalGaloisGroup
end OTriangle
end Anabelian
