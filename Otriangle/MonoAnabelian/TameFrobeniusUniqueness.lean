import Otriangle.MonoAnabelian.FiniteTameRestriction
import Otriangle.MonoAnabelian.ResidueCharacteristicCandidate
import Otriangle.MonoAnabelian.RamificationComparison
import Otriangle.MonoAnabelian.UnramifiedFixedFieldsOf
import Otriangle.MonoAnabelian.UniformizerKummerRamification

/-!
# Uniqueness of the intrinsic Frobenius class

This file separates the formal uniqueness argument from its remaining arithmetic input.  If the
conjugation action on intrinsic tame inertia detects every non-inertial class, then two elements
which induce the prescribed Frobenius power action differ by inertia.  A reciprocity lift of a
uniformizer supplies a representative which is simultaneously Frobenius for the recorded and
spectral residue pointings.
-/

noncomputable section

namespace Anabelian.OTriangle.LocalGaloisGroup

open LCFT

universe u

/-- Faithfulness of the conjugation action of the classical unramified quotient on the intrinsic
tame quotient, stated without constructing the quotient action explicitly. -/
def TameConjugationFaithful
    (G : LocalGaloisGroup.{u}) (p : ℕ) : Prop :=
  ∀ g : G.toProfiniteGrp,
    (∀ x : G.toProfiniteGrp, x ∈ G.classicalInertiaSubgroup →
      g * x * g⁻¹ * x⁻¹ ∈ G.intrinsicWildInertiaSubgroup p) →
    g ∈ G.classicalInertiaSubgroup

/-- Two representatives which induce the same prescribed power action on tame inertia have a
quotient acting trivially on tame inertia. -/
theorem inverse_mul_tameConjugation_trivial_of_frobeniusRepresentatives
    (G : LocalGaloisGroup.{u}) (reciprocity : LocalReciprocityFamily.{u})
    (g sigma : G.toProfiniteGrp)
    (hg : IntrinsicRamification.IsFrobeniusRepresentative G.toProfiniteGrp
      G.presentation.residueChar
      (G.groupTheoreticResidueDegree G.presentation.residueChar) g)
    (hsigma : IntrinsicRamification.IsFrobeniusRepresentative G.toProfiniteGrp
      G.presentation.residueChar
      (G.groupTheoreticResidueDegree G.presentation.residueChar) sigma) :
    ∀ x : G.toProfiniteGrp, x ∈ G.classicalInertiaSubgroup →
      sigma⁻¹ * g * x * (sigma⁻¹ * g)⁻¹ * x⁻¹ ∈
        G.intrinsicWildInertiaSubgroup G.presentation.residueChar := by
  let p := G.presentation.residueChar
  let f := G.groupTheoreticResidueDegree p
  let P := G.intrinsicWildInertiaSubgroup p
  let qP : G.toProfiniteGrp →* G.toProfiniteGrp ⧸ P := QuotientGroup.mk' P
  let q := p ^ f
  intro x hx
  have hxI : x ∈ G.intrinsicInertiaSubgroup p := by
    rw [G.intrinsicInertiaSubgroup_eq_classicalInertiaSubgroup reciprocity]
    exact hx
  let y := sigma⁻¹ * x * sigma
  have hyI : y ∈ G.intrinsicInertiaSubgroup p := by
    have := (IntrinsicRamification.inertiaSubgroup_normal
      G.toProfiniteGrp p).conj_mem x hxI sigma⁻¹
    simpa only [y, inv_inv] using this
  have hgq : qP (g * x * g⁻¹) = qP (x ^ q) := by
    apply (QuotientGroup.eq_iff_div_mem).mpr
    change g * x * g⁻¹ * (x ^ q)⁻¹ ∈ P
    exact hg x hxI
  have hsigmaq : qP (sigma * y * sigma⁻¹) = qP (y ^ q) := by
    apply (QuotientGroup.eq_iff_div_mem).mpr
    change sigma * y * sigma⁻¹ * (y ^ q)⁻¹ ∈ P
    exact hsigma y hyI
  have hxy : qP x = qP (y ^ q) := by
    calc
      qP x = qP (sigma * y * sigma⁻¹) := by
        congr 1
        simp only [y]
        group
      _ = qP (y ^ q) := hsigmaq
  have hconj : qP (sigma⁻¹ * g * x * (sigma⁻¹ * g)⁻¹) = qP x := by
    calc
      qP (sigma⁻¹ * g * x * (sigma⁻¹ * g)⁻¹) =
          qP sigma⁻¹ * qP (g * x * g⁻¹) * qP sigma := by
        simp only [map_mul, map_inv]
        group
      _ = qP sigma⁻¹ * qP (x ^ q) * qP sigma := by rw [hgq]
      _ = qP (y ^ q) := by
        simp only [map_mul, map_inv, map_pow, y]
        rw [← inv_inv (qP sigma)]
        exact (conj_pow (a := (qP sigma)⁻¹) (b := qP x) (i := q)).symm
      _ = qP x := hxy.symm
  apply (QuotientGroup.eq_iff_div_mem).mp hconj

/-- Faithfulness of tame conjugation turns the existence supplied by a common spectral/classical
Frobenius lift into existence and uniqueness of the intrinsic Frobenius class. -/
theorem hasUniqueIntrinsicFrobeniusClass_of_tameConjugationFaithful
    (G : LocalGaloisGroup.{u}) (reciprocity : LocalReciprocityFamily.{u})
    (hfaith : G.TameConjugationFaithful G.presentation.residueChar) :
    G.HasUniqueIntrinsicFrobeniusClass G.presentation.residueChar := by
  let p := G.presentation.residueChar
  let f := G.groupTheoreticResidueDegree p
  obtain ⟨sigma, _, hspectral⟩ := G.exists_commonFrobeniusLift reciprocity
  have hsigma : IntrinsicRamification.IsFrobeniusRepresentative
      G.toProfiniteGrp p f sigma :=
    G.spectralFrobenius_isFrobeniusRepresentative reciprocity sigma hspectral
  let c : G.intrinsicUnramifiedQuotient p :=
    (QuotientGroup.mk' (G.intrinsicInertiaSubgroup p)) sigma
  refine ⟨c, ⟨sigma, rfl, hsigma⟩, ?_⟩
  intro d hd
  obtain ⟨g, rfl, hg⟩ := hd
  have htrivial :=
    G.inverse_mul_tameConjugation_trivial_of_frobeniusRepresentatives
      reciprocity g sigma hg hsigma
  have hmem : sigma⁻¹ * g ∈ G.classicalInertiaSubgroup :=
    hfaith (sigma⁻¹ * g) htrivial
  apply (QuotientGroup.eq_iff_div_mem).mpr
  change g * sigma⁻¹ ∈ G.intrinsicInertiaSubgroup p
  rw [G.intrinsicInertiaSubgroup_eq_classicalInertiaSubgroup reciprocity]
  have := G.classicalInertiaSubgroupNormal.conj_mem (sigma⁻¹ * g) hmem sigma
  simpa [mul_assoc] using this

/-- Under tame-conjugation faithfulness, the uniquely characterized intrinsic class is the
classical arithmetic Frobenius class. -/
theorem intrinsicFrobeniusClass_classicalImage_of_tameConjugationFaithful
    (G : LocalGaloisGroup.{u}) (reciprocity : LocalReciprocityFamily.{u})
    (hfaith : G.TameConjugationFaithful G.presentation.residueChar) :
    let hI := G.intrinsicInertiaSubgroup_eq_classicalInertiaSubgroup reciprocity
    let hU := G.hasUniqueIntrinsicFrobeniusClass_of_tameConjugationFaithful
      reciprocity hfaith
    G.intrinsicToClassicalInertiaQuotient hI
        (G.intrinsicFrobeniusClass G.presentation.residueChar hU) =
      G.classicalFrobeniusClass := by
  let p := G.presentation.residueChar
  let f := G.groupTheoreticResidueDegree p
  let hI := G.intrinsicInertiaSubgroup_eq_classicalInertiaSubgroup reciprocity
  let hU := G.hasUniqueIntrinsicFrobeniusClass_of_tameConjugationFaithful
    reciprocity hfaith
  obtain ⟨sigma, hclassical, hspectral⟩ := G.exists_commonFrobeniusLift reciprocity
  have hsigma : IntrinsicRamification.IsFrobeniusRepresentative
      G.toProfiniteGrp p f sigma :=
    G.spectralFrobenius_isFrobeniusRepresentative reciprocity sigma hspectral
  have hsigmaClass : IntrinsicRamification.IsFrobeniusClass
      G.toProfiniteGrp p f
        ((QuotientGroup.mk' (G.intrinsicInertiaSubgroup p)) sigma) :=
    ⟨sigma, rfl, hsigma⟩
  have hselected : G.intrinsicFrobeniusClass p hU =
      (QuotientGroup.mk' (G.intrinsicInertiaSubgroup p)) sigma :=
    hU.unique
      (IntrinsicRamification.frobeniusClass_spec G.toProfiniteGrp p f hU)
      hsigmaClass
  dsimp only
  rw [hselected]
  change QuotientGroup.quotientMulEquivOfEq hI
      ((QuotientGroup.mk' (G.intrinsicInertiaSubgroup p)) sigma) = _
  change (QuotientGroup.mk' G.classicalInertiaSubgroup) sigma = _
  apply G.classicalInertiaQuotientEquivResidue.injective
  rw [G.classicalInertiaQuotientEquivResidue_mk,
    G.classicalInertiaQuotientEquivResidue_frobeniusClass]
  exact hclassical

/-- All components of Hoshi's local ramification comparison follow once tame conjugation is
known to be faithful. -/
theorem hoshiRamificationComparison_of_tameConjugationFaithful
    (G : LocalGaloisGroup.{u}) (reciprocity : LocalReciprocityFamily.{u})
    (hfaith : G.TameConjugationFaithful G.presentation.residueChar) :
    G.HoshiRamificationComparison where
  residueCharacteristic_iff :=
    G.isResidueCharacteristicCandidate_iff_reciprocity
      (reciprocity.map G.presentation)
  inertia_eq := G.intrinsicInertiaSubgroup_eq_classicalInertiaSubgroup reciprocity
  frobenius_unique :=
    G.hasUniqueIntrinsicFrobeniusClass_of_tameConjugationFaithful reciprocity hfaith
  frobenius_eq :=
    G.intrinsicFrobeniusClass_classicalImage_of_tameConjugationFaithful
      reciprocity hfaith

end Anabelian.OTriangle.LocalGaloisGroup
