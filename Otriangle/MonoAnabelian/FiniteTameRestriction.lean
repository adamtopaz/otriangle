import Otriangle.MonoAnabelian.FiniteTameFixedField
import Otriangle.MonoAnabelian.InertiaComparison

/-!
# Restriction of the tame Frobenius relation

Restriction to a normal finite fixed field turns Hoshi's prime-to-`p` neighborhood condition into
a faithful finite tame character.  A lift of arithmetic Frobenius for the spectral pointing
therefore satisfies the intrinsic Frobenius representative predicate after testing against every
such neighborhood.
-/

noncomputable section

namespace Anabelian.OTriangle.LocalGaloisGroup

open LCFT ValuativeRel
open FiniteTameRamification

universe u

/-- Restriction to a normal finite fixed field, with its domain expressed using the profinite
group carried by a local Galois presentation. -/
noncomputable def fixedFieldRestrictNormalHom
    (G : LocalGaloisGroup.{u}) (U : OpenSubgroup G.toProfiniteGrp)
    (hN : U.toSubgroup.Normal) :
    G.toProfiniteGrp →*
      ((G.fixedField (OrderDual.toDual U)) ≃ₐ[G.presentation]
        (G.fixedField (OrderDual.toDual U))) := by
  let V : G.OpenSubgroupIndex := OrderDual.toDual U
  letI : FiniteDimensional G.presentation (G.fixedField V) :=
    G.fixedField_finiteDimensional V
  letI : Algebra.IsAlgebraic G.presentation (G.fixedField V) := by infer_instance
  letI : IsGalois G.presentation (G.fixedField V) :=
    G.fixedField_isGalois_of_normal U hN
  exact AlgEquiv.restrictNormalHom (G.fixedField V)

@[simp]
theorem fixedFieldRestrictNormalHom_ker
    (G : LocalGaloisGroup.{u}) (U : OpenSubgroup G.toProfiniteGrp)
    (hN : U.toSubgroup.Normal) :
    (G.fixedFieldRestrictNormalHom U hN).ker = U.toSubgroup := by
  let V : G.OpenSubgroupIndex := OrderDual.toDual U
  letI : FiniteDimensional G.presentation (G.fixedField V) :=
    G.fixedField_finiteDimensional V
  letI : Algebra.IsAlgebraic G.presentation (G.fixedField V) := by infer_instance
  letI : IsGalois G.presentation (G.fixedField V) :=
    G.fixedField_isGalois_of_normal U hN
  change (AlgEquiv.restrictNormalHom (G.fixedField V)).ker = U.toSubgroup
  rw [IntermediateField.restrictNormalHom_ker]
  exact InfiniteGalois.fixingSubgroup_fixedField ⟨U.toSubgroup, U.isClosed⟩

theorem restrict_conjugation_eq_pow_of_fixedField_residue_frobenius
    (G : LocalGaloisGroup.{u}) (U : OpenSubgroup G.toProfiniteGrp)
    (hN : U.toSubgroup.Normal)
    (hcop : Nat.Coprime
      (G.fixedFieldBaseExtension (OrderDual.toDual U)).relativeRamificationIndex
      G.presentation.residueChar)
    (sigma : G.toProfiniteGrp) (q : ℕ)
    (hfrob :
      let V : G.OpenSubgroupIndex := OrderDual.toDual U
      let K := G.presentation
      let L := G.fixedField V
      letI := K.nontriviallyNormedField
      letI := K.isUltrametricDist
      letI := K.completeSpace
      letI := G.fixedFieldNontriviallyNormedField V
      letI := G.fixedFieldIsUltrametricDist V
      letI : ValuativeRel L := G.fixedFieldValuativeRel V
      letI : TopologicalSpace L := G.fixedFieldTopologicalSpace V
      letI : IsNonarchimedeanLocalField L := G.fixedFieldIsNonarchimedeanLocalField V
      letI : ValuativeExtension K L := G.fixedFieldValuativeExtensionFromPresentation V
      letI : FiniteDimensional K L := G.fixedField_finiteDimensional V
      letI : Algebra.IsAlgebraic K L := by infer_instance
      letI : IsGalois K L := G.fixedField_isGalois_of_normal U hN
      letI : IsScalarTower K K L := IsScalarTower.of_algebraMap_eq' rfl
      letI : MulSemiringAction (L ≃ₐ[K] L) 𝒪[L] :=
        SpectralLocalField.integerMulSemiringAction K K L
      ∀ z : IsLocalRing.ResidueField 𝒪[L],
        (G.fixedFieldRestrictNormalHom U hN sigma) • z = z ^ q)
    (tau : G.spectralInertiaSubgroup) :
    let V : G.OpenSubgroupIndex := OrderDual.toDual U
    let K := G.presentation
    let L := G.fixedField V
    letI := K.nontriviallyNormedField
    letI := K.isUltrametricDist
    letI := K.completeSpace
    letI := G.fixedFieldNontriviallyNormedField V
    letI := G.fixedFieldIsUltrametricDist V
    letI : ValuativeRel L := G.fixedFieldValuativeRel V
    letI : TopologicalSpace L := G.fixedFieldTopologicalSpace V
    letI : IsNonarchimedeanLocalField L := G.fixedFieldIsNonarchimedeanLocalField V
    letI : ValuativeExtension K L := G.fixedFieldValuativeExtensionFromPresentation V
    letI : FiniteDimensional K L := G.fixedField_finiteDimensional V
    letI : Algebra.IsAlgebraic K L := by infer_instance
    letI : IsGalois K L := G.fixedField_isGalois_of_normal U hN
    letI : IsScalarTower K K L := IsScalarTower.of_algebraMap_eq' rfl
    G.fixedFieldRestrictNormalHom U hN (sigma * tau.1 * sigma⁻¹) =
      (G.fixedFieldRestrictNormalHom U hN tau.1) ^ q := by
  let V : G.OpenSubgroupIndex := OrderDual.toDual U
  let K := G.presentation
  let L := G.fixedField V
  letI := K.nontriviallyNormedField
  letI := K.isUltrametricDist
  letI := K.completeSpace
  letI := G.fixedFieldNontriviallyNormedField V
  letI := G.fixedFieldIsUltrametricDist V
  letI : ValuativeRel L := G.fixedFieldValuativeRel V
  letI : TopologicalSpace L := G.fixedFieldTopologicalSpace V
  letI : IsNonarchimedeanLocalField L := G.fixedFieldIsNonarchimedeanLocalField V
  letI : ValuativeExtension K L := G.fixedFieldValuativeExtensionFromPresentation V
  letI : FiniteDimensional K L := G.fixedField_finiteDimensional V
  letI : Algebra.IsAlgebraic K L := by infer_instance
  letI : IsGalois K L := G.fixedField_isGalois_of_normal U hN
  letI : IsScalarTower K K L := IsScalarTower.of_algebraMap_eq' rfl
  letI : MulSemiringAction (L ≃ₐ[K] L) 𝒪[L] :=
    SpectralLocalField.integerMulSemiringAction K K L
  letI : FaithfulSMul (L ≃ₐ[K] L) 𝒪[L] :=
    SpectralLocalField.integerMulSemiringAction_faithful K K L
  let I_L : Subgroup (L ≃ₐ[K] L) :=
    (IsLocalRing.maximalIdeal 𝒪[L]).inertia (L ≃ₐ[K] L)
  have hmap : G.spectralInertiaSubgroup.map
      (AlgEquiv.restrictNormalHom L) = I_L :=
    G.map_spectralInertiaSubgroup_restrictNormalHom U hN
  have htmem : AlgEquiv.restrictNormalHom L tau.1 ∈ I_L := by
    rw [← hmap]
    exact ⟨tau.1, tau.2, rfl⟩
  let t : inertia 𝒪[L] (L ≃ₐ[K] L) :=
    ⟨AlgEquiv.restrictNormalHom L tau.1, htmem⟩
  have hinj := G.fixedFieldFiniteTameCharacter_injective U hN hcop
  have hrel := conjugate_eq_pow_of_residue_frobenius 𝒪[L] (L ≃ₐ[K] L)
    (AlgEquiv.restrictNormalHom L sigma) q hinj hfrob t
  have hval := congrArg Subtype.val hrel
  change (AlgEquiv.restrictNormalHom L sigma) *
      (AlgEquiv.restrictNormalHom L tau.1) *
        (AlgEquiv.restrictNormalHom L sigma)⁻¹ =
    (AlgEquiv.restrictNormalHom L tau.1) ^ q at hval
  dsimp only
  rw [map_mul, map_mul, map_inv]
  exact hval

/-- A lift of the spectral pointing's arithmetic residue Frobenius acts by the base residue-field
cardinality on every normal finite fixed field's residue field. -/
theorem fixedField_residue_smul_eq_pow_of_spectralResidueFrobenius
    (G : LocalGaloisGroup.{u}) (U : OpenSubgroup G.toProfiniteGrp)
    (hN : U.toSubgroup.Normal) (sigma : G.toProfiniteGrp)
    (hsigma : G.presentation.spectralResidueGaloisMap sigma =
      LCFT.residueFrobenius G.presentation.spectralPointing) :
    let V : G.OpenSubgroupIndex := OrderDual.toDual U
    let K := G.presentation
    let L := G.fixedField V
    letI := K.nontriviallyNormedField
    letI := K.isUltrametricDist
    letI := K.completeSpace
    letI := G.fixedFieldNontriviallyNormedField V
    letI := G.fixedFieldIsUltrametricDist V
    letI : ValuativeRel L := G.fixedFieldValuativeRel V
    letI : TopologicalSpace L := G.fixedFieldTopologicalSpace V
    letI : IsNonarchimedeanLocalField L := G.fixedFieldIsNonarchimedeanLocalField V
    letI : ValuativeExtension K L := G.fixedFieldValuativeExtensionFromPresentation V
    letI : FiniteDimensional K L := G.fixedField_finiteDimensional V
    letI : Algebra.IsAlgebraic K L := by infer_instance
    letI : IsGalois K L := G.fixedField_isGalois_of_normal U hN
    letI : IsScalarTower K K L := IsScalarTower.of_algebraMap_eq' rfl
    letI : MulSemiringAction (L ≃ₐ[K] L) 𝒪[L] :=
      SpectralLocalField.integerMulSemiringAction K K L
    ∀ z : IsLocalRing.ResidueField 𝒪[L],
      (G.fixedFieldRestrictNormalHom U hN sigma) • z =
        z ^ Nat.card (LCFT.ResidueField K) := by
  let V : G.OpenSubgroupIndex := OrderDual.toDual U
  let K := G.presentation
  let L := G.fixedField V
  let A := K.algebraicClosure
  letI := K.nontriviallyNormedField
  letI := K.isUltrametricDist
  letI := K.completeSpace
  letI := G.fixedFieldNontriviallyNormedField V
  letI := G.fixedFieldIsUltrametricDist V
  letI : ValuativeRel L := G.fixedFieldValuativeRel V
  letI : TopologicalSpace L := G.fixedFieldTopologicalSpace V
  letI : IsNonarchimedeanLocalField L := G.fixedFieldIsNonarchimedeanLocalField V
  letI : ValuativeExtension K L := G.fixedFieldValuativeExtensionFromPresentation V
  letI : FiniteDimensional K L := G.fixedField_finiteDimensional V
  letI : Algebra.IsAlgebraic K L := by infer_instance
  letI : IsGalois K L := G.fixedField_isGalois_of_normal U hN
  letI : IsScalarTower K K L := IsScalarTower.of_algebraMap_eq' rfl
  letI : MulSemiringAction (L ≃ₐ[K] L) 𝒪[L] :=
    SpectralLocalField.integerMulSemiringAction K K L
  letI := G.spectralAlgebraicClosureNontriviallyNormedField
  letI := G.spectralAlgebraicClosureIsUltrametricDist
  letI : ValuativeRel A := G.spectralAlgebraicClosureValuativeRel
  letI : ValuativeExtension K A := K.spectralValuativeExtension A
  letI : ValuativeExtension L A := G.fixedFieldValuativeExtension V
  letI : IsAlgClosure L A := G.fixedFieldIsAlgClosure V
  dsimp only
  intro z
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  apply (algebraMap (IsLocalRing.ResidueField 𝒪[L])
    (IsLocalRing.ResidueField 𝒪[A])).injective
  change algebraMap (IsLocalRing.ResidueField 𝒪[L])
      (IsLocalRing.ResidueField 𝒪[A])
        (IsLocalRing.residue 𝒪[L]
          ((G.fixedFieldRestrictNormalHom U hN sigma) • x)) =
    algebraMap (IsLocalRing.ResidueField 𝒪[L])
      (IsLocalRing.ResidueField 𝒪[A])
        ((IsLocalRing.residue 𝒪[L] x) ^ Nat.card (LCFT.ResidueField K))
  rw [IsLocalRing.ResidueField.algebraMap_residue, map_pow,
    IsLocalRing.ResidueField.algebraMap_residue]
  have hcomm : algebraMap 𝒪[L] 𝒪[A]
      ((G.fixedFieldRestrictNormalHom U hN sigma) • x) =
      K.spectralClosureIntegerAlgEquiv sigma (algebraMap 𝒪[L] 𝒪[A] x) := by
    apply Subtype.ext
    exact AlgEquiv.restrictNormal_commutes sigma L (x : L)
  rw [hcomm]
  have hz := DFunLike.congr_fun hsigma
    (IsLocalRing.residue 𝒪[A] (algebraMap 𝒪[L] 𝒪[A] x))
  change IsLocalRing.residue 𝒪[A]
      (K.spectralClosureIntegerAlgEquiv sigma (algebraMap 𝒪[L] 𝒪[A] x)) = _ at hz
  rw [LCFT.residueFrobenius_apply] at hz
  exact hz

/-- Every lift of arithmetic Frobenius for the spectral pointing satisfies Hoshi's intrinsic
conjugation condition. -/
theorem spectralFrobenius_isFrobeniusRepresentative
    (G : LocalGaloisGroup.{u}) (reciprocity : LocalReciprocityFamily.{u})
    (sigma : G.toProfiniteGrp)
    (hsigma : G.presentation.spectralResidueGaloisMap sigma =
      LCFT.residueFrobenius G.presentation.spectralPointing) :
    IntrinsicRamification.IsFrobeniusRepresentative G.toProfiniteGrp
      G.presentation.residueChar
      (G.groupTheoreticResidueDegree G.presentation.residueChar) sigma := by
  let p := G.presentation.residueChar
  let f := G.groupTheoreticResidueDegree p
  intro x hx
  have hxclassical : x ∈ G.classicalInertiaSubgroup := by
    rw [← G.intrinsicInertiaSubgroup_eq_classicalInertiaSubgroup reciprocity]
    exact hx
  have hxspectral : x ∈ G.spectralInertiaSubgroup := by
    rw [← G.classicalInertiaSubgroup_eq_spectral reciprocity]
    exact hxclassical
  let tau : G.spectralInertiaSubgroup := ⟨x, hxspectral⟩
  rw [IntrinsicRamification.mem_wildInertiaSubgroup_iff]
  intro U hU
  obtain ⟨hN, hcop⟩ :=
    (G.isWildInertiaNeighborhood_iff_relativeRamificationIndex_coprime
      reciprocity U).mp hU
  have hfcard := G.fixedField_residue_smul_eq_pow_of_spectralResidueFrobenius
    U hN sigma hsigma
  have hcard : Nat.card (LCFT.ResidueField G.presentation) = p ^ f := by
    calc
      Nat.card (LCFT.ResidueField G.presentation) =
          p ^ LCFT.localResidueDegree G.presentation :=
        LCFT.residueField_card_eq_residueChar_pow_residueDegree G.presentation
      _ = p ^ f := by
        congr 1
        exact (G.groupTheoreticResidueDegree_eq_localResidueDegree
          (reciprocity.map G.presentation)).symm
  have hfrob :
      let V : G.OpenSubgroupIndex := OrderDual.toDual U
      let K := G.presentation
      let L := G.fixedField V
      letI := K.nontriviallyNormedField
      letI := K.isUltrametricDist
      letI := K.completeSpace
      letI := G.fixedFieldNontriviallyNormedField V
      letI := G.fixedFieldIsUltrametricDist V
      letI : ValuativeRel L := G.fixedFieldValuativeRel V
      letI : TopologicalSpace L := G.fixedFieldTopologicalSpace V
      letI : IsNonarchimedeanLocalField L := G.fixedFieldIsNonarchimedeanLocalField V
      letI : ValuativeExtension K L := G.fixedFieldValuativeExtensionFromPresentation V
      letI : FiniteDimensional K L := G.fixedField_finiteDimensional V
      letI : Algebra.IsAlgebraic K L := by infer_instance
      letI : IsGalois K L := G.fixedField_isGalois_of_normal U hN
      letI : IsScalarTower K K L := IsScalarTower.of_algebraMap_eq' rfl
      letI : MulSemiringAction (L ≃ₐ[K] L) 𝒪[L] :=
        SpectralLocalField.integerMulSemiringAction K K L
      ∀ z : IsLocalRing.ResidueField 𝒪[L],
        (G.fixedFieldRestrictNormalHom U hN sigma) • z = z ^ (p ^ f) := by
    simpa only [hcard] using hfcard
  have hrel := G.restrict_conjugation_eq_pow_of_fixedField_residue_frobenius
    U hN hcop sigma (p ^ f) hfrob tau
  change sigma * x * sigma⁻¹ * (x ^ (p ^ f))⁻¹ ∈ U.toSubgroup
  rw [← G.fixedFieldRestrictNormalHom_ker U hN]
  change G.fixedFieldRestrictNormalHom U hN
      (sigma * x * sigma⁻¹ * (x ^ (p ^ f))⁻¹) = 1
  rw [map_mul, hrel, map_inv, map_pow, mul_inv_cancel]

end Anabelian.OTriangle.LocalGaloisGroup
