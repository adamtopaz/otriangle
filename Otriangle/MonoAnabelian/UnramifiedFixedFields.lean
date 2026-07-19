import Otriangle.MonoAnabelian.ResidueFiniteExtensions
import Otriangle.MonoAnabelian.FiniteInertiaRestriction

/-!
# Canonical unramified fixed fields

The inverse image of the fixing subgroup of the degree-`n` residue extension is an open normal
subgroup of the absolute Galois group.  Its fixed field is therefore a finite Galois extension,
and it is unramified because the subgroup contains spectral inertia.
-/

noncomputable section

namespace Anabelian.OTriangle.LocalGaloisGroup

open LCFT ValuativeRel

universe u

/-- The open subgroup cutting out the canonical degree-`n` unramified extension. -/
noncomputable def residueUnramifiedOpenSubgroup
    (G : LocalGaloisGroup.{u}) (n : ℕ) [NeZero n] :
    OpenSubgroup G.toProfiniteGrp :=
  OpenSubgroup.comap G.presentation.spectralResidueGaloisMap
    G.presentation.spectralResidueGaloisMap_continuous
    ⟨(LCFT.residueFiniteGaloisIntermediateField
        G.presentation.spectralPointing n).toIntermediateField.fixingSubgroup,
      IntermediateField.fixingSubgroup_isOpen _⟩

/-- The subgroup defining the canonical unramified extension is normal. -/
theorem residueUnramifiedOpenSubgroup_normal
    (G : LocalGaloisGroup.{u}) (n : ℕ) [NeZero n] :
    (G.residueUnramifiedOpenSubgroup n).toSubgroup.Normal := by
  let E := LCFT.residueFiniteGaloisIntermediateField
    G.presentation.spectralPointing n
  letI : IsGalois (LCFT.ResidueField G.presentation.spectralPointing)
      E.toIntermediateField := E.isGalois
  change (E.toIntermediateField.fixingSubgroup.comap
    G.presentation.spectralResidueGaloisMap).Normal
  exact (inferInstance : E.toIntermediateField.fixingSubgroup.Normal).comap
    G.presentation.spectralResidueGaloisMap

/-- Spectral inertia is contained in every canonical unramified subgroup. -/
theorem spectralInertiaSubgroup_le_residueUnramifiedOpenSubgroup
    (G : LocalGaloisGroup.{u}) (n : ℕ) [NeZero n] :
    G.spectralInertiaSubgroup ≤
      (G.residueUnramifiedOpenSubgroup n).toSubgroup := by
  intro sigma hsigma
  change G.presentation.spectralResidueGaloisMap sigma ∈
    (LCFT.residueFiniteGaloisIntermediateField
      G.presentation.spectralPointing n).toIntermediateField.fixingSubgroup
  change G.presentation.spectralResidueGaloisMap sigma = 1 at hsigma
  rw [hsigma]
  exact Subgroup.one_mem _

/-- The fixed field of the canonical residue subgroup is unramified. -/
theorem residueUnramified_relativeRamificationIndex_eq_one
    (G : LocalGaloisGroup.{u}) (n : ℕ) [NeZero n] :
    (G.fixedFieldBaseExtension
      (OrderDual.toDual (G.residueUnramifiedOpenSubgroup n))).relativeRamificationIndex = 1 := by
  rw [← G.spectralInertiaSubgroup_le_iff_relativeRamificationIndex_eq_one
    (G.residueUnramifiedOpenSubgroup n)
    (G.residueUnramifiedOpenSubgroup_normal n)]
  exact G.spectralInertiaSubgroup_le_residueUnramifiedOpenSubgroup n

/-- The canonical unramified fixed field has the prescribed degree. -/
theorem residueUnramified_fixedField_finrank
    (G : LocalGaloisGroup.{u}) (n : ℕ) [NeZero n] :
    Module.finrank G.presentation
      (G.fixedField (OrderDual.toDual (G.residueUnramifiedOpenSubgroup n))) = n := by
  let E := LCFT.residueFiniteGaloisIntermediateField
    G.presentation.spectralPointing n
  let U := G.residueUnramifiedOpenSubgroup n
  change Module.finrank G.presentation
      (IntermediateField.fixedField U.toSubgroup) = n
  rw [IntermediateField.finrank_eq_fixingSubgroup_index]
  rw [InfiniteGalois.fixingSubgroup_fixedField ⟨U.toSubgroup, U.isClosed⟩]
  change (E.toIntermediateField.fixingSubgroup.comap
    G.presentation.spectralResidueGaloisMap).index = n
  rw [E.toIntermediateField.fixingSubgroup.index_comap_of_surjective
    G.presentation.spectralResidueGaloisMap_surjective]
  rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
  exact LCFT.residueFiniteGaloisIntermediateField_finrank
    G.presentation.spectralPointing n

/-- The residue extension of the canonical unramified fixed field also has degree `n`. -/
theorem residueUnramified_residueField_finrank
    (G : LocalGaloisGroup.{u}) (n : ℕ) [NeZero n] :
    let U := G.residueUnramifiedOpenSubgroup n
    let V : G.OpenSubgroupIndex := OrderDual.toDual U
    let K := G.presentation
    let L := G.fixedField V
    letI := K.nontriviallyNormedField
    letI := K.isUltrametricDist
    letI := K.completeSpace
    letI := G.fixedFieldNontriviallyNormedField V
    letI := G.fixedFieldIsUltrametricDist V
    letI : ValuativeRel L := G.fixedFieldValuativeRel V
    letI : ValuativeExtension K L :=
      G.fixedFieldValuativeExtensionFromPresentation V
    Module.finrank (IsLocalRing.ResidueField 𝒪[K])
      (IsLocalRing.ResidueField 𝒪[L]) = n := by
  let U := G.residueUnramifiedOpenSubgroup n
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
  letI : ValuativeExtension K L :=
    G.fixedFieldValuativeExtensionFromPresentation V
  letI : FiniteDimensional K L := G.fixedField_finiteDimensional V
  letI : Algebra.IsAlgebraic K L := by infer_instance
  letI : IsGalois K L :=
    G.fixedField_isGalois_of_normal U (G.residueUnramifiedOpenSubgroup_normal n)
  letI : IsScalarTower K K L := IsScalarTower.of_algebraMap_eq' rfl
  letI : MulSemiringAction (L ≃ₐ[K] L) 𝒪[L] :=
    SpectralLocalField.integerMulSemiringAction K K L
  let I : Subgroup (L ≃ₐ[K] L) :=
    (IsLocalRing.maximalIdeal 𝒪[L]).inertia (L ≃ₐ[K] L)
  have hdegree := G.fixedFieldFiniteInertia_card_mul_residueField_finrank
    U (G.residueUnramifiedOpenSubgroup_normal n)
  have hIcard : Nat.card I = 1 := by
    calc
      Nat.card I = (G.fixedFieldBaseExtension V).relativeRamificationIndex :=
        G.fixedFieldFiniteInertia_card U
          (G.residueUnramifiedOpenSubgroup_normal n)
      _ = 1 := G.residueUnramified_relativeRamificationIndex_eq_one n
  dsimp only at hdegree
  rw [hIcard, one_mul] at hdegree
  exact hdegree.trans (G.residueUnramified_fixedField_finrank n)

set_option maxHeartbeats 800000 in
-- The dependent residue-field tower unfolds three spectral valuation structures.
/-- The residue embedding from the canonical unramified fixed field into the residue algebraic
closure. -/
noncomputable def residueUnramifiedResidueEmbedding
    (G : LocalGaloisGroup.{u}) (n : ℕ) [NeZero n] :
    let U := G.residueUnramifiedOpenSubgroup n
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
    letI := G.spectralAlgebraicClosureNontriviallyNormedField
    letI := G.spectralAlgebraicClosureIsUltrametricDist
    letI : ValuativeRel A := G.spectralAlgebraicClosureValuativeRel
    letI : ValuativeExtension K L :=
      G.fixedFieldValuativeExtensionFromPresentation V
    letI : ValuativeExtension K A := K.spectralValuativeExtension A
    letI : ValuativeExtension L A := G.fixedFieldValuativeExtension V
    letI : IsScalarTower (IsLocalRing.ResidueField 𝒪[K])
        (IsLocalRing.ResidueField 𝒪[L]) (IsLocalRing.ResidueField 𝒪[A]) :=
      IsScalarTower.of_algebraMap_eq' (by
        apply RingHom.ext
        intro x
        obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
        change IsLocalRing.residue 𝒪[A]
            (algebraMap 𝒪[K] 𝒪[A] a) =
          algebraMap (IsLocalRing.ResidueField 𝒪[L])
            (IsLocalRing.ResidueField 𝒪[A])
              (algebraMap (IsLocalRing.ResidueField 𝒪[K])
                (IsLocalRing.ResidueField 𝒪[L])
                  (IsLocalRing.residue 𝒪[K] a))
        rw [IsLocalRing.ResidueField.algebraMap_residue,
          IsLocalRing.ResidueField.algebraMap_residue]
        rfl)
    IsLocalRing.ResidueField 𝒪[L] →ₐ[IsLocalRing.ResidueField 𝒪[K]]
      IsLocalRing.ResidueField 𝒪[A] := by
  let U := G.residueUnramifiedOpenSubgroup n
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
  letI := G.spectralAlgebraicClosureNontriviallyNormedField
  letI := G.spectralAlgebraicClosureIsUltrametricDist
  letI : ValuativeRel A := G.spectralAlgebraicClosureValuativeRel
  letI : ValuativeExtension K L :=
    G.fixedFieldValuativeExtensionFromPresentation V
  letI : ValuativeExtension K A := K.spectralValuativeExtension A
  letI : ValuativeExtension L A := G.fixedFieldValuativeExtension V
  letI : IsScalarTower (IsLocalRing.ResidueField 𝒪[K])
      (IsLocalRing.ResidueField 𝒪[L]) (IsLocalRing.ResidueField 𝒪[A]) :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
      change IsLocalRing.residue 𝒪[A]
          (algebraMap 𝒪[K] 𝒪[A] a) =
        algebraMap (IsLocalRing.ResidueField 𝒪[L])
          (IsLocalRing.ResidueField 𝒪[A])
            (algebraMap (IsLocalRing.ResidueField 𝒪[K])
              (IsLocalRing.ResidueField 𝒪[L])
                (IsLocalRing.residue 𝒪[K] a))
      rw [IsLocalRing.ResidueField.algebraMap_residue,
        IsLocalRing.ResidueField.algebraMap_residue]
      rfl)
  exact IsScalarTower.toAlgHom _ _ _

set_option maxHeartbeats 1600000 in
-- The field-range proof combines the dependent residue tower with infinite Galois fixed fields.
/-- The residue field of the canonical unramified fixed field is exactly the chosen degree-`n`
intermediate field in the residue algebraic closure. -/
theorem residueUnramifiedResidueEmbedding_fieldRange
    (G : LocalGaloisGroup.{u}) (n : ℕ) [NeZero n] :
    let U := G.residueUnramifiedOpenSubgroup n
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
    letI := G.spectralAlgebraicClosureNontriviallyNormedField
    letI := G.spectralAlgebraicClosureIsUltrametricDist
    letI : ValuativeRel A := G.spectralAlgebraicClosureValuativeRel
    letI : ValuativeExtension K L :=
      G.fixedFieldValuativeExtensionFromPresentation V
    letI : ValuativeExtension K A := K.spectralValuativeExtension A
    letI : ValuativeExtension L A := G.fixedFieldValuativeExtension V
    letI : IsScalarTower (IsLocalRing.ResidueField 𝒪[K])
        (IsLocalRing.ResidueField 𝒪[L]) (IsLocalRing.ResidueField 𝒪[A]) :=
      IsScalarTower.of_algebraMap_eq' (by
        apply RingHom.ext
        intro x
        obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
        change IsLocalRing.residue 𝒪[A]
            (algebraMap 𝒪[K] 𝒪[A] a) =
          algebraMap (IsLocalRing.ResidueField 𝒪[L])
            (IsLocalRing.ResidueField 𝒪[A])
              (algebraMap (IsLocalRing.ResidueField 𝒪[K])
                (IsLocalRing.ResidueField 𝒪[L])
                  (IsLocalRing.residue 𝒪[K] a))
        rw [IsLocalRing.ResidueField.algebraMap_residue,
          IsLocalRing.ResidueField.algebraMap_residue]
        rfl)
    (G.residueUnramifiedResidueEmbedding n).fieldRange =
      (LCFT.residueFiniteGaloisIntermediateField K.spectralPointing n).toIntermediateField := by
  let U := G.residueUnramifiedOpenSubgroup n
  let V : G.OpenSubgroupIndex := OrderDual.toDual U
  let K := G.presentation
  let L := G.fixedField V
  let A := K.algebraicClosure
  let E := LCFT.residueFiniteGaloisIntermediateField K.spectralPointing n
  letI := K.nontriviallyNormedField
  letI := K.isUltrametricDist
  letI := K.completeSpace
  letI := G.fixedFieldNontriviallyNormedField V
  letI := G.fixedFieldIsUltrametricDist V
  letI : ValuativeRel L := G.fixedFieldValuativeRel V
  letI := G.spectralAlgebraicClosureNontriviallyNormedField
  letI := G.spectralAlgebraicClosureIsUltrametricDist
  letI : ValuativeRel A := G.spectralAlgebraicClosureValuativeRel
  letI : ValuativeExtension K L :=
    G.fixedFieldValuativeExtensionFromPresentation V
  letI : ValuativeExtension K A := K.spectralValuativeExtension A
  letI : ValuativeExtension L A := G.fixedFieldValuativeExtension V
  letI : IsScalarTower (IsLocalRing.ResidueField 𝒪[K])
      (IsLocalRing.ResidueField 𝒪[L]) (IsLocalRing.ResidueField 𝒪[A]) :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
      change IsLocalRing.residue 𝒪[A]
          (algebraMap 𝒪[K] 𝒪[A] a) =
        algebraMap (IsLocalRing.ResidueField 𝒪[L])
          (IsLocalRing.ResidueField 𝒪[A])
            (algebraMap (IsLocalRing.ResidueField 𝒪[K])
              (IsLocalRing.ResidueField 𝒪[L])
                (IsLocalRing.residue 𝒪[K] a))
      rw [IsLocalRing.ResidueField.algebraMap_residue,
        IsLocalRing.ResidueField.algebraMap_residue]
      rfl)
  let i := G.residueUnramifiedResidueEmbedding n
  have hle : i.fieldRange ≤ E.toIntermediateField := by
    rintro y ⟨x, rfl⟩
    rw [← InfiniteGalois.fixedField_fixingSubgroup E.toIntermediateField,
      IntermediateField.mem_fixedField_iff]
    intro tau htau
    obtain ⟨sigma, hsigma⟩ := K.spectralResidueGaloisMap_surjective tau
    have hsigmaU : sigma ∈ U.toSubgroup := by
      change K.spectralResidueGaloisMap sigma ∈ E.toIntermediateField.fixingSubgroup
      rw [hsigma]
      exact htau
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    change tau (IsLocalRing.residue 𝒪[A]
        (algebraMap 𝒪[L] 𝒪[A] a)) = _
    rw [← hsigma]
    change IsLocalRing.residue 𝒪[A]
        (K.spectralClosureIntegerAlgEquiv sigma
          (algebraMap 𝒪[L] 𝒪[A] a)) = _
    have hfix : sigma (a : L) = (a : L) :=
      (IntermediateField.mem_fixedField_iff
        (H := U.toSubgroup) ((a : L) : A)).mp (a : L).property sigma hsigmaU
    have hcomm : K.spectralClosureIntegerAlgEquiv sigma
        (algebraMap 𝒪[L] 𝒪[A] a) = algebraMap 𝒪[L] 𝒪[A] a := by
      apply Subtype.ext
      change sigma ((a : L) : A) = ((a : L) : A)
      exact hfix
    rw [hcomm]
    change IsLocalRing.residue 𝒪[A] (algebraMap 𝒪[L] 𝒪[A] a) =
      algebraMap (IsLocalRing.ResidueField 𝒪[L])
        (IsLocalRing.ResidueField 𝒪[A]) (IsLocalRing.residue 𝒪[L] a)
    exact (IsLocalRing.ResidueField.algebraMap_residue a).symm
  apply IntermediateField.eq_of_le_of_finrank_eq hle
  have hi : Module.finrank (IsLocalRing.ResidueField 𝒪[K]) i.fieldRange = n := by
    rw [← i.equivFieldRange.toLinearEquiv.finrank_eq]
    exact G.residueUnramified_residueField_finrank n
  rw [hi]
  exact (LCFT.residueFiniteGaloisIntermediateField_finrank K.spectralPointing n).symm

end Anabelian.OTriangle.LocalGaloisGroup
