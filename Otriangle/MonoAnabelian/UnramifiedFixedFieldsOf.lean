import Otriangle.MonoAnabelian.UnramifiedFixedFields

/-!
# Unramified fixed fields attached to arbitrary finite residue subfields

The degree-indexed construction in `UnramifiedFixedFields` is convenient for canonical towers.
For the tame-conjugation argument we instead start with a particular residue element. This file
cuts out the unramified local extension attached to any finite Galois intermediate field containing
that element.
-/

noncomputable section

namespace Anabelian.OTriangle.LocalGaloisGroup

open LCFT ValuativeRel

universe u

variable (G : LocalGaloisGroup.{u})

abbrev ResidueFiniteGaloisIntermediateField :=
  FiniteGaloisIntermediateField
    (LCFT.ResidueField G.presentation.spectralPointing)
    (LCFT.AlgebraicClosureResidueField G.presentation.spectralPointing)

/-- The inverse image in the absolute Galois group of the fixing subgroup of a finite residue
subfield. -/
noncomputable def residueUnramifiedOpenSubgroupOf
    (E : G.ResidueFiniteGaloisIntermediateField) :
    OpenSubgroup G.toProfiniteGrp :=
  OpenSubgroup.comap G.presentation.spectralResidueGaloisMap
    G.presentation.spectralResidueGaloisMap_continuous
    ⟨E.toIntermediateField.fixingSubgroup,
      IntermediateField.fixingSubgroup_isOpen _⟩

theorem residueUnramifiedOpenSubgroupOf_normal
    (E : G.ResidueFiniteGaloisIntermediateField) :
    (G.residueUnramifiedOpenSubgroupOf E).toSubgroup.Normal := by
  letI : IsGalois (LCFT.ResidueField G.presentation.spectralPointing)
      E.toIntermediateField := E.isGalois
  change (E.toIntermediateField.fixingSubgroup.comap
    G.presentation.spectralResidueGaloisMap).Normal
  exact (inferInstance : E.toIntermediateField.fixingSubgroup.Normal).comap
    G.presentation.spectralResidueGaloisMap

theorem spectralInertiaSubgroup_le_residueUnramifiedOpenSubgroupOf
    (E : G.ResidueFiniteGaloisIntermediateField) :
    G.spectralInertiaSubgroup ≤
      (G.residueUnramifiedOpenSubgroupOf E).toSubgroup := by
  intro sigma hsigma
  change G.presentation.spectralResidueGaloisMap sigma ∈
    E.toIntermediateField.fixingSubgroup
  change G.presentation.spectralResidueGaloisMap sigma = 1 at hsigma
  rw [hsigma]
  exact Subgroup.one_mem _

theorem residueUnramifiedOf_relativeRamificationIndex_eq_one
    (E : G.ResidueFiniteGaloisIntermediateField) :
    (G.fixedFieldBaseExtension
      (OrderDual.toDual (G.residueUnramifiedOpenSubgroupOf E))).relativeRamificationIndex = 1 := by
  rw [← G.spectralInertiaSubgroup_le_iff_relativeRamificationIndex_eq_one
    (G.residueUnramifiedOpenSubgroupOf E)
    (G.residueUnramifiedOpenSubgroupOf_normal E)]
  exact G.spectralInertiaSubgroup_le_residueUnramifiedOpenSubgroupOf E

theorem residueUnramifiedOf_fixedField_finrank
    (E : G.ResidueFiniteGaloisIntermediateField) :
    Module.finrank G.presentation
      (G.fixedField (OrderDual.toDual (G.residueUnramifiedOpenSubgroupOf E))) =
        Module.finrank (LCFT.ResidueField G.presentation.spectralPointing) E := by
  let U := G.residueUnramifiedOpenSubgroupOf E
  change Module.finrank G.presentation
      (IntermediateField.fixedField U.toSubgroup) = _
  rw [IntermediateField.finrank_eq_fixingSubgroup_index]
  rw [InfiniteGalois.fixingSubgroup_fixedField ⟨U.toSubgroup, U.isClosed⟩]
  change (E.toIntermediateField.fixingSubgroup.comap
    G.presentation.spectralResidueGaloisMap).index = _
  rw [E.toIntermediateField.fixingSubgroup.index_comap_of_surjective
    G.presentation.spectralResidueGaloisMap_surjective]
  rw [← IntermediateField.finrank_eq_fixingSubgroup_index]

/-- The residue degree of the unramified fixed field is the degree of the selected residue
intermediate field. -/
theorem residueUnramifiedOf_residueField_finrank
    (E : G.ResidueFiniteGaloisIntermediateField) :
    let U := G.residueUnramifiedOpenSubgroupOf E
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
      (IsLocalRing.ResidueField 𝒪[L]) =
        Module.finrank (LCFT.ResidueField K.spectralPointing) E := by
  let U := G.residueUnramifiedOpenSubgroupOf E
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
    G.fixedField_isGalois_of_normal U (G.residueUnramifiedOpenSubgroupOf_normal E)
  letI : IsScalarTower K K L := IsScalarTower.of_algebraMap_eq' rfl
  letI : MulSemiringAction (L ≃ₐ[K] L) 𝒪[L] :=
    SpectralLocalField.integerMulSemiringAction K K L
  let I : Subgroup (L ≃ₐ[K] L) :=
    (IsLocalRing.maximalIdeal 𝒪[L]).inertia (L ≃ₐ[K] L)
  have hdegree := G.fixedFieldFiniteInertia_card_mul_residueField_finrank
    U (G.residueUnramifiedOpenSubgroupOf_normal E)
  have hIcard : Nat.card I = 1 := by
    calc
      Nat.card I = (G.fixedFieldBaseExtension V).relativeRamificationIndex :=
        G.fixedFieldFiniteInertia_card U
          (G.residueUnramifiedOpenSubgroupOf_normal E)
      _ = 1 := G.residueUnramifiedOf_relativeRamificationIndex_eq_one E
  dsimp only at hdegree
  rw [hIcard, one_mul] at hdegree
  exact hdegree.trans (G.residueUnramifiedOf_fixedField_finrank E)

set_option maxHeartbeats 800000 in
-- The dependent residue-field tower unfolds three spectral valuation structures.
/-- The residue embedding from the unramified fixed field attached to `E` into the residue
algebraic closure. -/
noncomputable def residueUnramifiedOfResidueEmbedding
    (E : G.ResidueFiniteGaloisIntermediateField) :
    let U := G.residueUnramifiedOpenSubgroupOf E
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
  let U := G.residueUnramifiedOpenSubgroupOf E
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
/-- The residue field of the unramified fixed field attached to `E` is exactly `E` inside the
chosen residue algebraic closure. -/
theorem residueUnramifiedOfResidueEmbedding_fieldRange
    (E : G.ResidueFiniteGaloisIntermediateField) :
    let U := G.residueUnramifiedOpenSubgroupOf E
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
    (G.residueUnramifiedOfResidueEmbedding E).fieldRange = E.toIntermediateField := by
  let U := G.residueUnramifiedOpenSubgroupOf E
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
  let i := G.residueUnramifiedOfResidueEmbedding E
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
  have hi : Module.finrank (IsLocalRing.ResidueField 𝒪[K]) i.fieldRange =
      Module.finrank (LCFT.ResidueField K.spectralPointing) E := by
    rw [← i.equivFieldRange.toLinearEquiv.finrank_eq]
    exact G.residueUnramifiedOf_residueField_finrank E
  rw [hi]
  rfl

end Anabelian.OTriangle.LocalGaloisGroup
