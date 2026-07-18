import Otriangle.MonoAnabelian.FixedFields
import Otriangle.MonoAnabelian.SpectralResidue

/-!
# Local-field structures on open-subgroup fixed fields

The fixed field of an open subgroup is finite over the presented local field.  This module equips
it and the common algebraic closure with compatible spectral valuations and proves that the fixed
field is again a nonarchimedean local field with the common closure as an algebraic closure.
-/

noncomputable section

namespace Anabelian
namespace OTriangle
namespace LocalGaloisGroup

open ValuativeRel

universe u

variable (G : LocalGaloisGroup.{u})

/-- The spectral norm on the finite fixed field of an open subgroup. -/
@[implicit_reducible]
noncomputable def fixedFieldNontriviallyNormedField (U : G.OpenSubgroupIndex) :
    NontriviallyNormedField (G.fixedField U) := by
  letI := G.presentation.nontriviallyNormedField
  letI := G.presentation.isUltrametricDist
  letI := G.presentation.completeSpace
  letI : FiniteDimensional G.presentation (G.fixedField U) :=
    G.fixedField_finiteDimensional U
  exact SpectralLocalField.nontriviallyNormedField G.presentation (G.fixedField U)

/-- The spectral norm on a fixed field is nonarchimedean. -/
theorem fixedFieldIsUltrametricDist (U : G.OpenSubgroupIndex) :
    letI := G.fixedFieldNontriviallyNormedField U
    IsUltrametricDist (G.fixedField U) := by
  letI := G.presentation.nontriviallyNormedField
  letI := G.presentation.isUltrametricDist
  letI := G.presentation.completeSpace
  letI := G.fixedFieldNontriviallyNormedField U
  exact SpectralLocalField.isUltrametricDist G.presentation (G.fixedField U)

/-- The valuative relation determined by the spectral norm on a fixed field. -/
@[implicit_reducible]
noncomputable def fixedFieldValuativeRel (U : G.OpenSubgroupIndex) :
    ValuativeRel (G.fixedField U) := by
  letI := G.presentation.nontriviallyNormedField
  letI := G.presentation.isUltrametricDist
  letI := G.presentation.completeSpace
  exact SpectralLocalField.valuativeRel G.presentation (G.fixedField U)

/-- The spectral topology on a fixed field. -/
@[implicit_reducible]
noncomputable def fixedFieldTopologicalSpace (U : G.OpenSubgroupIndex) :
    TopologicalSpace (G.fixedField U) := by
  letI := G.presentation.nontriviallyNormedField
  letI := G.presentation.isUltrametricDist
  letI := G.presentation.completeSpace
  exact SpectralLocalField.topologicalSpace G.presentation (G.fixedField U)

/-- A finite fixed field, with its spectral valuation, is a nonarchimedean local field. -/
theorem fixedFieldIsNonarchimedeanLocalField (U : G.OpenSubgroupIndex) :
    letI := G.fixedFieldNontriviallyNormedField U
    letI := G.fixedFieldIsUltrametricDist U
    letI := G.fixedFieldValuativeRel U
    letI := G.fixedFieldTopologicalSpace U
    IsNonarchimedeanLocalField (G.fixedField U) := by
  letI := G.presentation.nontriviallyNormedField
  letI := G.presentation.isUltrametricDist
  letI := G.presentation.completeSpace
  letI := G.fixedFieldNontriviallyNormedField U
  letI := G.fixedFieldIsUltrametricDist U
  letI : ValuativeRel (G.fixedField U) := G.fixedFieldValuativeRel U
  letI : TopologicalSpace (G.fixedField U) := G.fixedFieldTopologicalSpace U
  letI : FiniteDimensional G.presentation (G.fixedField U) :=
    G.fixedField_finiteDimensional U
  exact SpectralLocalField.isNonarchimedeanLocalField
    G.presentation (G.fixedField U)

/-- The spectral norm on the common algebraic closure, viewed as an algebraic extension of the
presented local field. -/
@[implicit_reducible]
noncomputable def spectralAlgebraicClosureNontriviallyNormedField :
    NontriviallyNormedField G.presentation.algebraicClosure := by
  letI := G.presentation.nontriviallyNormedField
  letI := G.presentation.isUltrametricDist
  letI := G.presentation.completeSpace
  exact SpectralLocalField.nontriviallyNormedField
    G.presentation G.presentation.algebraicClosure

/-- The spectral norm on the common algebraic closure is nonarchimedean. -/
theorem spectralAlgebraicClosureIsUltrametricDist :
    letI := G.spectralAlgebraicClosureNontriviallyNormedField
    IsUltrametricDist G.presentation.algebraicClosure := by
  letI := G.presentation.nontriviallyNormedField
  letI := G.presentation.isUltrametricDist
  letI := G.presentation.completeSpace
  letI := G.spectralAlgebraicClosureNontriviallyNormedField
  exact SpectralLocalField.isUltrametricDist
    G.presentation G.presentation.algebraicClosure

/-- The spectral valuative relation on the common algebraic closure. -/
@[implicit_reducible]
noncomputable def spectralAlgebraicClosureValuativeRel :
    ValuativeRel G.presentation.algebraicClosure := by
  letI := G.presentation.nontriviallyNormedField
  letI := G.presentation.isUltrametricDist
  letI := G.presentation.completeSpace
  exact SpectralLocalField.valuativeRel
    G.presentation G.presentation.algebraicClosure

/-- The spectral valuation on the common algebraic closure extends the spectral valuation on each
finite fixed field. -/
theorem fixedFieldValuativeExtension (U : G.OpenSubgroupIndex) :
    letI := G.fixedFieldNontriviallyNormedField U
    letI := G.fixedFieldIsUltrametricDist U
    letI := G.fixedFieldValuativeRel U
    letI := G.spectralAlgebraicClosureNontriviallyNormedField
    letI := G.spectralAlgebraicClosureIsUltrametricDist
    letI := G.spectralAlgebraicClosureValuativeRel
    ValuativeExtension (G.fixedField U) G.presentation.algebraicClosure := by
  letI := G.presentation.nontriviallyNormedField
  letI := G.presentation.isUltrametricDist
  letI := G.presentation.completeSpace
  letI := G.fixedFieldNontriviallyNormedField U
  letI := G.fixedFieldIsUltrametricDist U
  letI : ValuativeRel (G.fixedField U) := G.fixedFieldValuativeRel U
  letI := G.spectralAlgebraicClosureNontriviallyNormedField
  letI := G.spectralAlgebraicClosureIsUltrametricDist
  letI : ValuativeRel G.presentation.algebraicClosure :=
    G.spectralAlgebraicClosureValuativeRel
  exact SpectralLocalField.valuativeExtension G.presentation
    (E := G.fixedField U) (A := G.presentation.algebraicClosure)

/-- The common algebraic closure is also an algebraic closure of every finite fixed field. -/
theorem fixedFieldIsAlgClosure (U : G.OpenSubgroupIndex) :
    IsAlgClosure (G.fixedField U) G.presentation.algebraicClosure := by
  letI : Algebra.IsAlgebraic (G.fixedField U) G.presentation.algebraicClosure :=
    Algebra.IsAlgebraic.tower_top (K := G.presentation)
      (A := G.presentation.algebraicClosure) (G.fixedField U)
  exact
    { isAlgClosed := IsAlgClosure.isAlgClosed G.presentation
      isAlgebraic := inferInstance }

/-- The spectral valuation on a fixed field extends the original valuation on the presented local
field, not merely the norm-derived copy of that valuation. -/
theorem fixedFieldValuativeExtensionFromPresentation (U : G.OpenSubgroupIndex) :
    letI := G.fixedFieldNontriviallyNormedField U
    letI := G.fixedFieldIsUltrametricDist U
    letI := G.fixedFieldValuativeRel U
    ValuativeExtension G.presentation (G.fixedField U) := by
  letI := G.presentation.nontriviallyNormedField
  letI := G.presentation.isUltrametricDist
  letI := G.presentation.completeSpace
  letI := G.fixedFieldNontriviallyNormedField U
  letI := G.fixedFieldIsUltrametricDist U
  letI : ValuativeRel (G.fixedField U) := G.fixedFieldValuativeRel U
  exact G.presentation.spectralValuativeExtension (G.fixedField U)

/-- A finite fixed field, with the common algebraic closure and the canonical spectral residue
action, is a pointed mixed-characteristic local field. -/
noncomputable def fixedFieldPointed (U : G.OpenSubgroupIndex) :
    PointedMixedCharLocalField.{u} := by
  letI := G.presentation.nontriviallyNormedField
  letI := G.presentation.isUltrametricDist
  letI := G.presentation.completeSpace
  letI := G.fixedFieldNontriviallyNormedField U
  letI := G.fixedFieldIsUltrametricDist U
  letI : ValuativeRel (G.fixedField U) := G.fixedFieldValuativeRel U
  letI : TopologicalSpace (G.fixedField U) := G.fixedFieldTopologicalSpace U
  letI : IsNonarchimedeanLocalField (G.fixedField U) :=
    G.fixedFieldIsNonarchimedeanLocalField U
  letI : ValuativeExtension G.presentation (G.fixedField U) :=
    G.fixedFieldValuativeExtensionFromPresentation U
  letI := G.spectralAlgebraicClosureNontriviallyNormedField
  letI := G.spectralAlgebraicClosureIsUltrametricDist
  letI : ValuativeRel G.presentation.algebraicClosure :=
    G.spectralAlgebraicClosureValuativeRel
  letI : ValuativeExtension (G.fixedField U) G.presentation.algebraicClosure :=
    G.fixedFieldValuativeExtension U
  letI : IsAlgClosure (G.fixedField U) G.presentation.algebraicClosure :=
    G.fixedFieldIsAlgClosure U
  letI : IsGalois (G.fixedField U) G.presentation.algebraicClosure := by
    infer_instance
  letI : Algebra.IsIntegral 𝒪[G.fixedField U] 𝒪[G.presentation.algebraicClosure] :=
    SpectralLocalField.integer_isIntegral G.presentation
      (G.fixedField U) G.presentation.algebraicClosure
  letI : Algebra.IsIntegral 𝓀[G.fixedField U] 𝓀[G.presentation.algebraicClosure] :=
    SpectralLocalField.residueField_isIntegral (R := 𝒪[G.fixedField U])
      (S := 𝒪[G.presentation.algebraicClosure])
  letI : Algebra.IsAlgebraic 𝓀[G.fixedField U] 𝓀[G.presentation.algebraicClosure] :=
    ⟨fun x => IsIntegral.isAlgebraic (Algebra.IsIntegral.isIntegral x)⟩
  letI : CharZero (G.fixedField U) :=
    charZero_of_injective_algebraMap
      (algebraMap G.presentation (G.fixedField U)).injective
  letI : CharP 𝓀[G.fixedField U] G.presentation.residueChar :=
    charP_of_injective_algebraMap
      (algebraMap 𝓀[G.presentation] 𝓀[G.fixedField U]).injective
      G.presentation.residueChar
  refine
    { carrier := G.fixedField U
      residueChar := G.presentation.residueChar
      algebraicClosure := G.presentation.algebraicClosure
      residueGaloisMap := SpectralLocalField.residueGaloisMap G.presentation
        (G.fixedField U) G.presentation.algebraicClosure
      residueGaloisMap_surjective := SpectralLocalField.residueGaloisMap_surjective
        G.presentation (G.fixedField U) G.presentation.algebraicClosure
      residueGaloisMap_continuous := SpectralLocalField.residueGaloisMap_continuous
        G.presentation (G.fixedField U) G.presentation.algebraicClosure
      residueGaloisMap_commutes := fun σ τ =>
        SpectralLocalField.finiteBaseGalois_commutes _ _ σ τ }

end LocalGaloisGroup
end OTriangle
end Anabelian
