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

end LocalGaloisGroup
end OTriangle
end Anabelian
