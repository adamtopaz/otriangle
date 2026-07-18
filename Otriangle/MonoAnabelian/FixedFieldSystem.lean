import Otriangle.MonoAnabelian.FixedFieldLocal
import Otriangle.MonoAnabelian.FiniteExtensionSystem
import Otriangle.MonoAnabelian.SpectralIntegers

/-!
# The finite-extension system of fixed fields

Open subgroups, ordered by reverse inclusion, give a directed system of pointed finite extensions.
The transition maps are the literal inclusions of fixed fields, so their identity and composition
laws hold definitionally on nonzero integral elements.
-/

noncomputable section

namespace Anabelian
namespace OTriangle
namespace LocalGaloisGroup

universe u

variable (G : LocalGaloisGroup.{u})

/-- Inclusion of fixed fields as a finite valued extension of their pointed local-field
structures. -/
noncomputable def fixedFieldFiniteExtension
    {U V : G.OpenSubgroupIndex} (h : U ≤ V) :
    LCFT.FiniteExtension (G.fixedFieldPointed U) (G.fixedFieldPointed V) := by
  letI : Algebra (G.fixedField U) (G.fixedField V) :=
    RingHom.toAlgebra (IntermediateField.inclusion (G.fixedField_mono h))
  letI : IsScalarTower G.presentation (G.fixedField U) (G.fixedField V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : FiniteDimensional G.presentation (G.fixedField V) :=
    G.fixedField_finiteDimensional V
  letI : FiniteDimensional (G.fixedField U) (G.fixedField V) :=
    FiniteDimensional.right G.presentation (G.fixedField U) (G.fixedField V)
  letI := G.presentation.nontriviallyNormedField
  letI := G.presentation.isUltrametricDist
  letI := G.presentation.completeSpace
  letI := G.fixedFieldNontriviallyNormedField U
  letI := G.fixedFieldIsUltrametricDist U
  letI : ValuativeRel (G.fixedField U) := G.fixedFieldValuativeRel U
  letI := G.fixedFieldNontriviallyNormedField V
  letI := G.fixedFieldIsUltrametricDist V
  letI : ValuativeRel (G.fixedField V) := G.fixedFieldValuativeRel V
  letI : ValuativeExtension (G.fixedField U) (G.fixedField V) :=
    SpectralLocalField.valuativeExtension G.presentation
      (E := G.fixedField U) (A := G.fixedField V)
  refine
    { algebra := ?_
      finiteDimensional := ?_
      valuativeExtension := ?_ }
  all_goals infer_instance

/-- The pointed fixed fields and their inclusions form the finite-extension system indexed by open
subgroups. -/
noncomputable def fixedFieldFiniteExtensionSystem :
    LCFT.FiniteExtensionSystem.{u} G.OpenSubgroupIndex where
  field := G.fixedFieldPointed
  extension := fun _ _ h => G.fixedFieldFiniteExtension h
  baseIntegerMonoidMap_refl := by
    intro U
    ext x
    rfl
  baseIntegerMonoidMap_trans := by
    intro U V W hUV hVW
    ext x
    rfl

end LocalGaloisGroup
end OTriangle
end Anabelian
