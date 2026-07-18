import Otriangle.MonoAnabelian.Transport

/-!
# The integral mono-anabelian reconstruction package
-/

noncomputable section

namespace Anabelian
namespace LCFT

universe u

/-- The algorithm of Summary 4.3 together with the integral Kummer comparison of Definition 7.4. -/
structure MonoAnabelianReconstructionPackage (reciprocity : LocalReciprocityFamily.{u}) where
  integral : IntegralReconstruction.{u} reciprocity

/-- Hoshi's mono-anabelian reconstruction package constructed from local reciprocity. -/
theorem monoAnabelianReconstructionPackage_of_reciprocity
    (reciprocity : LocalReciprocityFamily.{u}) :
    Nonempty (MonoAnabelianReconstructionPackage.{u} reciprocity) := by
  sorry -- The construction is developed in the subsequent reconstruction modules.

/-- Existence of the reconstruction package follows from existence of local reciprocity. -/
theorem monoAnabelianReconstructionPackage_exists
    (h : Nonempty (LocalReciprocityFamily.{u})) :
    Nonempty (Σ reciprocity, MonoAnabelianReconstructionPackage.{u} reciprocity) := by
  rcases h with ⟨reciprocity⟩
  obtain ⟨package⟩ := monoAnabelianReconstructionPackage_of_reciprocity reciprocity
  exact ⟨⟨reciprocity, package⟩⟩

noncomputable def localReciprocityFamily : LocalReciprocityFamily.{u} :=
  localReciprocityFamily_exists.some

noncomputable def monoAnabelianReconstructionPackage :
    MonoAnabelianReconstructionPackage.{u} localReciprocityFamily :=
  (monoAnabelianReconstructionPackage_of_reciprocity localReciprocityFamily).some

noncomputable def integralReconstruction :
    IntegralReconstruction.{u} localReciprocityFamily :=
  monoAnabelianReconstructionPackage.integral

end LCFT
end Anabelian
