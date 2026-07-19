import Otriangle.MonoAnabelian.IntegralKummerNaturality
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

/-- Assemble the package from the uniform ramification comparison and integral Kummer
naturality.  All fixed-field, transfer-colimit, coherence, and equivariance data are supplied by
the construction in `Otriangle.MonoAnabelian`; the two hypotheses are precisely the arithmetic
content of Hoshi's Propositions 3.6--3.9 and Sections 6--7. -/
noncomputable def monoAnabelianReconstructionPackageOfComparisons
    (reciprocity : LocalReciprocityFamily.{u})
    (hoshi : OTriangle.LocalGaloisGroup.HoshiRamificationComparisonFamily.{u})
    (kummerNaturality : OTriangle.IntegralKummerNaturality reciprocity hoshi) :
    MonoAnabelianReconstructionPackage.{u} reciprocity where
  integral := OTriangle.integralReconstructionOfHoshiComparison
    reciprocity hoshi kummerNaturality

/-- Hoshi's mono-anabelian reconstruction package constructed from local reciprocity. -/
theorem monoAnabelianReconstructionPackage_of_reciprocity
    (reciprocity : LocalReciprocityFamily.{u}) :
    Nonempty (MonoAnabelianReconstructionPackage.{u} reciprocity) := by
  let hoshi : OTriangle.LocalGaloisGroup.HoshiRamificationComparisonFamily.{u} :=
    OTriangle.LocalGaloisGroup.hoshiRamificationComparisonFamily_of_reciprocity reciprocity
  exact ⟨monoAnabelianReconstructionPackageOfComparisons reciprocity hoshi
    (OTriangle.integralKummerNaturality_of_reciprocity reciprocity hoshi)⟩

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
