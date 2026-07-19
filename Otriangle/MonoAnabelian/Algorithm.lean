import Otriangle.MonoAnabelian.DiagramTransport
import Otriangle.MonoAnabelian.ReconstructedObject

/-!
# Functorial integral reconstruction

Nodewise Hoshi transport commutes with transfer, and therefore descends to the filtered colimit
over open subgroups.  This module records the induced map and its functorial and equivariance laws.
-/

noncomputable section

open CategoryTheory

namespace Anabelian
namespace OTriangle
namespace LocalGaloisGroup

universe u

/-- The multiplicative equivalence of reconstructed direct limits induced by a continuous group
equivalence, conditional on Hoshi's uniform local ramification comparison. -/
noncomputable def reconstructedDirectLimitEquivOfHoshiComparison
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H)
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (hoshi : HoshiRamificationComparisonFamily.{u}) :
    G.reconstructedDirectLimit reciprocity ≃*
      H.reconstructedDirectLimit reciprocity :=
  LCFT.FilteredColimit.mulEquivAlongOrderIso
    ((G.fixedFieldFiniteExtensionSystem).reconstructedTransition reciprocity)
    ((H.fixedFieldFiniteExtensionSystem).reconstructedTransition reciprocity)
    (G.openSubgroupIndexEquiv f)
    (fun U ↦ fixedFieldReconstructedNodeEquiv f U reciprocity hoshi)
    (fun _ _ h ↦ fixedFieldReconstructedNodeEquiv_natural f h reciprocity hoshi)

@[simp]
theorem reconstructedDirectLimitEquivOfHoshiComparison_mk
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H)
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (hoshi : HoshiRamificationComparisonFamily.{u})
    (U : G.OpenSubgroupIndex)
    (x : (G.fixedFieldFiniteExtensionSystem).reconstructedNode reciprocity U) :
    reconstructedDirectLimitEquivOfHoshiComparison f reciprocity hoshi
        (⟦⟨U, x⟩⟧ : G.reconstructedDirectLimit reciprocity) =
      (⟦⟨G.openSubgroupIndexEquiv f U,
        fixedFieldReconstructedNodeEquiv f U reciprocity hoshi x⟩⟧ :
        H.reconstructedDirectLimit reciprocity) :=
  rfl

end LocalGaloisGroup
end OTriangle
end Anabelian
