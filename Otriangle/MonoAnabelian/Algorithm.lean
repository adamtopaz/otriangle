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

/-- Reconstructed direct-limit transport along the identity group morphism is the identity. -/
theorem reconstructedDirectLimitEquivOfHoshiComparison_id
    (G : LocalGaloisGroup.{u})
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (hoshi : HoshiRamificationComparisonFamily.{u}) :
    reconstructedDirectLimitEquivOfHoshiComparison (CategoryStruct.id G)
        reciprocity hoshi =
      MulEquiv.refl (G.reconstructedDirectLimit reciprocity) := by
  apply LCFT.FilteredColimit.mulEquivAlongOrderIso_eq_refl
  · exact G.openSubgroupIndexEquiv_id_apply
  · exact fun U x ↦
      fixedFieldReconstructedNodeEquiv_id_apply_heq G U reciprocity hoshi x

/-- Reconstructed direct-limit transport respects composition of local Galois-group
morphisms. -/
theorem reconstructedDirectLimitEquivOfHoshiComparison_comp
    {G H I : LocalGaloisGroup.{u}} (f : G ⟶ H) (g : H ⟶ I)
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (hoshi : HoshiRamificationComparisonFamily.{u}) :
    reconstructedDirectLimitEquivOfHoshiComparison (f ≫ g) reciprocity hoshi =
      (reconstructedDirectLimitEquivOfHoshiComparison f reciprocity hoshi).trans
        (reconstructedDirectLimitEquivOfHoshiComparison g reciprocity hoshi) := by
  apply MulEquiv.ext
  intro z
  induction z using DirectLimit.induction with
  | _ U x =>
      change (⟦⟨G.openSubgroupIndexEquiv (f ≫ g) U,
          fixedFieldReconstructedNodeEquiv (f ≫ g) U reciprocity hoshi x⟩⟧ :
          I.reconstructedDirectLimit reciprocity) =
        ⟦⟨H.openSubgroupIndexEquiv g (G.openSubgroupIndexEquiv f U),
          fixedFieldReconstructedNodeEquiv g
            (G.openSubgroupIndexEquiv f U) reciprocity hoshi
            (fixedFieldReconstructedNodeEquiv f U reciprocity hoshi x)⟩⟧
      exact congrArg
        (fun y : (Sigma fun V ↦
          (I.fixedFieldFiniteExtensionSystem).reconstructedNode reciprocity V) ↦
            (⟦y⟧ : I.reconstructedDirectLimit reciprocity))
        (Sigma.ext (G.openSubgroupIndexEquiv_comp_apply f g U)
          (fixedFieldReconstructedNodeEquiv_comp_apply_heq
            f g U reciprocity hoshi x))

end LocalGaloisGroup
end OTriangle
end Anabelian
