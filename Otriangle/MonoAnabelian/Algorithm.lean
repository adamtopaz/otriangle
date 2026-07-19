import Otriangle.MonoAnabelian.ConjugationTransport
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

/-- Transport attached to an inner automorphism is the conjugation automorphism defining the
intrinsic action on the reconstructed direct limit. -/
theorem reconstructedDirectLimitEquivOfHoshiComparison_conjugation
    (G : LocalGaloisGroup.{u})
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (hoshi : HoshiRamificationComparisonFamily.{u})
    (σ : G.toProfiniteGrp) :
    reconstructedDirectLimitEquivOfHoshiComparison (G.conjugationHom σ)
        reciprocity hoshi =
      G.reconstructedDirectLimitConjugationEquiv reciprocity σ := by
  apply MulEquiv.ext
  intro z
  induction z using DirectLimit.induction with
  | _ U x =>
      change (⟦⟨G.conjugationIndex σ U,
          fixedFieldReconstructedNodeEquiv (G.conjugationHom σ) U
            reciprocity hoshi x⟩⟧ : G.reconstructedDirectLimit reciprocity) =
        ⟦⟨G.conjugationIndex σ U,
          G.reconstructedNodeConjugationEquiv reciprocity σ U x⟩⟧
      rw [G.fixedFieldReconstructedNodeEquiv_conjugation reciprocity hoshi σ U]
      rfl

/-- Reconstructed transport is equivariant for the intrinsic Galois actions. -/
theorem reconstructedDirectLimitEquivOfHoshiComparison_action
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H)
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (hoshi : HoshiRamificationComparisonFamily.{u})
    (σ : G.toProfiniteGrp) (z : G.reconstructedDirectLimit reciprocity) :
    reconstructedDirectLimitEquivOfHoshiComparison f reciprocity hoshi
        ((G.reconstructedDirectLimitAction reciprocity).smul σ z) =
      (H.reconstructedDirectLimitAction reciprocity).smul (f.equiv σ)
        (reconstructedDirectLimitEquivOfHoshiComparison f reciprocity hoshi z) := by
  rw [G.reconstructedDirectLimitAction_smul,
    H.reconstructedDirectLimitAction_smul,
    ← G.reconstructedDirectLimitEquivOfHoshiComparison_conjugation
      reciprocity hoshi σ,
    ← H.reconstructedDirectLimitEquivOfHoshiComparison_conjugation
      reciprocity hoshi (f.equiv σ)]
  calc
    _ = reconstructedDirectLimitEquivOfHoshiComparison
        (G.conjugationHom σ ≫ f) reciprocity hoshi z := by
      exact congrArg
        (fun e : G.reconstructedDirectLimit reciprocity ≃*
            H.reconstructedDirectLimit reciprocity ↦ e z)
        (G.reconstructedDirectLimitEquivOfHoshiComparison_comp
          (G.conjugationHom σ) f reciprocity hoshi).symm
    _ = reconstructedDirectLimitEquivOfHoshiComparison
        (f ≫ H.conjugationHom (f.equiv σ)) reciprocity hoshi z := by
      rw [G.conjugationHom_natural f σ]
    _ = _ := by
      exact congrArg
        (fun e : G.reconstructedDirectLimit reciprocity ≃*
            H.reconstructedDirectLimit reciprocity ↦ e z)
        (G.reconstructedDirectLimitEquivOfHoshiComparison_comp f
          (H.conjugationHom (f.equiv σ)) reciprocity hoshi)

end LocalGaloisGroup

/-- The fixed-field transfer construction is a functorial integral mono-anabelian algorithm once
Hoshi's local ramification comparison has been established uniformly. -/
noncomputable def integralMonoAnabelianAlgorithmOfHoshiComparison
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (hoshi : LocalGaloisGroup.HoshiRamificationComparisonFamily.{u}) :
    LCFT.IntegralMonoAnabelianAlgorithm.{u} reciprocity where
  obj G := G.reconstructedIntegralMonoid reciprocity
  reconstructMap f :=
    LocalGaloisGroup.reconstructedDirectLimitEquivOfHoshiComparison
      f reciprocity hoshi
  reconstructMap_action f σ x :=
    LocalGaloisGroup.reconstructedDirectLimitEquivOfHoshiComparison_action
      f reciprocity hoshi σ x
  reconstructMap_id G :=
    G.reconstructedDirectLimitEquivOfHoshiComparison_id reciprocity hoshi
  reconstructMap_comp f g :=
    LocalGaloisGroup.reconstructedDirectLimitEquivOfHoshiComparison_comp
      f g reciprocity hoshi

end OTriangle
end Anabelian
