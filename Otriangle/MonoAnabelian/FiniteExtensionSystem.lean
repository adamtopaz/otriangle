import Otriangle.MonoAnabelian.DirectLimit

/-!
# Directed systems of finite local-field extensions

This module specializes the abstract filtered-colimit comparison to the systems of finite local
extensions occurring in Hoshi's Definition 4.1.  The system records only the identity and
composition laws for the field inclusions.  The corresponding laws for group-theoretic transfer
are derived from the reciprocity squares and are not additional assumptions on local reciprocity.
-/

noncomputable section

namespace Anabelian
namespace LCFT

open OTriangle

universe u v

/-- A directed diagram of pointed local fields and finite valued inclusions. -/
@[pp_with_univ]
structure FiniteExtensionSystem (ι : Type v) [Preorder ι] where
  /-- The local field at each index. -/
  field : ι → PointedMixedCharLocalField.{u}
  /-- The finite valued extension associated to an inequality of indices. -/
  extension : ∀ i j, i ≤ j → FiniteExtension (field i) (field j)
  /-- The inclusion at a reflexive inequality is the identity on integral elements. -/
  baseIntegerMonoidMap_refl : ∀ i,
    (extension i i le_rfl).baseIntegerMonoidMap = MonoidHom.id (baseIntegerMonoid (field i))
  /-- Field inclusions compose along chains of indices. -/
  baseIntegerMonoidMap_trans : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k),
    (extension j k hjk).baseIntegerMonoidMap.comp
        (extension i j hij).baseIntegerMonoidMap =
      (extension i k (hij.trans hjk)).baseIntegerMonoidMap

namespace FiniteExtensionSystem

variable {ι : Type v} [Preorder ι]

/-- The field-theoretic integral monoid at one node of a finite-extension system. -/
abbrev baseNode (S : FiniteExtensionSystem.{u} ι) (i : ι) : Type u :=
  baseIntegerMonoid (S.field i)

/-- Inclusion of integral monoids is the field-theoretic transition map. -/
noncomputable abbrev baseTransition (S : FiniteExtensionSystem.{u} ι)
    (i j : ι) (h : i ≤ j) : S.baseNode i →* S.baseNode j :=
  (S.extension i j h).baseIntegerMonoidMap

instance baseDirectedSystem (S : FiniteExtensionSystem.{u} ι) :
    DirectedSystem S.baseNode (S.baseTransition · · ·) where
  map_self := by
    intro i x
    rw [show S.baseTransition _ _ le_rfl = MonoidHom.id _ from
      S.baseIntegerMonoidMap_refl _]
    rfl
  map_map := by
    intro k j i hij hjk x
    exact DFunLike.congr_fun (S.baseIntegerMonoidMap_trans _ _ _ hij hjk) x

variable (reciprocity : LocalReciprocityFamily.{u})

/-- The reconstructed integral monoid at one node of a finite-extension system. -/
abbrev reconstructedNode (S : FiniteExtensionSystem.{u} ι) (i : ι) : Type u :=
  reciprocity.reconstructedBaseIntegerMonoid (S.field i)

/-- Transfer restricted to reciprocity images is the reconstructed transition map. -/
noncomputable abbrev reconstructedTransition (S : FiniteExtensionSystem.{u} ι)
    (i j : ι) (h : i ≤ j) :
    S.reconstructedNode reciprocity i →* S.reconstructedNode reciprocity j :=
  reciprocity.reconstructedBaseIntegerMonoidMap (S.extension i j h)

/-- At each node, the reciprocity equivalence intertwines field inclusion and transfer. -/
theorem nodeEquiv_natural (S : FiniteExtensionSystem.{u} ι)
    (i j : ι) (h : i ≤ j) :
    (reciprocity.baseIntegerMonoidEquiv (S.field j)).toMonoidHom.comp
        (S.baseTransition i j h) =
      (S.reconstructedTransition reciprocity i j h).comp
        (reciprocity.baseIntegerMonoidEquiv (S.field i)).toMonoidHom :=
  reciprocity.baseIntegerMonoidEquiv_natural (S.extension i j h)

/-- A reconstructed transition is conjugate to field inclusion by the node equivalences. -/
theorem reconstructedTransition_apply (S : FiniteExtensionSystem.{u} ι)
    (i j : ι) (h : i ≤ j) (x : S.reconstructedNode reciprocity i) :
    S.reconstructedTransition reciprocity i j h x =
      reciprocity.baseIntegerMonoidEquiv (S.field j)
        (S.baseTransition i j h
          ((reciprocity.baseIntegerMonoidEquiv (S.field i)).symm x)) := by
  let eᵢ := reciprocity.baseIntegerMonoidEquiv (S.field i)
  let eⱼ := reciprocity.baseIntegerMonoidEquiv (S.field j)
  have hn := DFunLike.congr_fun (S.nodeEquiv_natural reciprocity i j h) (eᵢ.symm x)
  change eⱼ (S.baseTransition i j h (eᵢ.symm x)) =
    S.reconstructedTransition reciprocity i j h (eᵢ (eᵢ.symm x)) at hn
  rw [eᵢ.apply_symm_apply] at hn
  exact hn.symm

/-- The reconstructed transitions satisfy the directed-system laws because field inclusions do. -/
instance reconstructedDirectedSystem (S : FiniteExtensionSystem.{u} ι) :
    DirectedSystem (S.reconstructedNode reciprocity)
      (S.reconstructedTransition reciprocity · · ·) where
  map_self := by
    intro i x
    rw [S.reconstructedTransition_apply reciprocity]
    rw [show S.baseTransition _ _ le_rfl = MonoidHom.id _ from
      S.baseIntegerMonoidMap_refl _]
    exact (reciprocity.baseIntegerMonoidEquiv (S.field _)).apply_symm_apply x
  map_map := by
    intro k j i hij hjk x
    rw [S.reconstructedTransition_apply reciprocity,
      S.reconstructedTransition_apply reciprocity,
      S.reconstructedTransition_apply reciprocity]
    rw [(reciprocity.baseIntegerMonoidEquiv (S.field _)).symm_apply_apply]
    have htrans := DFunLike.congr_fun
      (S.baseIntegerMonoidMap_trans _ _ _ hij hjk)
      ((reciprocity.baseIntegerMonoidEquiv (S.field _)).symm x)
    exact congrArg (reciprocity.baseIntegerMonoidEquiv (S.field _)) htrans

variable [IsDirectedOrder ι] [Nonempty ι]

/-- Nodewise reciprocity induces the multiplicative comparison of the two direct limits. -/
noncomputable def directLimitEquiv (S : FiniteExtensionSystem.{u} ι) :
    DirectLimit S.baseNode S.baseTransition ≃*
      DirectLimit (S.reconstructedNode reciprocity) (S.reconstructedTransition reciprocity) :=
  FilteredColimit.mulEquiv S.baseTransition (S.reconstructedTransition reciprocity)
    (fun i ↦ reciprocity.baseIntegerMonoidEquiv (S.field i))
    (S.nodeEquiv_natural reciprocity)

@[simp]
theorem directLimitEquiv_mk (S : FiniteExtensionSystem.{u} ι)
    (i : ι) (x : S.baseNode i) :
    S.directLimitEquiv reciprocity (⟦⟨i, x⟩⟧ : DirectLimit S.baseNode S.baseTransition) =
      (⟦⟨i, reciprocity.baseIntegerMonoidEquiv (S.field i) x⟩⟧ :
        DirectLimit (S.reconstructedNode reciprocity) (S.reconstructedTransition reciprocity)) :=
  rfl

end FiniteExtensionSystem
end LCFT
end Anabelian
