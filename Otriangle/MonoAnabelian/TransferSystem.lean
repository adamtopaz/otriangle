import Otriangle.MonoAnabelian.OneField

/-!
# Transfer system for reconstructed integral monoids

This module formalizes the transfer square from Hoshi's Lemma 1.7(iii) and the transition maps in
Definition 4.1.  Valuation compatibility is part of the notion of a finite extension of pointed
local fields, so field inclusion preserves the integral submonoids.
-/

noncomputable section

namespace Anabelian
namespace LCFT

open OTriangle
open ValuativeRel

universe u

namespace FiniteExtension

/-- Inclusion along a finite valued extension preserves nonzero integral elements. -/
noncomputable def baseIntegerMonoidMap {K L : PointedMixedCharLocalField.{u}}
    (E : FiniteExtension K L) : baseIntegerMonoid K →* baseIntegerMonoid L := by
  letI := E.algebra
  letI := E.valuativeExtension
  apply MonoidHom.codRestrict
    (E.fieldUnitsMap.comp (baseIntegerMonoid K).subtype) (baseIntegerMonoid L)
  intro x
  change algebraMap K L (x.1 : K) ∈ (valuation L).integer
  have hx : (x.1 : K) ∈ (valuation K).integer := x.property
  rw [Valuation.mem_integer_iff] at hx ⊢
  exact (Valuation.HasExtension.val_map_le_one_iff
    (valuation K) (valuation L) (x.1 : K)).mpr hx

theorem baseIntegerMonoidMap_injective {K L : PointedMixedCharLocalField.{u}}
    (E : FiniteExtension K L) : Function.Injective E.baseIntegerMonoidMap := by
  letI := E.algebra
  intro x y h
  apply Subtype.ext
  apply Units.ext
  apply (algebraMap K L).injective
  have h' := congrArg (fun z : baseIntegerMonoid L ↦ ((z.1 : Lˣ) : L)) h
  exact h'

theorem fieldUnitsMap_injective {K L : PointedMixedCharLocalField.{u}}
    (E : FiniteExtension K L) : Function.Injective E.fieldUnitsMap := by
  letI := E.algebra
  exact Units.map_injective (algebraMap K L).injective

end FiniteExtension

namespace LocalReciprocityFamily

/-- Transfer restricts to the one-field reconstructed integral monoids. -/
noncomputable def reconstructedBaseIntegerMonoidMap
    (reciprocity : LocalReciprocityFamily.{u})
    {K L : PointedMixedCharLocalField.{u}} (E : FiniteExtension K L) :
    reciprocity.reconstructedBaseIntegerMonoid K →*
      reciprocity.reconstructedBaseIntegerMonoid L := by
  apply MonoidHom.codRestrict
    ((reciprocity.transferMap K L E).comp
      (reciprocity.reconstructedBaseIntegerMonoid K).subtype)
    (reciprocity.reconstructedBaseIntegerMonoid L)
  rintro ⟨y, x, rfl⟩
  refine ⟨E.baseIntegerMonoidMap x, ?_⟩
  change (reciprocity.map L).toMonoidHom (E.fieldUnitsMap x.1) =
    reciprocity.transferMap K L E ((reciprocity.map K).toMonoidHom x.1)
  exact (DFunLike.congr_fun (reciprocity.transfer_naturality K L E) x.1).symm

theorem reconstructedBaseIntegerMonoidMap_injective
    (reciprocity : LocalReciprocityFamily.{u})
    {K L : PointedMixedCharLocalField.{u}} (E : FiniteExtension K L) :
    Function.Injective (reciprocity.reconstructedBaseIntegerMonoidMap E) := by
  intro a b h
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  subst a
  subst b
  have h' := congrArg (fun z : reciprocity.reconstructedBaseIntegerMonoid L ↦ z.1) h
  change reciprocity.transferMap K L E ((reciprocity.map K).toMonoidHom x.1) =
    reciprocity.transferMap K L E ((reciprocity.map K).toMonoidHom y.1) at h'
  have hxnat := DFunLike.congr_fun (reciprocity.transfer_naturality K L E) x.1
  have hynat := DFunLike.congr_fun (reciprocity.transfer_naturality K L E) y.1
  have hrecL : (reciprocity.map L).toMonoidHom (E.fieldUnitsMap x.1) =
      (reciprocity.map L).toMonoidHom (E.fieldUnitsMap y.1) := by
    exact hxnat.symm.trans (h'.trans hynat)
  apply Subtype.ext
  apply congrArg (reciprocity.map K).toMonoidHom
  apply E.fieldUnitsMap_injective
  apply (reciprocity.map L).injective
  exact hrecL

/-- The one-field reciprocity equivalences commute with inclusion and transfer. -/
theorem baseIntegerMonoidEquiv_natural
    (reciprocity : LocalReciprocityFamily.{u})
    {K L : PointedMixedCharLocalField.{u}} (E : FiniteExtension K L) :
    (reciprocity.baseIntegerMonoidEquiv L).toMonoidHom.comp E.baseIntegerMonoidMap =
      (reciprocity.reconstructedBaseIntegerMonoidMap E).comp
        (reciprocity.baseIntegerMonoidEquiv K).toMonoidHom := by
  ext x
  change (reciprocity.map L).toMonoidHom (E.fieldUnitsMap x.1) =
    reciprocity.transferMap K L E ((reciprocity.map K).toMonoidHom x.1)
  exact (DFunLike.congr_fun (reciprocity.transfer_naturality K L E) x.1).symm

end LocalReciprocityFamily
end LCFT
end Anabelian
