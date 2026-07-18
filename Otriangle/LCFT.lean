import Otriangle.OTriangle
import Mathlib.RingTheory.Norm.Basic

/-!
# Specification of local reciprocity

This file records the characterization of the local reciprocity maps for mixed-characteristic
local fields. It is deliberately an interface/specification: the constructions of inertia,
Frobenius, the map on abelianized absolute Galois groups, and the existence and uniqueness of the
reciprocity family are left as `sorry`.

The three defining properties are:

1. units map isomorphically onto inertia;
2. every uniformizer maps to arithmetic Frobenius modulo inertia;
3. reciprocity is compatible with norms along finite extensions.
-/

noncomputable section

open ValuativeRel

namespace Anabelian
namespace LCFT

open OTriangle

universe u

/-- The absolute Galois group attached to the algebraic closure fixed by `K`. -/
abbrev AbsoluteGaloisGroup (K : PointedMixedCharLocalField.{u}) : Type u :=
  K.algebraicClosure ≃ₐ[K] K.algebraicClosure

/-- The topological abelianization of the absolute Galois group attached to `K`. -/
abbrev AbelianizedAbsoluteGaloisGroup (K : PointedMixedCharLocalField.{u}) : Type u :=
  TopologicalAbelianization (AbsoluteGaloisGroup K)

/-- The residue field of `K`. -/
abbrev ResidueField (K : PointedMixedCharLocalField.{u}) : Type u :=
  𝓀[K]

/-- The residue field of the fixed algebraic closure `K̄`, formed directly from the
`ValuativeRel` carried by `K.algebraicClosure`. -/
abbrev AlgebraicClosureResidueField (K : PointedMixedCharLocalField.{u}) : Type u :=
  𝓀[K.algebraicClosure]

/-- The residue-field extension induced by the valuative extension `K̄/K`. -/
noncomputable instance algebraicClosureResidueFieldAlgebra
    (K : PointedMixedCharLocalField.{u}) :
    Algebra (ResidueField K) (AlgebraicClosureResidueField K) := by
  sorry -- TODO: this should exist in mathlib, I hope...

noncomputable instance algebraicClosureResidueFieldModule
    (K : PointedMixedCharLocalField.{u}) :
    Module (ResidueField K) (AlgebraicClosureResidueField K) :=
  (algebraicClosureResidueFieldAlgebra K).toModule

noncomputable instance algebraicClosureResidueFieldIsTorsionFree
    (K : PointedMixedCharLocalField.{u}) :
    Module.IsTorsionFree (ResidueField K) (AlgebraicClosureResidueField K) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (RingHom.injective (algebraMap (ResidueField K) (AlgebraicClosureResidueField K)))

/-- The residue field of the fixed algebraic closure of `K` is an algebraic closure of the residue
field of `K`. -/
noncomputable instance algebraicClosureResidueFieldIsAlgClosure
    (K : PointedMixedCharLocalField.{u}) :
    IsAlgClosure (ResidueField K) (AlgebraicClosureResidueField K) := by
  sorry -- TODO: this might be easy, given what's already in mathlib!

/-- The absolute Galois group of the residue field, computed using the algebraic closure induced by
`K.algebraicClosure`. -/
abbrev ResidueAbsoluteGaloisGroup (K : PointedMixedCharLocalField.{u}) : Type u :=
  AlgebraicClosureResidueField K ≃ₐ[ResidueField K] AlgebraicClosureResidueField K

/-- The inertia subgroup in the abelianized absolute Galois group. -/
noncomputable def inertiaSubgroup (K : PointedMixedCharLocalField.{u}) :
    Subgroup (AbelianizedAbsoluteGaloisGroup K) := by
  sorry -- TODO: I think we can define this properly.

/-- The canonical identification of the quotient by inertia with the absolute Galois group of the
residue field. -/
noncomputable def unramifiedQuotientEquiv (K : PointedMixedCharLocalField.{u}) :
    (AbelianizedAbsoluteGaloisGroup K ⧸ inertiaSubgroup K) ≃*
      ResidueAbsoluteGaloisGroup K := by
  sorry -- TODO: I think we can define this properly, too!

/-- Arithmetic Frobenius in the absolute Galois group of the finite residue field. -/
noncomputable def residueFrobenius (K : PointedMixedCharLocalField.{u}) :
    ResidueAbsoluteGaloisGroup K := by
  sorry -- TODO: we can define this.

/-- Our Frobenius convention is arithmetic Frobenius: it raises elements to the cardinality of the
residue field. -/
theorem residueFrobenius_apply (K : PointedMixedCharLocalField.{u})
    (x : AlgebraicClosureResidueField K) :
    (show AlgebraicClosureResidueField K ≃ₐ[ResidueField K]
        AlgebraicClosureResidueField K from residueFrobenius K) x =
      x ^ Nat.card (ResidueField K) := by
  sorry -- TODO: we can prove this.

/-- The canonical inclusion `𝒪_Kˣ → Kˣ`. -/
noncomputable def integerUnitsToFieldUnits (K : PointedMixedCharLocalField.{u}) :
    𝒪[K]ˣ →* Kˣ :=
  Units.map (algebraMap 𝒪[K] K)

/-- The subgroup `𝒪_Kˣ ≤ Kˣ`. -/
noncomputable def integerUnitSubgroup (K : PointedMixedCharLocalField.{u}) : Subgroup Kˣ :=
  MonoidHom.range (integerUnitsToFieldUnits K)

/-- A nonzero element of `K` is a uniformizer when its valuation is the distinguished generator of
the discrete value group. -/
def IsUniformizer (K : PointedMixedCharLocalField.{u}) (π : Kˣ) : Prop :=
  valuation K (π : K) = ValuativeRel.uniformizer K

/-- The type of candidate reciprocity homomorphisms for `K`. -/
abbrev ReciprocityHom (K : PointedMixedCharLocalField.{u}) :=
  Kˣ →* AbelianizedAbsoluteGaloisGroup K

/-- The first local-reciprocity condition: the restriction to `𝒪_Kˣ` is an isomorphism onto
inertia. -/
structure MapsUnitsIsomorphically (K : PointedMixedCharLocalField.{u})
    (rec : ReciprocityHom K) where
  /-- The isomorphism induced by reciprocity between units and inertia. -/
  unitsEquiv : 𝒪[K]ˣ ≃* inertiaSubgroup K
  /-- The isomorphism is the restriction of the reciprocity homomorphism. -/
  compatibility :
    (inertiaSubgroup K).subtype.comp unitsEquiv.toMonoidHom =
      rec.comp (integerUnitsToFieldUnits K)

/-- The units condition implies that reciprocity descends to the quotients by units and inertia. -/
theorem integerUnitSubgroup_le_comap_inertia {K : PointedMixedCharLocalField.{u}}
    {rec : ReciprocityHom K} (h : MapsUnitsIsomorphically K rec) :
    integerUnitSubgroup K ≤ Subgroup.comap rec (inertiaSubgroup K) := by
  sorry -- TODO: this is a simple consequence of the units condition, but we need to prove it.

/-- The map `Kˣ / 𝒪_Kˣ → Gal_K^ab / I_K` induced by a candidate reciprocity map satisfying the
units condition. -/
noncomputable def inducedUnramifiedMap {K : PointedMixedCharLocalField.{u}}
    (rec : ReciprocityHom K) (h : MapsUnitsIsomorphically K rec) :
    (Kˣ ⧸ integerUnitSubgroup K) →*
      (AbelianizedAbsoluteGaloisGroup K ⧸ inertiaSubgroup K) :=
  QuotientGroup.map (integerUnitSubgroup K) (inertiaSubgroup K) rec
    (integerUnitSubgroup_le_comap_inertia h)

/-- The second local-reciprocity condition: the class of every uniformizer maps to arithmetic
Frobenius under the canonical identification of the unramified quotient with the residue-field
absolute Galois group. -/
def MapsUniformizersToFrobenius {K : PointedMixedCharLocalField.{u}}
    (rec : ReciprocityHom K) (h : MapsUnitsIsomorphically K rec) : Prop :=
  ∀ (π : Kˣ), IsUniformizer K π →
    unramifiedQuotientEquiv K
        (inducedUnramifiedMap rec h ((QuotientGroup.mk' (integerUnitSubgroup K)) π)) =
      residueFrobenius K

/-- A local reciprocity map for one field, equipped with the units and Frobenius properties that
characterize it. -/
structure LocalReciprocityMap (K : PointedMixedCharLocalField.{u}) where
  /-- The reciprocity homomorphism `Kˣ → Gal_K^ab`. -/
  toMonoidHom : ReciprocityHom K
  /-- Units map isomorphically onto inertia. -/
  mapsUnits : MapsUnitsIsomorphically K toMonoidHom
  /-- Uniformizers map to arithmetic Frobenius modulo inertia. -/
  mapsUniformizers : MapsUniformizersToFrobenius toMonoidHom mapsUnits

namespace LocalReciprocityMap

instance (K : PointedMixedCharLocalField.{u}) :
    CoeFun (LocalReciprocityMap K) (fun _ ↦ Kˣ → AbelianizedAbsoluteGaloisGroup K) where
  coe rec := rec.toMonoidHom

end LocalReciprocityMap

/-- A finite extension between pointed mixed-characteristic local fields. The chosen algebraic
closures are not required to be related: the induced map on abelianized absolute Galois groups is
canonical and is specified separately below. -/
@[pp_with_univ]
structure FiniteExtension (K L : PointedMixedCharLocalField.{u}) where
  [algebra : Algebra K L]
  [finiteDimensional : FiniteDimensional K L]

namespace FiniteExtension

/-- The norm homomorphism `Lˣ → Kˣ` of a finite extension. -/
noncomputable def norm {K L : PointedMixedCharLocalField.{u}} (E : FiniteExtension K L) :
    Lˣ →* Kˣ := by
  letI := E.algebra
  letI := E.finiteDimensional
  exact Units.map (Algebra.norm K)

/-- The canonical map `Gal_L^ab → Gal_K^ab` induced by a finite extension `L/K`. At the level of
absolute Galois groups this depends on a choice of compatible algebraic closures only up to inner
conjugacy, so its abelianization is canonical. -/
noncomputable def abelianizedGaloisMap {K L : PointedMixedCharLocalField.{u}}
    (E : FiniteExtension K L) :
    AbelianizedAbsoluteGaloisGroup L →* AbelianizedAbsoluteGaloisGroup K := by
  sorry -- TODO: we can define this!

end FiniteExtension

/-- A family of local reciprocity maps satisfying the three characterizing properties from local
class field theory. -/
structure LocalReciprocityFamily where
  /-- The local reciprocity map for every pointed mixed-characteristic local field. -/
  map : (K : PointedMixedCharLocalField.{u}) → LocalReciprocityMap K
  /-- The third local-reciprocity condition: for every finite extension `L/K`, reciprocity
  intertwines the norm `Lˣ → Kˣ` with the canonical map `Gal_L^ab → Gal_K^ab`. -/
  norm_naturality : ∀ (K L : PointedMixedCharLocalField.{u}) (E : FiniteExtension K L),
    (map K).toMonoidHom.comp E.norm =
      E.abelianizedGaloisMap.comp (map L).toMonoidHom

/-- Existence of the family of local reciprocity maps. This is the local existence theorem of
local class field theory and is intentionally left outside the present specification. -/
theorem localReciprocityFamily_exists : Nonempty (LocalReciprocityFamily.{u}) := by
  sorry -- Note: Leave this as a sorry!

/-- The family of local reciprocity maps selected by the specification. -/
noncomputable def localReciprocityFamily : LocalReciprocityFamily.{u} :=
  localReciprocityFamily_exists.some

/-- The three properties characterize the whole family of local reciprocity maps. -/
theorem localReciprocityFamily_unique (r s : LocalReciprocityFamily.{u}) : r = s := by
  sorry -- Note: Leave this as a sorry!

end LCFT
end Anabelian
