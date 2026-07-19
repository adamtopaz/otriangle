import Mathlib.CategoryTheory.Equivalence
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Valuation.Extension

/-!
# Core definitions for the O-triangle formalization

This module contains the local-field presentations, Galois-group and Galois-monoid categories,
and their forgetful functors.  It deliberately does not import local class field theory, so that
`Otriangle.LCFT` can build on these definitions without an import cycle.

It is also the shared ancestor of `Otriangle.Comparator.Challenge` and
`Otriangle.Comparator.Solution`, which is why it imports nothing but Mathlib: the statements of the
main theorems are elaborated against these definitions alone, so auditing the challenge means
auditing this one file rather than the whole development.  `Otriangle.OTriangle.Core` re-exports it
for the rest of the project, so the definitions used by the challenge are literally the ones the
development is built on.
-/

noncomputable section

open CategoryTheory
open ValuativeRel

namespace Anabelian
namespace OTriangle

universe u

/-- A `ValuativeExtension` of fields supplies the equivalent `Valuation.HasExtension` interface
used by the valuation-ring and residue-field APIs. -/
noncomputable instance valuativeExtensionHasExtension
    {K L : Type*} [Field K] [Field L] [ValuativeRel K] [ValuativeRel L]
    [Algebra K L] [ValuativeExtension K L] :
    (valuation K).HasExtension (valuation L) := by
  constructor
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  simp only [Valuation.comap_apply]
  rw [← map_one (valuation K), ← map_one (valuation L), ← map_one (algebraMap K L)]
  rw [← Valuation.Compatible.vle_iff_le, ← Valuation.Compatible.vle_iff_le]
  exact (ValuativeExtension.vle_iff_vle (A := K) (B := L) x 1).symm

/-- A pointed mixed-characteristic nonarchimedean local field: a local field together with a
fixed algebraic closure equipped with a valuation extending that of the base field. The mixed
characteristic is recorded as characteristic zero for the field and positive prime characteristic
for its residue field. -/
@[pp_with_univ]
structure PointedMixedCharLocalField where
  /-- The underlying field. -/
  carrier : Type u
  [field : Field carrier]
  [valuativeRel : ValuativeRel carrier]
  [topologicalSpace : TopologicalSpace carrier]
  [isLocalField : IsNonarchimedeanLocalField carrier]
  [charZero : CharZero carrier]
  /-- The residue characteristic. -/
  residueChar : ℕ
  [residueCharPrime : Fact residueChar.Prime]
  [residueFieldCharP : CharP 𝓀[carrier] residueChar]
  /-- The chosen algebraic closure. -/
  algebraicClosure : Type u
  [algebraicClosureField : Field algebraicClosure]
  /-- A valuation on the chosen algebraic closure. -/
  [algebraicClosureValuativeRel : ValuativeRel algebraicClosure]
  [algebra : Algebra carrier algebraicClosure]
  /-- The valuation on the algebraic closure extends the valuation on the base field. -/
  [valuativeExtension : ValuativeExtension carrier algebraicClosure]
  [isAlgClosure : IsAlgClosure carrier algebraicClosure]
  /-- The canonical action of the absolute Galois group on the residue field of the chosen
  algebraic closure.  Recording it with the pointing avoids making every consumer redevelop the
  uniqueness of the extended valuation. -/
  residueGaloisMap :
    (algebraicClosure ≃ₐ[carrier] algebraicClosure) →*
      (𝓀[algebraicClosure] ≃ₐ[𝓀[carrier]] 𝓀[algebraicClosure])
  /-- Every automorphism of the algebraic residue extension lifts to the chosen algebraic
  closure. -/
  residueGaloisMap_surjective : Function.Surjective residueGaloisMap
  /-- The residue action is continuous for the two Krull topologies. -/
  residueGaloisMap_continuous : Continuous residueGaloisMap
  /-- The absolute Galois group of the finite residue field is commutative. -/
  residueGaloisMap_commutes :
    ∀ σ τ : (𝓀[algebraicClosure] ≃ₐ[𝓀[carrier]] 𝓀[algebraicClosure]),
      σ * τ = τ * σ

attribute [instance] PointedMixedCharLocalField.field PointedMixedCharLocalField.valuativeRel
  PointedMixedCharLocalField.topologicalSpace PointedMixedCharLocalField.isLocalField
  PointedMixedCharLocalField.charZero PointedMixedCharLocalField.residueCharPrime
  PointedMixedCharLocalField.residueFieldCharP PointedMixedCharLocalField.algebraicClosureField
  PointedMixedCharLocalField.algebraicClosureValuativeRel PointedMixedCharLocalField.algebra
  PointedMixedCharLocalField.valuativeExtension PointedMixedCharLocalField.isAlgClosure

instance : CoeSort PointedMixedCharLocalField.{u} (Type u) where
  coe K := K.carrier

namespace PointedMixedCharLocalField

/-- The ring of integers of the chosen algebraic closure. It is the integral closure of the
valuation ring `𝒪[K]` in `K.algebraicClosure`. -/
abbrev algebraicClosureIntegers (K : PointedMixedCharLocalField.{u}) : Type u :=
  integralClosure 𝒪[K] K.algebraicClosure

/-- The submonoid `𝒪_{K̄}^▹` of nonzero integers in the chosen algebraic closure. -/
def nonzeroAlgebraicClosureIntegers (K : PointedMixedCharLocalField.{u}) :
    Submonoid K.algebraicClosureIntegers where
  carrier := {x | x ≠ 0}
  one_mem' := one_ne_zero
  mul_mem' hx hy := mul_ne_zero hx hy

/-- The multiplicative monoid `𝒪_{K̄}^▹` of nonzero integers in the chosen algebraic closure. -/
abbrev integerMonoid (K : PointedMixedCharLocalField.{u}) : Type u :=
  K.nonzeroAlgebraicClosureIntegers

/-- The canonical action of `Gal(K̄/K)` on `𝒪_{K̄}^▹`. -/
noncomputable instance integerMonoidMulDistribMulAction (K : PointedMixedCharLocalField.{u}) :
    MulDistribMulAction (K.algebraicClosure ≃ₐ[K] K.algebraicClosure) K.integerMonoid where
  smul σ x :=
    ⟨σ • (x : K.algebraicClosureIntegers), (smul_ne_zero_iff_ne σ).2 x.property⟩
  one_smul x := Subtype.ext (one_smul _ (x : K.algebraicClosureIntegers))
  mul_smul σ τ x := Subtype.ext (mul_smul σ τ (x : K.algebraicClosureIntegers))
  smul_one σ := Subtype.ext (smul_one σ)
  smul_mul σ x y := Subtype.ext (smul_mul' σ
    (x : K.algebraicClosureIntegers) (y : K.algebraicClosureIntegers))

end PointedMixedCharLocalField

/-- An object presented as the absolute Galois group of a mixed-characteristic local field,
with respect to the algebraic closure fixed in the presentation. -/
@[pp_with_univ]
structure LocalGaloisGroup where
  /-- The mixed-characteristic local field and its chosen algebraic closure. -/
  presentation : PointedMixedCharLocalField.{u}

namespace LocalGaloisGroup

/-- The absolute Galois group, equipped with its Krull topology, as a profinite group. -/
noncomputable def toProfiniteGrp (G : LocalGaloisGroup.{u}) : ProfiniteGrp.{u} :=
  InfiniteGalois.profiniteGalGrp G.presentation G.presentation.algebraicClosure

/-- A morphism is an isomorphism of the underlying profinite groups, as in the étale-like
isomorphisms of Hoshi's Theorem 7.6. -/
@[ext]
structure Hom (G H : LocalGaloisGroup.{u}) where
  /-- The underlying continuous group isomorphism. -/
  equiv : G.toProfiniteGrp ≃ₜ* H.toProfiniteGrp

instance : Category LocalGaloisGroup.{u} where
  Hom := Hom
  id G := ⟨ContinuousMulEquiv.refl G.toProfiniteGrp⟩
  comp f g := ⟨f.equiv.trans g.equiv⟩
  id_comp f := by ext x; rfl
  comp_id f := by ext x; rfl
  assoc f g h := by ext x; rfl

/-- Forget the local-field presentation and retain the profinite-group isomorphism. -/
noncomputable def forget : LocalGaloisGroup.{u} ⥤ ProfiniteGrp.{u} where
  obj G := G.toProfiniteGrp
  map f := (ProfiniteGrp.ContinuousMulEquiv.toProfiniteGrpIso f.equiv).hom
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

end LocalGaloisGroup

/-- The absolute Galois group of a pointed mixed-characteristic local field together with the
multiplicative monoid `𝒪_{K̄}^▹` and its canonical Galois action. -/
@[pp_with_univ]
structure LocalGaloisMonoid where
  /-- The pointed mixed-characteristic local field labelling the object. -/
  label : PointedMixedCharLocalField.{u}

namespace LocalGaloisMonoid

/-- Construct the Galois group with its equivariant integral monoid from a pointed local field. -/
def of (K : PointedMixedCharLocalField.{u}) : LocalGaloisMonoid.{u} :=
  ⟨K⟩

/-- The pointed local field presenting the object. -/
abbrev presentation (X : LocalGaloisMonoid.{u}) : PointedMixedCharLocalField.{u} :=
  X.label

/-- Retain only the absolute Galois group attached to the label. -/
def toLocalGaloisGroup (X : LocalGaloisMonoid.{u}) : LocalGaloisGroup.{u} :=
  ⟨X.label⟩

/-- The underlying absolute Galois group as a profinite group. -/
noncomputable abbrev toProfiniteGrp (X : LocalGaloisMonoid.{u}) : ProfiniteGrp.{u} :=
  X.toLocalGaloisGroup.toProfiniteGrp

/-- The monoid `𝒪_{K̄}^▹` carrying the canonical action of the underlying absolute Galois group. -/
abbrev integerMonoid (X : LocalGaloisMonoid.{u}) : Type u :=
  X.presentation.integerMonoid

/-- The canonical action, expressed using the profinite-group realization of the Galois group. -/
noncomputable instance galoisAction (X : LocalGaloisMonoid.{u}) :
    MulDistribMulAction X.toProfiniteGrp X.integerMonoid :=
  PointedMixedCharLocalField.integerMonoidMulDistribMulAction X.presentation

/-- The canonical Galois action as an explicit function. -/
noncomputable def galoisAct (X : LocalGaloisMonoid.{u})
    (σ : X.toProfiniteGrp) (x : X.integerMonoid) : X.integerMonoid :=
  (galoisAction X).smul σ x

/-- A morphism consists of an isomorphism of absolute Galois groups and an equivariant isomorphism
of the monoids `𝒪_{K̄}^▹`.  This is an isomorphism of integral MLF-pairs in Hoshi's sense. -/
@[ext]
structure Hom (X Y : LocalGaloisMonoid.{u}) where
  /-- The isomorphism of the underlying profinite Galois groups. -/
  groupHom : X.toLocalGaloisGroup ⟶ Y.toLocalGaloisGroup
  /-- The isomorphism between the monoids of nonzero algebraic integers. -/
  monoidIso : X.integerMonoid ≃* Y.integerMonoid
  /-- Equivariance of `monoidIso` with respect to `groupHom`. -/
  action_compatible : ∀ (σ : X.toProfiniteGrp) (x : X.integerMonoid),
    monoidIso (X.galoisAct σ x) = Y.galoisAct (groupHom.equiv σ) (monoidIso x)

instance : Category LocalGaloisMonoid.{u} where
  Hom := Hom
  id X :=
    { groupHom := 𝟙 X.toLocalGaloisGroup
      monoidIso := MulEquiv.refl X.integerMonoid
      action_compatible := by
        intro σ x
        rfl }
  comp f g :=
    { groupHom := f.groupHom ≫ g.groupHom
      monoidIso := f.monoidIso.trans g.monoidIso
      action_compatible := by
        intro σ x
        rw [MulEquiv.trans_apply, f.action_compatible, g.action_compatible]
        rfl }
  id_comp f := by ext <;> simp
  comp_id f := by ext <;> simp
  assoc f g h := by ext <;> simp

/-- Forget the equivariant monoid and retain the absolute Galois group isomorphism. -/
noncomputable def forgetGaloisGroup : LocalGaloisMonoid.{u} ⥤ LocalGaloisGroup.{u} where
  obj X := X.toLocalGaloisGroup
  map f := f.groupHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The forgetful functor is surjective on objects: both kinds of objects are labelled by a
pointed mixed-characteristic local field. -/
theorem forgetGaloisGroup_obj_surjective : Function.Surjective forgetGaloisGroup.obj := by
  rintro ⟨K⟩
  exact ⟨of K, rfl⟩

/-- The forgetful functor from local Galois monoids to local Galois groups is essentially
surjective. -/
theorem forgetGaloisGroup_essSurj : forgetGaloisGroup.EssSurj :=
  Functor.essSurj_of_surj forgetGaloisGroup_obj_surjective

noncomputable instance : forgetGaloisGroup.EssSurj :=
  forgetGaloisGroup_essSurj

/-- Forget to the underlying profinite absolute Galois group. -/
noncomputable def forgetProfiniteGrp : LocalGaloisMonoid.{u} ⥤ ProfiniteGrp.{u} :=
  forgetGaloisGroup ⋙ LocalGaloisGroup.forget

end LocalGaloisMonoid
end OTriangle
end Anabelian
