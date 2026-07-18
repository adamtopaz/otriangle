import Otriangle.LCFT

/-!
# Interfaces for integral mono-anabelian reconstruction

This module separates the output of Hoshi's group-theoretic algorithm (Summary 4.3) from the
Kummer comparison (Definition 7.4).  No existence assertion is made here.
-/

noncomputable section

open CategoryTheory

namespace Anabelian
namespace LCFT

open OTriangle

universe u

/-- A commutative monoid reconstructed from an absolute Galois group, together with its Galois
action.  This bundles the output denoted `𝒪^▹(G)` in Hoshi's Summary 4.3. -/
@[pp_with_univ]
structure ReconstructedIntegralMonoid (G : LocalGaloisGroup.{u}) where
  /-- The reconstructed multiplicative monoid. -/
  carrier : Type u
  [commMonoid : CommMonoid carrier]
  /-- The Galois action reconstructed with the monoid. -/
  [action : MulDistribMulAction G.toProfiniteGrp carrier]

attribute [instance] ReconstructedIntegralMonoid.commMonoid
  ReconstructedIntegralMonoid.action

instance (G : LocalGaloisGroup.{u}) :
    CoeSort (ReconstructedIntegralMonoid G) (Type u) where
  coe M := M.carrier

/-- The functorial integral mono-anabelian algorithm of Hoshi's Summary 4.3. -/
@[pp_with_univ]
structure IntegralMonoAnabelianAlgorithm (reciprocity : LocalReciprocityFamily.{u}) where
  /-- The reconstructed integral monoid attached to a group. -/
  obj : (G : LocalGaloisGroup.{u}) → ReconstructedIntegralMonoid G
  /-- Functorial transport along an isomorphism of groups. -/
  reconstructMap : ∀ {G H : LocalGaloisGroup.{u}}, (G ⟶ H) → obj G ≃* obj H
  /-- Reconstructed transport is equivariant. -/
  reconstructMap_action : ∀ {G H : LocalGaloisGroup.{u}} (f : G ⟶ H)
      (σ : G.toProfiniteGrp) (x : obj G),
    reconstructMap f (σ • x) = f.equiv σ • reconstructMap f x
  /-- The identity group map induces the identity monoid map. -/
  reconstructMap_id : ∀ (G : LocalGaloisGroup.{u}),
    reconstructMap (CategoryStruct.id G) = MulEquiv.refl (obj G)
  /-- Reconstructed transport respects composition. -/
  reconstructMap_comp : ∀ {G H I : LocalGaloisGroup.{u}} (f : G ⟶ H) (g : H ⟶ I),
    reconstructMap (f ≫ g) = (reconstructMap f).trans (reconstructMap g)

/-- The integral Kummer comparison of Hoshi's Definition 7.4.  The integral index group is
trivial, so this is a single natural comparison rather than a nontrivial orbit. -/
@[pp_with_univ]
structure IntegralKummerComparison {reciprocity : LocalReciprocityFamily.{u}}
    (algorithm : IntegralMonoAnabelianAlgorithm.{u} reciprocity) where
  /-- The Kummer comparison between a model monoid and its reconstruction. -/
  comparison : (X : LocalGaloisMonoid.{u}) →
    X.integerMonoid ≃* algorithm.obj X.toLocalGaloisGroup
  /-- The Kummer comparison is equivariant. -/
  comparison_action : ∀ (X : LocalGaloisMonoid.{u})
      (σ : X.toProfiniteGrp) (x : X.integerMonoid),
    comparison X (X.galoisAct σ x) = σ • comparison X x
  /-- Kummer comparisons form a natural family. -/
  comparison_natural : ∀ {X Y : LocalGaloisMonoid.{u}} (f : X ⟶ Y),
    (comparison X).trans (algorithm.reconstructMap f.groupHom) =
      f.monoidIso.trans (comparison Y)

/-- The complete integral reconstruction data used in Theorem 7.6. -/
@[pp_with_univ]
structure IntegralReconstruction (reciprocity : LocalReciprocityFamily.{u}) where
  algorithm : IntegralMonoAnabelianAlgorithm.{u} reciprocity
  kummer : IntegralKummerComparison.{u} algorithm

namespace IntegralReconstruction

variable {reciprocity : LocalReciprocityFamily.{u}}

abbrev obj (R : IntegralReconstruction.{u} reciprocity) := R.algorithm.obj

abbrev reconstructMap (R : IntegralReconstruction.{u} reciprocity)
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H) : R.obj G ≃* R.obj H :=
  R.algorithm.reconstructMap f

abbrev reconstructMap_action (R : IntegralReconstruction.{u} reciprocity)
    {G H : LocalGaloisGroup.{u}} (f : G ⟶ H)
    (σ : G.toProfiniteGrp) (x : R.obj G) :
    R.reconstructMap f (σ • x) = f.equiv σ • R.reconstructMap f x :=
  R.algorithm.reconstructMap_action f σ x

abbrev comparison (R : IntegralReconstruction.{u} reciprocity) := R.kummer.comparison

abbrev comparison_action (R : IntegralReconstruction.{u} reciprocity) :=
  R.kummer.comparison_action

abbrev comparison_natural (R : IntegralReconstruction.{u} reciprocity)
    {X Y : LocalGaloisMonoid.{u}} (f : X ⟶ Y) :
    (R.comparison X).trans (R.reconstructMap f.groupHom) =
      f.monoidIso.trans (R.comparison Y) :=
  R.kummer.comparison_natural f

end IntegralReconstruction
end LCFT
end Anabelian
