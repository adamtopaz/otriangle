import Otriangle.MonoAnabelian.Interface

/-!
# Mono-anabelian transport

This module contains the formal categorical transport argument in Hoshi's Theorem 7.6.  It uses
only the functorial reconstruction and the natural Kummer comparison.
-/

noncomputable section

namespace Anabelian
namespace LCFT

open OTriangle

universe u

namespace IntegralReconstruction

variable {reciprocity : LocalReciprocityFamily.{u}}

/-- Conjugate reconstructed transport by the two canonical Kummer comparisons. -/
noncomputable def lift (R : IntegralReconstruction.{u} reciprocity)
    {X Y : LocalGaloisMonoid.{u}}
    (f : X.toLocalGaloisGroup ⟶ Y.toLocalGaloisGroup) : X ⟶ Y where
  groupHom := f
  monoidIso := (R.comparison X).trans ((R.reconstructMap f).trans (R.comparison Y).symm)
  action_compatible := by
    intro σ x
    simp only [MulEquiv.trans_apply]
    rw [R.comparison_action, R.reconstructMap_action]
    apply (R.comparison Y).injective
    rw [R.comparison_action, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

@[simp]
theorem lift_groupHom (R : IntegralReconstruction.{u} reciprocity)
    {X Y : LocalGaloisMonoid.{u}}
    (f : X.toLocalGaloisGroup ⟶ Y.toLocalGaloisGroup) :
    (R.lift f).groupHom = f := rfl

/-- Naturality of the unique integral comparison makes the group component injective. -/
theorem hom_ext (R : IntegralReconstruction.{u} reciprocity)
    {X Y : LocalGaloisMonoid.{u}} (f g : X ⟶ Y)
    (h : f.groupHom = g.groupHom) : f = g := by
  have hcomp : f.monoidIso.trans (R.comparison Y) =
      g.monoidIso.trans (R.comparison Y) := by
    calc
      f.monoidIso.trans (R.comparison Y) =
          (R.comparison X).trans (R.reconstructMap f.groupHom) :=
        (R.comparison_natural f).symm
      _ = (R.comparison X).trans (R.reconstructMap g.groupHom) := by rw [h]
      _ = g.monoidIso.trans (R.comparison Y) := R.comparison_natural g
  have hmonoid : f.monoidIso = g.monoidIso := by
    apply MulEquiv.ext
    intro x
    apply (R.comparison Y).injective
    exact DFunLike.congr_fun hcomp x
  exact LocalGaloisMonoid.Hom.ext h hmonoid

end IntegralReconstruction
end LCFT
end Anabelian
