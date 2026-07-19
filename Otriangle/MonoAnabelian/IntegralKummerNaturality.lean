import Otriangle.MonoAnabelian.IntegralKummerRigidity
import Otriangle.MonoAnabelian.KummerComparison

/-!
# Naturality of the integral Kummer comparison

The objectwise comparison with the fixed-field transfer colimit is already equivariant.  Given
an isomorphism of integral Galois pairs, transport across the two comparisons therefore differs
from the supplied monoid isomorphism by a central automorphism of the source integral monoid.
Integral Kummer rigidity says that this automorphism is the identity.
-/

noncomputable section

open CategoryTheory

namespace Anabelian
namespace OTriangle

universe u

private theorem equivariantIntegerMonoidEquiv_eq
    {B : Type u} [Mul B]
    {X Y : LocalGaloisMonoid.{u}} (f : X ⟶ Y)
    (actB : Y.toProfiniteGrp → B → B)
    (alpha beta : X.integerMonoid ≃* B)
    (halpha : ∀ (sigma : X.toProfiniteGrp) (x : X.integerMonoid),
      alpha ((LCFT.ReconstructedIntegralMonoid.actualAction
        X.toLocalGaloisGroup).smul sigma x) =
        actB (f.groupHom.equiv sigma) (alpha x))
    (hbeta : ∀ (sigma : X.toProfiniteGrp) (x : X.integerMonoid),
      beta ((LCFT.ReconstructedIntegralMonoid.actualAction
        X.toLocalGaloisGroup).smul sigma x) =
        actB (f.groupHom.equiv sigma) (beta x)) :
    alpha = beta := by
  have hbetaInv : ∀ (tau : Y.toProfiniteGrp) (y : B),
      beta.symm (actB tau y) =
        (LCFT.ReconstructedIntegralMonoid.actualAction
          X.toLocalGaloisGroup).smul (f.groupHom.equiv.symm tau) (beta.symm y) := by
    intro tau y
    apply beta.injective
    rw [beta.apply_symm_apply, hbeta,
      f.groupHom.equiv.apply_symm_apply, beta.apply_symm_apply]
  let delta : X.integerMonoid ≃* X.integerMonoid := alpha.trans beta.symm
  have hdelta : ∀ (sigma : X.toProfiniteGrp) (x : X.integerMonoid),
      delta ((LCFT.ReconstructedIntegralMonoid.actualAction
        X.toLocalGaloisGroup).smul sigma x) =
        (LCFT.ReconstructedIntegralMonoid.actualAction
          X.toLocalGaloisGroup).smul sigma (delta x) := by
    intro sigma x
    change beta.symm (alpha ((LCFT.ReconstructedIntegralMonoid.actualAction
      X.toLocalGaloisGroup).smul sigma x)) =
      (LCFT.ReconstructedIntegralMonoid.actualAction X.toLocalGaloisGroup).smul sigma
        (beta.symm (alpha x))
    rw [halpha, hbetaInv, f.groupHom.equiv.symm_apply_apply]
  have hdeltaEq : delta = MulEquiv.refl X.integerMonoid :=
    X.toLocalGaloisGroup.centralIntegerMonoidEquiv_eq_refl delta hdelta
  apply MulEquiv.ext
  intro x
  have hx := congrArg (fun e : X.integerMonoid ≃* X.integerMonoid ↦ e x) hdeltaEq
  have hx' := congrArg beta hx
  change beta (beta.symm (alpha x)) = beta x at hx'
  simpa only [beta.apply_symm_apply] using hx'

private theorem equivariantIntegerMonoidPairTrans_eq
    {B C D : Type u} [Mul B] [Mul C] [Mul D]
    {X Y : LocalGaloisMonoid.{u}} (f : X ⟶ Y)
    (a₁ : X.integerMonoid ≃* B) (a₂ : B ≃* D)
    (b₁ : X.integerMonoid ≃* C) (b₂ : C ≃* D)
    (actD : Y.toProfiniteGrp → D → D)
    (halpha : ∀ (sigma : X.toProfiniteGrp) (x : X.integerMonoid),
      a₂ (a₁ ((LCFT.ReconstructedIntegralMonoid.actualAction
        X.toLocalGaloisGroup).smul sigma x)) =
        actD (f.groupHom.equiv sigma) (a₂ (a₁ x)))
    (hbeta : ∀ (sigma : X.toProfiniteGrp) (x : X.integerMonoid),
      b₂ (b₁ ((LCFT.ReconstructedIntegralMonoid.actualAction
        X.toLocalGaloisGroup).smul sigma x)) =
        actD (f.groupHom.equiv sigma) (b₂ (b₁ x))) :
    a₁.trans a₂ = b₁.trans b₂ := by
  apply equivariantIntegerMonoidEquiv_eq f actD (a₁.trans a₂) (b₁.trans b₂)
  · intro sigma x
    change a₂ (a₁ ((LCFT.ReconstructedIntegralMonoid.actualAction
      X.toLocalGaloisGroup).smul sigma x)) =
        actD (f.groupHom.equiv sigma) (a₂ (a₁ x))
    exact halpha sigma x
  · intro sigma x
    change b₂ (b₁ ((LCFT.ReconstructedIntegralMonoid.actualAction
      X.toLocalGaloisGroup).smul sigma x)) =
        actD (f.groupHom.equiv sigma) (b₂ (b₁ x))
    exact hbeta sigma x

private theorem reconstructedForward_action
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (hoshi : LocalGaloisGroup.HoshiRamificationComparisonFamily.{u})
    {X Y : LocalGaloisMonoid.{u}} (f : X ⟶ Y)
    (sigma : X.toProfiniteGrp) (x : X.integerMonoid) :
    LocalGaloisGroup.reconstructedDirectLimitEquivOfHoshiComparison
        f.groupHom reciprocity hoshi
          (X.toLocalGaloisGroup.reconstructedIntegralMonoidComparison reciprocity
            ((LCFT.ReconstructedIntegralMonoid.actualAction
              X.toLocalGaloisGroup).smul sigma x)) =
      (Y.toLocalGaloisGroup.reconstructedDirectLimitAction reciprocity).smul
        (f.groupHom.equiv sigma)
          (LocalGaloisGroup.reconstructedDirectLimitEquivOfHoshiComparison
            f.groupHom reciprocity hoshi
              (X.toLocalGaloisGroup.reconstructedIntegralMonoidComparison reciprocity x)) := by
  let cX := X.toLocalGaloisGroup.reconstructedIntegralMonoidComparison reciprocity
  let r := LocalGaloisGroup.reconstructedDirectLimitEquivOfHoshiComparison
    f.groupHom reciprocity hoshi
  calc
    _ = r ((X.toLocalGaloisGroup.reconstructedDirectLimitAction reciprocity).smul
        sigma (cX x)) := congrArg r
      (X.toLocalGaloisGroup.fixedFieldReconstructedDirectLimitEquiv_action
        reciprocity sigma x)
    _ = _ :=
      (LocalGaloisGroup.reconstructedDirectLimitEquivOfHoshiComparison_action
        f.groupHom reciprocity hoshi sigma (cX x))

private theorem reconstructedTarget_action
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    {X Y : LocalGaloisMonoid.{u}} (f : X ⟶ Y)
    (sigma : X.toProfiniteGrp) (x : X.integerMonoid) :
    Y.toLocalGaloisGroup.reconstructedIntegralMonoidComparison reciprocity
        (f.monoidIso ((LCFT.ReconstructedIntegralMonoid.actualAction
          X.toLocalGaloisGroup).smul sigma x)) =
      (Y.toLocalGaloisGroup.reconstructedDirectLimitAction reciprocity).smul
        (f.groupHom.equiv sigma)
          (Y.toLocalGaloisGroup.reconstructedIntegralMonoidComparison reciprocity
            (f.monoidIso x)) := by
  have hf : f.monoidIso ((LCFT.ReconstructedIntegralMonoid.actualAction
      X.toLocalGaloisGroup).smul sigma x) =
      (LCFT.ReconstructedIntegralMonoid.actualAction Y.toLocalGaloisGroup).smul
        (f.groupHom.equiv sigma) (f.monoidIso x) := by
    exact f.action_compatible sigma x
  calc
    _ = Y.toLocalGaloisGroup.reconstructedIntegralMonoidComparison reciprocity
        ((LCFT.ReconstructedIntegralMonoid.actualAction Y.toLocalGaloisGroup).smul
          (f.groupHom.equiv sigma) (f.monoidIso x)) := congrArg
            (Y.toLocalGaloisGroup.reconstructedIntegralMonoidComparison reciprocity) hf
    _ = _ := Y.toLocalGaloisGroup.fixedFieldReconstructedDirectLimitEquiv_action
      reciprocity (f.groupHom.equiv sigma) (f.monoidIso x)

/-- The canonical fixed-field comparisons are natural for isomorphisms of integral local Galois
pairs.  This is the integral specialization of Hoshi's Kummer poly-isomorphism. -/
theorem integralKummerNaturality_of_reciprocity
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (hoshi : LocalGaloisGroup.HoshiRamificationComparisonFamily.{u}) :
    IntegralKummerNaturality reciprocity hoshi := by
  intro X Y f
  exact equivariantIntegerMonoidPairTrans_eq f
    (X.toLocalGaloisGroup.reconstructedIntegralMonoidComparison reciprocity)
    (LocalGaloisGroup.reconstructedDirectLimitEquivOfHoshiComparison
      f.groupHom reciprocity hoshi)
    f.monoidIso
    (Y.toLocalGaloisGroup.reconstructedIntegralMonoidComparison reciprocity)
    (fun tau (z : Y.toLocalGaloisGroup.reconstructedDirectLimit reciprocity) ↦
      (Y.toLocalGaloisGroup.reconstructedDirectLimitAction reciprocity).smul tau z)
    (reconstructedForward_action reciprocity hoshi f)
    (reconstructedTarget_action reciprocity f)

end OTriangle
end Anabelian
