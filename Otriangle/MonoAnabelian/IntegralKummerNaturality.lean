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

set_option maxHeartbeats 4000000 in
-- Expanding the transported actions in this comparison square is elaboration-intensive.
/-- The canonical fixed-field comparisons are natural for isomorphisms of integral local Galois
pairs.  This is the integral specialization of Hoshi's Kummer poly-isomorphism. -/
theorem integralKummerNaturality_of_reciprocity
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (hoshi : LocalGaloisGroup.HoshiRamificationComparisonFamily.{u}) :
    IntegralKummerNaturality reciprocity hoshi := by
  intro X Y f
  let cX := X.toLocalGaloisGroup.reconstructedIntegralMonoidComparison reciprocity
  let cY := Y.toLocalGaloisGroup.reconstructedIntegralMonoidComparison reciprocity
  let r := LocalGaloisGroup.reconstructedDirectLimitEquivOfHoshiComparison
    f.groupHom reciprocity hoshi
  let canonical : X.integerMonoid ≃* Y.integerMonoid :=
    cX.trans (r.trans cY.symm)
  have hcanonical : ∀ (σ : X.toProfiniteGrp) (x : X.integerMonoid),
      canonical (X.galoisAct σ x) =
        Y.galoisAct (f.groupHom.equiv σ) (canonical x) := by
    intro σ x
    apply cY.injective
    change r (cX (X.galoisAct σ x)) =
      cY (Y.galoisAct (f.groupHom.equiv σ) (cY.symm (r (cX x))))
    rw [X.toLocalGaloisGroup.reconstructedIntegralMonoidComparison_action,
      LocalGaloisGroup.reconstructedDirectLimitEquivOfHoshiComparison_action,
      Y.toLocalGaloisGroup.reconstructedIntegralMonoidComparison_action,
      cY.apply_symm_apply]
  have hfInv : ∀ (τ : Y.toProfiniteGrp) (y : Y.integerMonoid),
      f.monoidIso.symm (Y.galoisAct τ y) =
        X.galoisAct (f.groupHom.equiv.symm τ) (f.monoidIso.symm y) := by
    intro τ y
    apply f.monoidIso.injective
    rw [f.monoidIso.apply_symm_apply, f.action_compatible,
      f.groupHom.equiv.apply_symm_apply, f.monoidIso.apply_symm_apply]
  let delta : X.integerMonoid ≃* X.integerMonoid :=
    canonical.trans f.monoidIso.symm
  have hdelta : ∀ (σ : X.toProfiniteGrp) (x : X.integerMonoid),
      delta (X.galoisAct σ x) = X.galoisAct σ (delta x) := by
    intro σ x
    change f.monoidIso.symm (canonical (X.galoisAct σ x)) =
      X.galoisAct σ (f.monoidIso.symm (canonical x))
    rw [hcanonical, hfInv, f.groupHom.equiv.symm_apply_apply]
  have hdeltaActual : ∀ (σ : X.toProfiniteGrp) (x : X.integerMonoid),
      delta ((LCFT.ReconstructedIntegralMonoid.actualAction
        X.toLocalGaloisGroup).smul σ x) =
        (LCFT.ReconstructedIntegralMonoid.actualAction
          X.toLocalGaloisGroup).smul σ (delta x) := by
    intro σ x
    exact hdelta σ x
  have hdeltaEq : delta = MulEquiv.refl X.integerMonoid :=
    X.toLocalGaloisGroup.centralIntegerMonoidEquiv_eq_refl delta hdeltaActual
  have hcanonicalEq : canonical = f.monoidIso := by
    apply MulEquiv.ext
    intro x
    have hx := congrArg (fun e : X.integerMonoid ≃* X.integerMonoid ↦ e x) hdeltaEq
    apply f.monoidIso.injective
    change f.monoidIso (f.monoidIso.symm (canonical x)) = f.monoidIso (f.monoidIso x)
    rw [f.monoidIso.apply_symm_apply]
    exact congrArg f.monoidIso hx
  apply MulEquiv.ext
  intro x
  have hx := congrArg (fun e : X.integerMonoid ≃* Y.integerMonoid ↦ e x) hcanonicalEq
  have := congrArg cY hx
  change cY (cY.symm (r (cX x))) = cY (f.monoidIso x) at this
  simpa only [cY.apply_symm_apply] using this

end OTriangle
end Anabelian
