import Otriangle.MonoAnabelian.Algorithm

/-!
# The integral Kummer comparison

The transfer colimit comes with a canonical comparison from the actual monoid of nonzero
algebraic integers.  Its equivariance was proved when the reconstructed action was defined.  This
file isolates the remaining assertion in Hoshi's integral Kummer comparison: these objectwise
comparisons are natural for every isomorphism of integral Galois pairs.

Keeping the naturality statement as a named proposition makes the dependency boundary precise:
the fixed-field construction supplies the functorial algorithm, while Hoshi's cyclotomic
synchronization and Kummer argument supply this final rigidity theorem.
-/

noncomputable section

open CategoryTheory

namespace Anabelian
namespace OTriangle

universe u

/-- Naturality of the canonical fixed-field comparison.  This is the integral specialization of
Hoshi's Kummer poly-isomorphism: the integral ambiguity group is trivial, so the comparison is a
single natural isomorphism. -/
def IntegralKummerNaturality
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (hoshi : LocalGaloisGroup.HoshiRamificationComparisonFamily.{u}) : Prop :=
  ∀ {X Y : LocalGaloisMonoid.{u}} (f : X ⟶ Y),
    (X.toLocalGaloisGroup.reconstructedIntegralMonoidComparison reciprocity).trans
        (LocalGaloisGroup.reconstructedDirectLimitEquivOfHoshiComparison
          f.groupHom reciprocity hoshi) =
      f.monoidIso.trans
        (Y.toLocalGaloisGroup.reconstructedIntegralMonoidComparison reciprocity)

/-- The objectwise fixed-field comparisons form an `IntegralKummerComparison` once their Kummer
naturality theorem is supplied. -/
noncomputable def integralKummerComparisonOfHoshiComparison
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (hoshi : LocalGaloisGroup.HoshiRamificationComparisonFamily.{u})
    (kummerNaturality : IntegralKummerNaturality reciprocity hoshi) :
    LCFT.IntegralKummerComparison.{u}
      (integralMonoAnabelianAlgorithmOfHoshiComparison reciprocity hoshi) where
  comparison X :=
    X.toLocalGaloisGroup.reconstructedIntegralMonoidComparison reciprocity
  comparison_action X σ x :=
    X.toLocalGaloisGroup.reconstructedIntegralMonoidComparison_action
      reciprocity σ x
  comparison_natural f := kummerNaturality f

/-- The fixed-field algorithm and the canonical Kummer comparisons assemble into the complete
integral reconstruction data after the two arithmetic comparison theorems are available. -/
noncomputable def integralReconstructionOfHoshiComparison
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (hoshi : LocalGaloisGroup.HoshiRamificationComparisonFamily.{u})
    (kummerNaturality : IntegralKummerNaturality reciprocity hoshi) :
    LCFT.IntegralReconstruction.{u} reciprocity where
  algorithm := integralMonoAnabelianAlgorithmOfHoshiComparison reciprocity hoshi
  kummer := integralKummerComparisonOfHoshiComparison
    reciprocity hoshi kummerNaturality

end OTriangle
end Anabelian
