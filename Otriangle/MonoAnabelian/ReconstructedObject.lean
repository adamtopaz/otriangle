import Otriangle.MonoAnabelian.FixedFieldComparison
import Otriangle.MonoAnabelian.Interface

/-!
# The reconstructed integral monoid as a Galois monoid

The transfer colimit is a commutative monoid.  Its comparison with the algebraic-closure integer
monoid transports the canonical Galois action to the colimit and makes the comparison equivariant.
-/

noncomputable section

namespace Anabelian
namespace LCFT

universe u

section TransportAction

variable {Γ A B : Type*} [Group Γ] [Monoid A] [Monoid B]

/-- Transport a multiplicative group action through a multiplicative equivalence. -/
@[implicit_reducible]
def transportMulDistribMulAction (a : MulDistribMulAction Γ A) (e : A ≃* B) :
    MulDistribMulAction Γ B where
  smul σ x := e (a.smul σ (e.symm x))
  one_smul x := by
    change e (a.smul 1 (e.symm x)) = x
    exact (congrArg e (a.one_smul (e.symm x))).trans (e.apply_symm_apply x)
  mul_smul σ τ x := by
    change e (a.smul (σ * τ) (e.symm x)) =
      e (a.smul σ (e.symm (e (a.smul τ (e.symm x)))))
    rw [e.symm_apply_apply]
    exact congrArg e (a.mul_smul σ τ (e.symm x))
  smul_one σ := by
    change e (a.smul σ (e.symm 1)) = 1
    calc
      e (a.smul σ (e.symm 1)) = e (a.smul σ 1) := by rw [map_one]
      _ = e 1 := congrArg e (a.smul_one σ)
      _ = 1 := map_one e
  smul_mul σ x y := by
    change e (a.smul σ (e.symm (x * y))) =
      e (a.smul σ (e.symm x)) * e (a.smul σ (e.symm y))
    calc
      e (a.smul σ (e.symm (x * y))) =
          e (a.smul σ (e.symm x * e.symm y)) := by rw [map_mul]
      _ = e (a.smul σ (e.symm x) * a.smul σ (e.symm y)) :=
        congrArg e (a.smul_mul σ (e.symm x) (e.symm y))
      _ = e (a.smul σ (e.symm x)) * e (a.smul σ (e.symm y)) := map_mul e _ _

theorem transportMulDistribMulAction_smul
    (a : MulDistribMulAction Γ A) (e : A ≃* B) (σ : Γ) (x : A) :
    e (a.smul σ x) = (transportMulDistribMulAction a e).smul σ (e x) := by
  change e (a.smul σ x) = e (a.smul σ (e.symm (e x)))
  rw [e.symm_apply_apply]

end TransportAction

namespace ReconstructedIntegralMonoid

open OTriangle

variable (G : LocalGaloisGroup.{u})

/-- The canonical action on the actual integral monoid, with its acting group expressed through
the bundled profinite realization of `G`. -/
@[implicit_reducible]
noncomputable def actualAction :
    MulDistribMulAction G.toProfiniteGrp G.presentation.integerMonoid := by
  change MulDistribMulAction
    (G.presentation.algebraicClosure ≃ₐ[G.presentation]
      G.presentation.algebraicClosure) G.presentation.integerMonoid
  exact PointedMixedCharLocalField.integerMonoidMulDistribMulAction G.presentation

/-- Package any monoid equivalent to the actual integral monoid as a reconstructed monoid, by
transporting the Galois action through the given equivalence. -/
@[implicit_reducible]
noncomputable def ofMulEquiv {B : Type u} [CommMonoid B]
    (e : G.presentation.integerMonoid ≃* B) : ReconstructedIntegralMonoid G where
  carrier := B
  commMonoid := inferInstance
  action := transportMulDistribMulAction (actualAction G) e

/-- The equivalence used to package `ofMulEquiv`. -/
noncomputable def comparisonOfMulEquiv {B : Type u} [CommMonoid B]
    (e : G.presentation.integerMonoid ≃* B) :
    G.presentation.integerMonoid ≃* ofMulEquiv G e := e

theorem comparisonOfMulEquiv_action {B : Type u} [CommMonoid B]
    (e : G.presentation.integerMonoid ≃* B) (σ : G.toProfiniteGrp)
    (x : G.presentation.integerMonoid) :
    comparisonOfMulEquiv G e ((actualAction G).smul σ x) =
      σ • comparisonOfMulEquiv G e x := by
  change e ((actualAction G).smul σ x) =
    (transportMulDistribMulAction (actualAction G) e).smul σ (e x)
  exact transportMulDistribMulAction_smul (actualAction G) e σ x

end ReconstructedIntegralMonoid

end LCFT

namespace OTriangle
namespace LocalGaloisGroup

variable (G : LocalGaloisGroup.{u})
variable (reciprocity : LCFT.LocalReciprocityFamily.{u})

/-- The carrier reconstructed as the transfer colimit over open subgroups. -/
abbrev reconstructedDirectLimit : Type u :=
  DirectLimit ((G.fixedFieldFiniteExtensionSystem).reconstructedNode reciprocity)
    ((G.fixedFieldFiniteExtensionSystem).reconstructedTransition reciprocity)

/-- The transfer colimit, equipped with the Galois action identified by the fixed-field
comparison. -/
@[implicit_reducible]
noncomputable def reconstructedIntegralMonoid : LCFT.ReconstructedIntegralMonoid G :=
  LCFT.ReconstructedIntegralMonoid.ofMulEquiv G
    (G.fixedFieldReconstructedDirectLimitEquiv reciprocity)

/-- The fixed-field colimit comparison as an equivalence into the packaged reconstructed
monoid. -/
noncomputable def reconstructedIntegralMonoidComparison :
    G.presentation.integerMonoid ≃* G.reconstructedIntegralMonoid reciprocity :=
  LCFT.ReconstructedIntegralMonoid.comparisonOfMulEquiv G
    (G.fixedFieldReconstructedDirectLimitEquiv reciprocity)

end LocalGaloisGroup
end OTriangle
end Anabelian
