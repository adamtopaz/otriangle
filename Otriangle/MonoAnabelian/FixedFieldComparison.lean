import Otriangle.MonoAnabelian.FixedFieldSystem
import Otriangle.MonoAnabelian.FieldColimit

/-!
# Comparison of the two fixed-field diagrams

The valuation ring of a spectral fixed field agrees with the integral closure of the base
valuation ring.  This identifies the field-theoretic diagram used by local reciprocity with the
fixed-field diagram whose colimit is the algebraic closure's integral monoid.
-/

noncomputable section

namespace Anabelian
namespace OTriangle
namespace LocalGaloisGroup

open ValuativeRel

universe u

variable (G : LocalGaloisGroup.{u})

/-- Nonzero spectral integers in a fixed field are the nonzero elements of the integral closure
of the base valuation ring. -/
noncomputable def fixedFieldBaseIntegerMonoidEquiv (U : G.OpenSubgroupIndex) :
    LCFT.baseIntegerMonoid (G.fixedFieldPointed U) ≃*
      G.fixedFieldIntegerMonoid U := by
  letI := G.presentation.nontriviallyNormedField
  letI := G.presentation.isUltrametricDist
  letI := G.presentation.completeSpace
  letI := G.fixedFieldNontriviallyNormedField U
  letI := G.fixedFieldIsUltrametricDist U
  letI : ValuativeRel (G.fixedField U) := G.fixedFieldValuativeRel U
  letI : ValuativeExtension G.presentation (G.fixedField U) :=
    G.fixedFieldValuativeExtensionFromPresentation U
  let forward : LCFT.baseIntegerMonoid (G.fixedFieldPointed U) →*
      G.fixedFieldIntegerMonoid U :=
    { toFun := fun x => by
        let z : 𝒪[G.fixedField U] := ⟨(x.1 : G.fixedField U), x.property⟩
        have hz : IsIntegral 𝒪[G.presentation] z :=
          G.presentation.spectralInteger_isIntegral (G.fixedField U) z
        let zInt : integralClosure 𝒪[G.presentation] (G.fixedField U) :=
          ⟨(x.1 : G.fixedField U), IsIntegral.algebraMap hz⟩
        exact ⟨zInt, by
          intro hz
          apply Units.ne_zero x.1
          have hz' := congrArg
            (fun w : integralClosure 𝒪[G.presentation] (G.fixedField U) =>
              (w : G.fixedField U)) hz
          exact hz'⟩
      map_one' := by ext; rfl
      map_mul' := by intro x y; ext; rfl }
  let backward : G.fixedFieldIntegerMonoid U →*
      LCFT.baseIntegerMonoid (G.fixedFieldPointed U) :=
    { toFun := fun y => by
        have hyne : (y.1 : G.fixedField U) ≠ 0 := by
          intro hy
          apply y.property
          apply Subtype.ext
          exact hy
        let yu : (G.fixedField U)ˣ := Units.mk0 (y.1 : G.fixedField U) hyne
        refine ⟨yu, ?_⟩
        have hyIntegral : IsIntegral 𝒪[G.fixedField U] (y.1 : G.fixedField U) :=
          IsIntegral.tower_top y.1.property
        exact (Valuation.integer.integers (valuation (G.fixedField U))).mem_of_integral
          hyIntegral
      map_one' := by ext; rfl
      map_mul' := by intro x y; ext; rfl }
  exact
    { toFun := forward
      invFun := backward
      left_inv := by intro x; ext; rfl
      right_inv := by intro y; ext; rfl
      map_mul' := forward.map_mul }

/-- The fixed-field integer identifications commute with inclusions. -/
theorem fixedFieldBaseIntegerMonoidEquiv_natural
    {U V : G.OpenSubgroupIndex} (h : U ≤ V) :
    (G.fixedFieldBaseIntegerMonoidEquiv V).toMonoidHom.comp
        ((G.fixedFieldFiniteExtensionSystem).baseTransition U V h) =
      (G.fixedFieldIntegerTransition U V h).comp
        (G.fixedFieldBaseIntegerMonoidEquiv U).toMonoidHom := by
  ext x
  rfl

/-- The LCFT base-node colimit is the fixed-field integral-closure colimit. -/
noncomputable def fixedFieldBaseDirectLimitEquiv :
    DirectLimit (G.fixedFieldFiniteExtensionSystem).baseNode
        (G.fixedFieldFiniteExtensionSystem).baseTransition ≃*
      DirectLimit G.fixedFieldIntegerMonoid G.fixedFieldIntegerTransition :=
  LCFT.FilteredColimit.mulEquiv
    (G.fixedFieldFiniteExtensionSystem).baseTransition
    G.fixedFieldIntegerTransition
    G.fixedFieldBaseIntegerMonoidEquiv
    (fun _ _ h => G.fixedFieldBaseIntegerMonoidEquiv_natural h)

variable (reciprocity : LCFT.LocalReciprocityFamily.{u})

/-- The integral monoid in the algebraic closure is the colimit reconstructed from transfer and
local reciprocity at all open subgroups. -/
noncomputable def fixedFieldReconstructedDirectLimitEquiv :
    G.presentation.integerMonoid ≃*
      DirectLimit ((G.fixedFieldFiniteExtensionSystem).reconstructedNode reciprocity)
        ((G.fixedFieldFiniteExtensionSystem).reconstructedTransition reciprocity) :=
  G.fixedFieldDirectLimitEquiv.symm |>.trans
    G.fixedFieldBaseDirectLimitEquiv.symm |>.trans
      ((G.fixedFieldFiniteExtensionSystem).directLimitEquiv reciprocity)

end LocalGaloisGroup
end OTriangle
end Anabelian
