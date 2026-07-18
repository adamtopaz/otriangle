import Otriangle.MonoAnabelian.FixedFields
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# The algebraic closure as a filtered union of fixed fields

This module proves the field-theoretic half of Hoshi's Proposition 4.2 for the nonzero integral
monoid.  The nonzero elements integral over the base valuation ring in the finite fixed fields form
a directed system, and its direct limit is the nonzero integral monoid in the algebraic closure.
-/

noncomputable section

namespace Anabelian
namespace OTriangle
namespace LocalGaloisGroup

open ValuativeRel

universe u

variable (G : LocalGaloisGroup.{u})

/-- The nonzero elements of the integral closure of the base valuation ring in a fixed field. -/
def fixedFieldIntegerSubmonoid (U : G.OpenSubgroupIndex) :
    Submonoid (integralClosure 𝒪[G.presentation] (G.fixedField U)) where
  carrier := {x | x ≠ 0}
  one_mem' := one_ne_zero
  mul_mem' hx hy := mul_ne_zero hx hy

/-- The field-theoretic integral monoid at an open-subgroup index. -/
abbrev fixedFieldIntegerMonoid (U : G.OpenSubgroupIndex) : Type u :=
  G.fixedFieldIntegerSubmonoid U

/-- The algebra homomorphism between integral closures induced by inclusion of fixed fields. -/
noncomputable def fixedFieldIntegralClosureMap {U V : G.OpenSubgroupIndex} (h : U ≤ V) :
    integralClosure 𝒪[G.presentation] (G.fixedField U) →ₐ[𝒪[G.presentation]]
      integralClosure 𝒪[G.presentation] (G.fixedField V) :=
  ((IntermediateField.inclusion (G.fixedField_mono h)).restrictScalars
    𝒪[G.presentation]).mapIntegralClosure

/-- Inclusion of fixed fields preserves nonzero integral elements. -/
noncomputable def fixedFieldIntegerMonoidMap {U V : G.OpenSubgroupIndex} (h : U ≤ V) :
    G.fixedFieldIntegerMonoid U →* G.fixedFieldIntegerMonoid V where
  toFun x := ⟨G.fixedFieldIntegralClosureMap h x.1, by
    intro hx
    apply x.property
    apply Subtype.ext
    apply Subtype.ext
    have hx' := congrArg
      (fun z : integralClosure 𝒪[G.presentation] (G.fixedField V) ↦
        ((z : G.fixedField V) : G.presentation.algebraicClosure)) hx
    exact hx'⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (G.fixedFieldIntegralClosureMap h)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (G.fixedFieldIntegralClosureMap h) x.1 y.1

/-- The transition map with its indices explicit, as required by `DirectLimit`. -/
noncomputable abbrev fixedFieldIntegerTransition (U V : G.OpenSubgroupIndex) (h : U ≤ V) :
    G.fixedFieldIntegerMonoid U →* G.fixedFieldIntegerMonoid V :=
  G.fixedFieldIntegerMonoidMap h

/-- The fixed-field integral monoids and their inclusion maps form a directed system. -/
instance fixedFieldIntegerDirectedSystem :
    DirectedSystem G.fixedFieldIntegerMonoid (G.fixedFieldIntegerTransition · · ·) where
  map_self := by
    intro U x
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_map := by
    intro W V U hUV hVW x
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Inclusion of one fixed field into the algebraic closure, restricted to integral elements. -/
noncomputable def fixedFieldToIntegerMonoid (U : G.OpenSubgroupIndex) :
    G.fixedFieldIntegerMonoid U →* G.presentation.integerMonoid where
  toFun x := by
    let f : G.fixedField U →ₐ[𝒪[G.presentation]] G.presentation.algebraicClosure :=
      (G.fixedField U).val.restrictScalars 𝒪[G.presentation]
    refine ⟨f.mapIntegralClosure x.1, ?_⟩
    intro hx
    apply x.property
    apply Subtype.ext
    have hx' := congrArg
      (fun z : integralClosure 𝒪[G.presentation] G.presentation.algebraicClosure ↦
        (z : G.presentation.algebraicClosure)) hx
    exact Subtype.ext hx'
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    rfl

theorem fixedFieldToIntegerMonoid_injective (U : G.OpenSubgroupIndex) :
    Function.Injective (G.fixedFieldToIntegerMonoid U) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  have h' := congrArg
    (fun z : G.presentation.integerMonoid ↦
      (((z.1 : integralClosure 𝒪[G.presentation] G.presentation.algebraicClosure) :
        G.presentation.algebraicClosure))) h
  exact h'

/-- The inclusion maps into the algebraic closure commute with fixed-field transitions. -/
theorem fixedFieldToIntegerMonoid_natural {U V : G.OpenSubgroupIndex} (h : U ≤ V)
    (x : G.fixedFieldIntegerMonoid U) :
    G.fixedFieldToIntegerMonoid U x =
      G.fixedFieldToIntegerMonoid V (G.fixedFieldIntegerMonoidMap h x) := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

set_option synthInstance.maxHeartbeats 200000 in
-- The dependent transition family makes synthesis for `DirectLimit.lift_mul` unusually expensive.
/-- The direct limit of fixed-field integral monoids maps canonically to the algebraic closure. -/
noncomputable def fixedFieldDirectLimitToIntegerMonoid :
    DirectLimit G.fixedFieldIntegerMonoid G.fixedFieldIntegerTransition →*
      G.presentation.integerMonoid where
  toFun := DirectLimit.lift G.fixedFieldIntegerTransition
    (fun i x ↦ G.fixedFieldToIntegerMonoid i x)
    (fun _ _ h x ↦ G.fixedFieldToIntegerMonoid_natural h x)
  map_one' := DirectLimit.lift_one
    (f := G.fixedFieldIntegerTransition)
    (g := fun i ↦ G.fixedFieldToIntegerMonoid i)
    (h := fun _ _ h x ↦ G.fixedFieldToIntegerMonoid_natural h x)
  map_mul' := DirectLimit.lift_mul
    (f := G.fixedFieldIntegerTransition)
    (g := fun i ↦ G.fixedFieldToIntegerMonoid i)
    (h := fun _ _ h x ↦ G.fixedFieldToIntegerMonoid_natural h x)

set_option synthInstance.maxHeartbeats 200000 in
-- Unfolding the dependent direct-limit hom requires the same enlarged synthesis budget.
/-- The field-theoretic fixed-field colimit is the nonzero integral monoid in the algebraic
closure. -/
noncomputable def fixedFieldDirectLimitEquiv :
    DirectLimit G.fixedFieldIntegerMonoid G.fixedFieldIntegerTransition ≃*
      G.presentation.integerMonoid := by
  let forward :
      DirectLimit G.fixedFieldIntegerMonoid G.fixedFieldIntegerTransition →*
        G.presentation.integerMonoid := G.fixedFieldDirectLimitToIntegerMonoid
  apply MulEquiv.ofBijective forward
  constructor
  · intro x y hxy
    induction x, y using DirectLimit.induction₂ with
    | _ i x y =>
      change G.fixedFieldToIntegerMonoid i x = G.fixedFieldToIntegerMonoid i y at hxy
      exact congrArg (fun z ↦ (⟦⟨i, z⟩⟧ :
        DirectLimit G.fixedFieldIntegerMonoid G.fixedFieldIntegerTransition))
        (G.fixedFieldToIntegerMonoid_injective i hxy)
  · intro x
    obtain ⟨U, hxU⟩ := G.exists_mem_fixedField
      ((x.1 : integralClosure 𝒪[G.presentation] G.presentation.algebraicClosure) :
        G.presentation.algebraicClosure)
    let y : G.fixedField U :=
      ⟨((x.1 : integralClosure 𝒪[G.presentation] G.presentation.algebraicClosure) :
        G.presentation.algebraicClosure), hxU⟩
    have hyIntegral : IsIntegral 𝒪[G.presentation] y := by
      apply IntermediateField.coe_isIntegral_iff.mp
      exact x.1.property
    let yInt : integralClosure 𝒪[G.presentation] (G.fixedField U) := ⟨y, hyIntegral⟩
    have hyNe : yInt ≠ 0 := by
      intro hy
      apply x.property
      apply Subtype.ext
      have hy' := congrArg
        (fun z : integralClosure 𝒪[G.presentation] (G.fixedField U) ↦
          ((z : G.fixedField U) : G.presentation.algebraicClosure)) hy
      exact hy'
    let yMon : G.fixedFieldIntegerMonoid U := ⟨yInt, hyNe⟩
    refine ⟨(⟦⟨U, yMon⟩⟧ :
      DirectLimit G.fixedFieldIntegerMonoid G.fixedFieldIntegerTransition), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl

@[simp]
theorem fixedFieldDirectLimitEquiv_mk (U : G.OpenSubgroupIndex)
    (x : G.fixedFieldIntegerMonoid U) :
    G.fixedFieldDirectLimitEquiv
        (⟦⟨U, x⟩⟧ : DirectLimit G.fixedFieldIntegerMonoid G.fixedFieldIntegerTransition) =
      G.fixedFieldToIntegerMonoid U x :=
  by
    change G.fixedFieldDirectLimitToIntegerMonoid
      (⟦⟨U, x⟩⟧ : DirectLimit G.fixedFieldIntegerMonoid G.fixedFieldIntegerTransition) =
        G.fixedFieldToIntegerMonoid U x
    rfl

end LocalGaloisGroup
end OTriangle
end Anabelian
