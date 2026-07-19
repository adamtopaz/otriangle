import Otriangle.MonoAnabelian.OpenSubgroups
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Fixed fields of open subgroups

This module records the infinite-Galois-theoretic bridge used by Hoshi's Definition 4.1.  An open
subgroup of an absolute Galois group has a finite fixed field, is the absolute Galois group over
that fixed field, and the fixed fields cover the chosen algebraic closure.
-/

noncomputable section

namespace Anabelian
namespace OTriangle
namespace LocalGaloisGroup

universe u

variable (G : LocalGaloisGroup.{u})

/-- The intermediate field fixed by an open subgroup. -/
abbrev fixedField (U : G.OpenSubgroupIndex) :
    IntermediateField G.presentation G.presentation.algebraicClosure :=
  IntermediateField.fixedField (OrderDual.ofDual U).toSubgroup

/-- Reverse inclusion of open subgroups gives inclusion of their fixed fields. -/
theorem fixedField_mono {U V : G.OpenSubgroupIndex} (h : U ≤ V) :
    G.fixedField U ≤ G.fixedField V :=
  IntermediateField.fixedField_antitone h

/-- The fixed field of an open subgroup is finite over the base local field. -/
theorem fixedField_finiteDimensional (U : G.OpenSubgroupIndex) :
    FiniteDimensional G.presentation (G.fixedField U) := by
  let U' : OpenSubgroup G.toProfiniteGrp := OrderDual.ofDual U
  let C : ClosedSubgroup G.toProfiniteGrp := ⟨U'.toSubgroup, U'.isClosed⟩
  apply (InfiniteGalois.isOpen_iff_finite (G.fixedField U)).mp
  have hfix : (G.fixedField U).fixingSubgroup = U'.toSubgroup :=
    InfiniteGalois.fixingSubgroup_fixedField C
  rw [hfix]
  exact U'.isOpen

/-- The fixed field of a normal open subgroup is Galois over the presented field. -/
theorem fixedField_isGalois_of_normal
    (U : OpenSubgroup G.toProfiniteGrp) (hN : U.toSubgroup.Normal) :
    IsGalois G.presentation (G.fixedField (OrderDual.toDual U)) := by
  let V : G.OpenSubgroupIndex := OrderDual.toDual U
  let e : G.toProfiniteGrp ≃* LCFT.AbsoluteGaloisGroup G.presentation :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  let H : Subgroup (LCFT.AbsoluteGaloisGroup G.presentation) :=
    U.toSubgroup.map e.toMonoidHom
  letI : H.Normal := hN.map e.toMonoidHom e.surjective
  have hfield : IntermediateField.fixedField H = G.fixedField V := by
    ext x
    simp only [IntermediateField.mem_fixedField_iff]
    constructor
    · intro hx f hf
      exact hx f ⟨f, hf, rfl⟩
    · intro hx f hf
      obtain ⟨g, hg, rfl⟩ := hf
      exact hx g hg
  exact hfield ▸
    (inferInstance : IsGalois G.presentation (IntermediateField.fixedField H))

/-- An open subgroup is multiplicatively equivalent to the absolute Galois group of its fixed
field inside the chosen algebraic closure. -/
noncomputable def fixedFieldGaloisEquiv (U : G.OpenSubgroupIndex) :
    (OrderDual.ofDual U).toSubgroup ≃*
      (G.presentation.algebraicClosure ≃ₐ[G.fixedField U]
        G.presentation.algebraicClosure) := by
  let U' : OpenSubgroup G.toProfiniteGrp := OrderDual.ofDual U
  let C : ClosedSubgroup G.toProfiniteGrp := ⟨U'.toSubgroup, U'.isClosed⟩
  have hfix : (G.fixedField U).fixingSubgroup = U'.toSubgroup :=
    InfiniteGalois.fixingSubgroup_fixedField C
  exact (MulEquiv.subgroupCongr hfix.symm).trans
    (IntermediateField.fixingSubgroupEquiv (G.fixedField U))

@[simp]
theorem fixedFieldGaloisEquiv_apply_coe (U : G.OpenSubgroupIndex)
    (σ : (OrderDual.ofDual U).toSubgroup) (x : G.presentation.algebraicClosure) :
    G.fixedFieldGaloisEquiv U σ x =
      (show G.presentation.algebraicClosure ≃ₐ[G.presentation]
        G.presentation.algebraicClosure from σ.1) x :=
  rfl

/-- Every element of the algebraic closure lies in the fixed field of some open subgroup. -/
theorem exists_mem_fixedField (x : G.presentation.algebraicClosure) :
    ∃ U : G.OpenSubgroupIndex, x ∈ G.fixedField U := by
  let E : IntermediateField G.presentation G.presentation.algebraicClosure :=
    IntermediateField.adjoin G.presentation {x}
  letI : FiniteDimensional G.presentation E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  let U' : OpenSubgroup G.toProfiniteGrp :=
    ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen⟩
  refine ⟨OrderDual.toDual U', ?_⟩
  change x ∈ IntermediateField.fixedField E.fixingSubgroup
  rw [InfiniteGalois.fixedField_fixingSubgroup E]
  exact IntermediateField.subset_adjoin (F := G.presentation) (S := {x}) (Set.mem_singleton x)

end LocalGaloisGroup
end OTriangle
end Anabelian
