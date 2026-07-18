import Mathlib.Algebra.Colimit.DirectLimit
import Otriangle.MonoAnabelian.TransferSystem

/-!
# Multiplicative equivalences of filtered colimits

This module supplies the abstract filtered-colimit step used in Hoshi's Proposition 4.2.  A
natural family of homomorphisms between directed systems of monoids induces a homomorphism of
their direct limits, and a natural family of multiplicative equivalences induces a multiplicative
equivalence of direct limits.
-/

noncomputable section

namespace Anabelian
namespace LCFT
namespace FilteredColimit

universe u v w

variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {A : ι → Type v} {B : ι → Type w}
variable [∀ i, Monoid (A i)] [∀ i, Monoid (B i)]
variable (fA : ∀ i j, i ≤ j → A i →* A j)
variable (fB : ∀ i j, i ≤ j → B i →* B j)
variable [DirectedSystem A (fA · · ·)] [DirectedSystem B (fB · · ·)]

/-- A natural family of monoid homomorphisms induces a homomorphism of direct limits. -/
noncomputable def mapMonoidHom (g : ∀ i, A i →* B i)
    (natural : ∀ i j (h : i ≤ j),
      (g j).comp (fA i j h) = (fB i j h).comp (g i)) :
    DirectLimit A fA →* DirectLimit B fB where
  toFun := DirectLimit.map fA fB (fun i ↦ g i) fun i j h x ↦
    (DFunLike.congr_fun (natural i j h) x).symm
  map_one' := by
    let ⟨i⟩ := ‹Nonempty ι›
    rw [DirectLimit.one_def i, DirectLimit.map_def, map_one, ← DirectLimit.one_def i]
  map_mul' := by
    intro x y
    induction x, y using DirectLimit.induction₂ with
    | _ i x y =>
      rw [DirectLimit.mul_def, DirectLimit.map_def, map_mul,
        DirectLimit.map_def, DirectLimit.map_def, DirectLimit.mul_def]

@[simp]
theorem mapMonoidHom_mk (g : ∀ i, A i →* B i)
    (natural : ∀ i j (h : i ≤ j),
      (g j).comp (fA i j h) = (fB i j h).comp (g i))
    (i : ι) (x : A i) :
    mapMonoidHom fA fB g natural (⟦⟨i, x⟩⟧ : DirectLimit A fA) =
      (⟦⟨i, g i x⟩⟧ : DirectLimit B fB) :=
  rfl

/-- A natural family of multiplicative equivalences induces an equivalence of direct limits. -/
noncomputable def mulEquiv (e : ∀ i, A i ≃* B i)
    (natural : ∀ i j (h : i ≤ j),
      (e j).toMonoidHom.comp (fA i j h) =
        (fB i j h).comp (e i).toMonoidHom) :
    DirectLimit A fA ≃* DirectLimit B fB := by
  have symm_natural : ∀ i j (h : i ≤ j),
      ((e j).symm : B j →* A j).comp (fB i j h) =
        (fA i j h).comp ((e i).symm : B i →* A i) := by
    intro i j h
    ext y
    change (e j).symm (fB i j h y) = fA i j h ((e i).symm y)
    apply (e j).injective
    rw [(e j).apply_symm_apply]
    symm
    calc
      e j (fA i j h ((e i).symm y)) =
          fB i j h (e i ((e i).symm y)) :=
        DFunLike.congr_fun (natural i j h) ((e i).symm y)
      _ = fB i j h y := congrArg (fB i j h) ((e i).apply_symm_apply y)
  let forward := mapMonoidHom fA fB (fun i ↦ (e i).toMonoidHom) natural
  let backward := mapMonoidHom fB fA (fun i ↦ ((e i).symm : B i →* A i)) symm_natural
  exact
    { toFun := forward
      invFun := backward
      left_inv := by
        intro x
        induction x using DirectLimit.induction with
        | _ i x =>
          rw [show forward (⟦⟨i, x⟩⟧ : DirectLimit A fA) =
              (⟦⟨i, e i x⟩⟧ : DirectLimit B fB) from rfl,
            show backward (⟦⟨i, e i x⟩⟧ : DirectLimit B fB) =
              (⟦⟨i, (e i).symm (e i x)⟩⟧ : DirectLimit A fA) from rfl,
            (e i).symm_apply_apply]
      right_inv := by
        intro y
        induction y using DirectLimit.induction with
        | _ i y =>
          rw [show backward (⟦⟨i, y⟩⟧ : DirectLimit B fB) =
              (⟦⟨i, (e i).symm y⟩⟧ : DirectLimit A fA) from rfl,
            show forward (⟦⟨i, (e i).symm y⟩⟧ : DirectLimit A fA) =
              (⟦⟨i, e i ((e i).symm y)⟩⟧ : DirectLimit B fB) from rfl,
            (e i).apply_symm_apply]
      map_mul' := forward.map_mul }

@[simp]
theorem mulEquiv_mk (e : ∀ i, A i ≃* B i)
    (natural : ∀ i j (h : i ≤ j),
      (e j).toMonoidHom.comp (fA i j h) =
        (fB i j h).comp (e i).toMonoidHom)
    (i : ι) (x : A i) :
    mulEquiv fA fB e natural (⟦⟨i, x⟩⟧ : DirectLimit A fA) =
      (⟦⟨i, e i x⟩⟧ : DirectLimit B fB) :=
  rfl

end FilteredColimit
end LCFT
end Anabelian
