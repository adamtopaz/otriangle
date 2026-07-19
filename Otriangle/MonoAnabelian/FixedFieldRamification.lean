import Otriangle.MonoAnabelian.FixedFieldSystem
import Otriangle.MonoAnabelian.GroupTransport
import Otriangle.MonoAnabelian.ExactGroupInvariants
import Otriangle.MonoAnabelian.LocalExtensionRamification
import Otriangle.MonoAnabelian.IntrinsicRamification

/-!
# Numerical ramification at open-subgroup fixed fields

The topological abelianization of an open subgroup is the abelianized absolute Galois group of
its finite fixed field.  Exact local reciprocity therefore evaluates Hoshi's numerical
ramification index there as the fixed field's absolute ramification index.  The local extension
tower formula then turns the two intrinsic neighborhood predicates into statements about the
relative ramification index of that fixed field.
-/

noncomputable section

open CategoryTheory

namespace Anabelian.OTriangle.LocalGaloisGroup

open LCFT

universe u

/-- The pointed fixed field of an open subgroup as a finite valued extension of the presentation. -/
noncomputable def fixedFieldBaseExtension (G : LocalGaloisGroup.{u})
    (U : G.OpenSubgroupIndex) :
    LCFT.FiniteExtension G.presentation (G.fixedFieldPointed U) := by
  letI := G.presentation.nontriviallyNormedField
  letI := G.presentation.isUltrametricDist
  letI := G.presentation.completeSpace
  letI := G.fixedFieldNontriviallyNormedField U
  letI := G.fixedFieldIsUltrametricDist U
  letI : ValuativeRel (G.fixedField U) := G.fixedFieldValuativeRel U
  refine
    { algebra := ?_
      finiteDimensional := ?_
      valuativeExtension := ?_ }
  · change Algebra G.presentation (G.fixedField U)
    infer_instance
  · change FiniteDimensional G.presentation (G.fixedField U)
    exact G.fixedField_finiteDimensional U
  · change ValuativeExtension G.presentation (G.fixedField U)
    exact G.fixedFieldValuativeExtensionFromPresentation U

/-- The intrinsic numerical ramification index of the ambient absolute Galois group is the
presentation's absolute ramification index. -/
theorem intrinsicRamificationIndex_eq_absoluteRamificationIndex
    (G : LocalGaloisGroup.{u})
    (reciprocity : LocalReciprocityFamily.{u}) :
    IntrinsicRamification.ramificationIndex G.toProfiniteGrp
        G.presentation.residueChar =
      absoluteRamificationIndex G.presentation := by
  exact abelianized_groupTheoreticRamificationIndex_eq_absoluteRamificationIndex
    (reciprocity.map G.presentation)

/-- At an open subgroup, the intrinsic numerical index is the absolute ramification index of
the corresponding fixed field. -/
theorem openSubgroupIntrinsicRamificationIndex_eq_fixedField
    (G : LocalGaloisGroup.{u})
    (reciprocity : LocalReciprocityFamily.{u})
    (U : OpenSubgroup G.toProfiniteGrp) :
    IntrinsicRamification.ramificationIndex U.toSubgroup
        G.presentation.residueChar =
      absoluteRamificationIndex
        (G.fixedFieldPointed (OrderDual.toDual U)) := by
  let V : G.OpenSubgroupIndex := OrderDual.toDual U
  let e := TopologicalAbelianization.congr
    (G.fixedFieldGaloisContinuousEquiv V)
  calc
    IntrinsicRamification.ramificationIndex U.toSubgroup
        G.presentation.residueChar =
      GroupTheoreticInvariants.ramificationIndex
        (AbelianizedAbsoluteGaloisGroup (G.fixedFieldPointed V))
        G.presentation.residueChar :=
      GroupTheoreticInvariants.ramificationIndex_congr e
        G.presentation.residueChar
    _ = absoluteRamificationIndex (G.fixedFieldPointed V) := by
      exact abelianized_groupTheoreticRamificationIndex_eq_absoluteRamificationIndex
        (reciprocity.map (G.fixedFieldPointed V))

/-- Equal-index intrinsic neighborhoods are precisely normal fixed fields of relative
ramification index one. -/
theorem isInertiaNeighborhood_iff_relativeRamificationIndex_eq_one
    (G : LocalGaloisGroup.{u})
    (reciprocity : LocalReciprocityFamily.{u})
    (U : OpenSubgroup G.toProfiniteGrp) :
    IntrinsicRamification.IsInertiaNeighborhood G.toProfiniteGrp
        G.presentation.residueChar U ↔
      U.toSubgroup.Normal ∧
        (G.fixedFieldBaseExtension (OrderDual.toDual U)).relativeRamificationIndex = 1 := by
  let V : G.OpenSubgroupIndex := OrderDual.toDual U
  let E := G.fixedFieldBaseExtension V
  rw [IntrinsicRamification.IsInertiaNeighborhood,
    G.openSubgroupIntrinsicRamificationIndex_eq_fixedField reciprocity U,
    G.intrinsicRamificationIndex_eq_absoluteRamificationIndex reciprocity]
  constructor
  · rintro ⟨hN, he⟩
    refine ⟨hN, ?_⟩
    have htower := E.absoluteRamificationIndex_eq_mul
    have hmul : absoluteRamificationIndex G.presentation *
        E.relativeRamificationIndex = absoluteRamificationIndex G.presentation * 1 := by
      rw [← htower, mul_one, he]
    exact Nat.mul_left_cancel (absoluteRamificationIndex_pos G.presentation) hmul
  · rintro ⟨hN, hrel⟩
    refine ⟨hN, ?_⟩
    rw [E.absoluteRamificationIndex_eq_mul, hrel, mul_one]

/-- Prime-to-`p` intrinsic neighborhoods are precisely normal fixed fields whose relative
ramification index is prime to `p`. -/
theorem isWildInertiaNeighborhood_iff_relativeRamificationIndex_coprime
    (G : LocalGaloisGroup.{u})
    (reciprocity : LocalReciprocityFamily.{u})
    (U : OpenSubgroup G.toProfiniteGrp) :
    IntrinsicRamification.IsWildInertiaNeighborhood G.toProfiniteGrp
        G.presentation.residueChar U ↔
      U.toSubgroup.Normal ∧
        Nat.Coprime
          (G.fixedFieldBaseExtension
            (OrderDual.toDual U)).relativeRamificationIndex
          G.presentation.residueChar := by
  let V : G.OpenSubgroupIndex := OrderDual.toDual U
  let E := G.fixedFieldBaseExtension V
  rw [IntrinsicRamification.IsWildInertiaNeighborhood,
    G.openSubgroupIntrinsicRamificationIndex_eq_fixedField reciprocity U,
    G.intrinsicRamificationIndex_eq_absoluteRamificationIndex reciprocity]
  constructor
  · rintro ⟨hN, q, hq, hcop, he⟩
    refine ⟨hN, ?_⟩
    have htower := E.absoluteRamificationIndex_eq_mul
    have hmul : absoluteRamificationIndex G.presentation *
        E.relativeRamificationIndex =
          absoluteRamificationIndex G.presentation * q := by
      rw [← htower, he]
    have hrel := Nat.mul_left_cancel
      (absoluteRamificationIndex_pos G.presentation) hmul
    rwa [hrel]
  · rintro ⟨hN, hcop⟩
    refine ⟨hN, E.relativeRamificationIndex,
      E.relativeRamificationIndex_pos, hcop, ?_⟩
    exact E.absoluteRamificationIndex_eq_mul

end Anabelian.OTriangle.LocalGaloisGroup
