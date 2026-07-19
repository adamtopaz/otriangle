import Otriangle.MonoAnabelian.TameKummerExtension
import Otriangle.MonoAnabelian.FiniteGaloisRamification

/-!
# Ramification of the explicit Kummer extensions

The fixed-field presentation of the splitting field of `X ^ n - π` has relative ramification
index `n`.  The lower bound comes directly from the equation `α ^ n = π`; the upper bound is
the finite inertia-cardinality theorem together with the degree computation.
-/

noncomputable section

namespace Anabelian
namespace LCFT

open OTriangle ValuativeRel Polynomial

universe u

/-- The normal open subgroup fixing the embedded tame Kummer field. -/
noncomputable def tameKummerOpenSubgroup
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) (hn : 0 < n) :
    OpenSubgroup (OTriangle.LocalGaloisGroup.mk K).toProfiniteGrp := by
  let L := tameKummerFiniteGaloisIntermediateField K n hn
  exact ⟨L.toIntermediateField.fixingSubgroup,
    L.toIntermediateField.fixingSubgroup_isOpen⟩

theorem tameKummerOpenSubgroup_normal
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) (hn : 0 < n) :
    (tameKummerOpenSubgroup K n hn).toSubgroup.Normal := by
  let L := tameKummerFiniteGaloisIntermediateField K n hn
  change L.toIntermediateField.fixingSubgroup.Normal
  infer_instance

theorem tameKummer_fixedField_eq
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) (hn : 0 < n) :
    let G := OTriangle.LocalGaloisGroup.mk K
    G.fixedField (OrderDual.toDual (tameKummerOpenSubgroup K n hn)) =
      tameKummerIntermediateField K n := by
  let G := OTriangle.LocalGaloisGroup.mk K
  let L := tameKummerFiniteGaloisIntermediateField K n hn
  change IntermediateField.fixedField L.toIntermediateField.fixingSubgroup =
    tameKummerIntermediateField K n
  rw [InfiniteGalois.fixedField_fixingSubgroup]
  rfl

/-- The explicit Kummer fixed field is totally ramified of degree `n`. -/
theorem tameKummer_relativeRamificationIndex_eq
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) (hn : 0 < n)
    (hroot : (primitiveRoots n K).Nonempty) :
    let G := OTriangle.LocalGaloisGroup.mk K
    let U := tameKummerOpenSubgroup K n hn
    (G.fixedFieldBaseExtension (OrderDual.toDual U)).relativeRamificationIndex = n := by
  let G := OTriangle.LocalGaloisGroup.mk K
  let U := tameKummerOpenSubgroup K n hn
  let V : G.OpenSubgroupIndex := OrderDual.toDual U
  let L := G.fixedFieldPointed V
  let E := G.fixedFieldBaseExtension V
  letI : NeZero n := ⟨hn.ne'⟩
  letI := G.presentation.nontriviallyNormedField
  letI := G.presentation.isUltrametricDist
  letI := G.presentation.completeSpace
  letI := G.fixedFieldNontriviallyNormedField V
  letI := G.fixedFieldIsUltrametricDist V
  letI : ValuativeRel L := G.fixedFieldValuativeRel V
  letI : TopologicalSpace L := G.fixedFieldTopologicalSpace V
  letI : IsNonarchimedeanLocalField L := G.fixedFieldIsNonarchimedeanLocalField V
  letI : Algebra K L := E.algebra
  letI : ValuativeExtension K L := E.valuativeExtension
  letI : FiniteDimensional K L := E.finiteDimensional
  letI : Algebra.IsAlgebraic K L := by infer_instance
  letI : IsGalois K (G.fixedField V) := G.fixedField_isGalois_of_normal U
    (tameKummerOpenSubgroup_normal K n hn)
  letI : IsScalarTower G.presentation G.presentation (G.fixedField V) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : MulSemiringAction
      ((G.fixedField V) ≃ₐ[G.presentation] (G.fixedField V))
        𝒪[G.fixedField V] :=
    SpectralLocalField.integerMulSemiringAction
      G.presentation G.presentation (G.fixedField V)
  let hfield : G.fixedField V = tameKummerIntermediateField K n :=
    tameKummer_fixedField_eq K n hn
  have hfinrank : Module.finrank K L = n := by
    change Module.finrank K (G.fixedField V) = n
    rw [hfield]
    exact tameKummerIntermediateField_finrank K n hn hroot
  let alpha : L := ⟨(tameKummerRoot K n : K.algebraicClosure), by
    rw [hfield]
    exact (tameKummerRoot K n).property⟩
  have halpha_pow : alpha ^ n =
      algebraMap K L (localUniformizerInteger K : K) := by
    apply Subtype.ext
    change (tameKummerRoot K n : K.algebraicClosure) ^ n =
      algebraMap K K.algebraicClosure (localUniformizerInteger K : K)
    exact congrArg Subtype.val (tameKummerRoot_pow K n)
  have halpha_integral : IsIntegral (LocalIntegerRing K) alpha := by
    let f : (LocalIntegerRing K)[X] :=
      X ^ n - C (localUniformizerInteger K)
    refine ⟨f, monic_X_pow_sub_C _ hn.ne', ?_⟩
    change Polynomial.aeval alpha f = 0
    rw [aeval_def, eval₂_sub, eval₂_X_pow, eval₂_C]
    change alpha ^ n - algebraMap (LocalIntegerRing K) L
      (localUniformizerInteger K) = 0
    rw [halpha_pow]
    apply sub_eq_zero.mpr
    rfl
  let alphaO : LocalIntegerRing L :=
    ⟨alpha, Valuation.Integers.mem_of_integral
      (Valuation.integer.integers (valuation L)) halpha_integral.tower_top⟩
  have halphaO_pow : alphaO ^ n =
      algebraMap (LocalIntegerRing K) (LocalIntegerRing L)
        (localUniformizerInteger K) := by
    apply Subtype.ext
    exact halpha_pow
  have hpi_base : localUniformizerInteger K ∈ localMaximalIdeal K := by
    rw [localMaximalIdeal_eq_span_uniformizer]
    exact Ideal.mem_span_singleton.mpr (dvd_refl _)
  have hpi_mem : algebraMap (LocalIntegerRing K) (LocalIntegerRing L)
      (localUniformizerInteger K) ∈ localMaximalIdeal L := by
    exact IsLocalRing.map_maximalIdeal_le
      (algebraMap (LocalIntegerRing K) (LocalIntegerRing L))
      (Ideal.mem_map_of_mem _ hpi_base)
  have halpha_mem : alphaO ∈ localMaximalIdeal L := by
    have hpow : alphaO ^ n ∈ localMaximalIdeal L := by
      rw [halphaO_pow]
      exact hpi_mem
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance n hpow
  have hmap_le : (localMaximalIdeal K).map
      (algebraMap (LocalIntegerRing K) (LocalIntegerRing L)) ≤
        localMaximalIdeal L ^ n := by
    rw [localMaximalIdeal_eq_span_uniformizer, Ideal.map_span,
      Set.image_singleton, ← halphaO_pow, ← Ideal.span_singleton_pow]
    exact Ideal.pow_right_mono
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr halpha_mem)) n
  have hlower : n ≤ E.relativeRamificationIndex := by
    have hpow_le : localMaximalIdeal L ^ E.relativeRamificationIndex ≤
        localMaximalIdeal L ^ n := by
      rw [← E.map_localMaximalIdeal_eq_pow]
      exact hmap_le
    have hc := Order.coheight_anti hpow_le
    simpa only [IsDiscreteValuationRing.coheight_pow_maximalIdeal,
      ENat.coe_le_coe] using hc
  have hupper : E.relativeRamificationIndex ≤ n := by
    calc
      E.relativeRamificationIndex = Nat.card
          ((IsLocalRing.maximalIdeal 𝒪[G.fixedField V]).inertia
            ((G.fixedField V) ≃ₐ[G.presentation] (G.fixedField V))) := by
        symm
        exact G.fixedFieldFiniteInertia_card U
          (tameKummerOpenSubgroup_normal K n hn)
      _ ≤ Nat.card
          ((G.fixedField V) ≃ₐ[G.presentation] (G.fixedField V)) :=
        Nat.card_le_card_of_injective (fun x => x.1) Subtype.val_injective
      _ = Module.finrank K (G.fixedField V) :=
        IsGalois.card_aut_eq_finrank G.presentation (G.fixedField V)
      _ = n := hfinrank
  exact Nat.le_antisymm hupper hlower

end LCFT
end Anabelian
