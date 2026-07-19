import Otriangle.MonoAnabelian.LocalArithmeticInvariants
import Otriangle.LCFT
import Mathlib.NumberTheory.RamificationInertia.Ramification

/-!
# Ramification indices in finite local extensions

For a finite valued extension `L/K`, the extension ramification index is the exponent with which
the maximal ideal of `K` extends to the maximal ideal of `L`.  This file constructs that exponent
directly in the two discrete valuation rings and proves the tower formula
`e(L) = e(K) * e(L/K)` for the absolute ramification indices used in the reconstruction.
-/

noncomputable section

namespace Anabelian.LCFT

open OTriangle ValuativeRel

universe u

theorem localMaximalIdeal_ne_bot (K : PointedMixedCharLocalField.{u}) :
    localMaximalIdeal K ≠ ⊥ := by
  rw [localMaximalIdeal_eq_span_uniformizer]
  intro h
  exact (localUniformizerInteger_irreducible K).ne_zero
    (Ideal.span_singleton_eq_bot.mp h)

private theorem mappedLocalMaximalIdeal_ne_bot
    {K L : PointedMixedCharLocalField.{u}} (E : FiniteExtension K L) :
    letI := E.algebra
    letI := E.valuativeExtension
    (localMaximalIdeal K).map
        (algebraMap (LocalIntegerRing K) (LocalIntegerRing L)) ≠ ⊥ := by
  letI := E.algebra
  letI := E.valuativeExtension
  intro h
  apply localMaximalIdeal_ne_bot K
  exact (Ideal.map_eq_bot_iff_of_injective
    (Valuation.HasExtension.algebraMap_injective
      (vK := valuation K) (vA := valuation L))).mp h

private theorem exists_mappedLocalMaximalIdeal_eq_maximalIdeal_pow
    {K L : PointedMixedCharLocalField.{u}} (E : FiniteExtension K L) :
    letI := E.algebra
    letI := E.valuativeExtension
    ∃ n : ℕ,
      (localMaximalIdeal K).map
          (algebraMap (LocalIntegerRing K) (LocalIntegerRing L)) =
        localMaximalIdeal L ^ n := by
  letI := E.algebra
  letI := E.valuativeExtension
  obtain ⟨n, hn⟩ :=
    IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
      (mappedLocalMaximalIdeal_ne_bot E)
      (localUniformizerInteger_irreducible L)
  refine ⟨n, hn.trans ?_⟩
  rw [localMaximalIdeal_eq_span_uniformizer]
  exact (Ideal.span_singleton_pow (localUniformizerInteger L) n).symm

/-- The relative ramification index of a finite valued extension. -/
noncomputable def FiniteExtension.relativeRamificationIndex
    {K L : PointedMixedCharLocalField.{u}} (E : FiniteExtension K L) : ℕ := by
  letI := E.algebra
  letI := E.valuativeExtension
  exact Nat.find (exists_mappedLocalMaximalIdeal_eq_maximalIdeal_pow E)

/-- The defining maximal-ideal factorization for the relative ramification index. -/
theorem FiniteExtension.map_localMaximalIdeal_eq_pow
    {K L : PointedMixedCharLocalField.{u}} (E : FiniteExtension K L) :
    letI := E.algebra
    letI := E.valuativeExtension
    (localMaximalIdeal K).map
        (algebraMap (LocalIntegerRing K) (LocalIntegerRing L)) =
      localMaximalIdeal L ^ E.relativeRamificationIndex := by
  letI := E.algebra
  letI := E.valuativeExtension
  exact Nat.find_spec (exists_mappedLocalMaximalIdeal_eq_maximalIdeal_pow E)

/-- Relative ramification indices are positive. -/
theorem FiniteExtension.relativeRamificationIndex_pos
    {K L : PointedMixedCharLocalField.{u}} (E : FiniteExtension K L) :
    0 < E.relativeRamificationIndex := by
  letI := E.algebra
  letI := E.valuativeExtension
  apply Nat.pos_of_ne_zero
  intro hzero
  have hmap := E.map_localMaximalIdeal_eq_pow
  rw [hzero, pow_zero, Ideal.one_eq_top] at hmap
  exact (IsLocalRing.map_maximalIdeal_lt_top
    (algebraMap (LocalIntegerRing K) (LocalIntegerRing L))).ne hmap

/-- Distinct powers of the maximal ideal in a DVR are distinct. -/
theorem localMaximalIdeal_pow_injective (K : PointedMixedCharLocalField.{u}) :
    Function.Injective (localMaximalIdeal K ^ ·) := by
  intro m n h
  have hc := congrArg Order.coheight h
  simp only [IsDiscreteValuationRing.coheight_pow_maximalIdeal] at hc
  exact ENat.coe_inj.mp hc

/-- A finite valued extension has relative ramification index one exactly when the base maximal
ideal extends to the upstairs maximal ideal. -/
theorem FiniteExtension.relativeRamificationIndex_eq_one_iff
    {K L : PointedMixedCharLocalField.{u}} (E : FiniteExtension K L) :
    E.relativeRamificationIndex = 1 ↔
      letI := E.algebra
      letI := E.valuativeExtension
      (localMaximalIdeal K).map
          (algebraMap (LocalIntegerRing K) (LocalIntegerRing L)) =
        localMaximalIdeal L := by
  letI := E.algebra
  letI := E.valuativeExtension
  constructor
  · intro h
    rw [E.map_localMaximalIdeal_eq_pow, h, pow_one]
  · intro h
    apply localMaximalIdeal_pow_injective L
    change localMaximalIdeal L ^ E.relativeRamificationIndex =
      localMaximalIdeal L ^ 1
    rw [← E.map_localMaximalIdeal_eq_pow, h, pow_one]

/-- A finite valued extension has the same residue characteristic as its base field. -/
theorem FiniteExtension.residueChar_eq
    {K L : PointedMixedCharLocalField.{u}} (E : FiniteExtension K L) :
    K.residueChar = L.residueChar := by
  letI := E.algebra
  letI := E.valuativeExtension
  let hpK : CharP (LocalResidueField L) K.residueChar :=
    charP_of_injective_algebraMap
      (algebraMap (LocalResidueField K) (LocalResidueField L)).injective
      K.residueChar
  exact CharP.eq (R := LocalResidueField L) hpK L.residueFieldCharP

/-- Extending the ideal generated by the residue characteristic gives the corresponding ideal
upstairs. -/
theorem FiniteExtension.map_residueCharIdeal
    {K L : PointedMixedCharLocalField.{u}} (E : FiniteExtension K L) :
    letI := E.algebra
    letI := E.valuativeExtension
    (residueCharIdeal K).map
        (algebraMap (LocalIntegerRing K) (LocalIntegerRing L)) =
      residueCharIdeal L := by
  letI := E.algebra
  letI := E.valuativeExtension
  have hgen : algebraMap (LocalIntegerRing K) (LocalIntegerRing L)
      (residueCharInteger K) = residueCharInteger L := by
    apply Subtype.ext
    change algebraMap K L (K.residueChar : K) = (L.residueChar : L)
    rw [map_natCast, E.residueChar_eq]
  rw [residueCharIdeal, residueCharIdeal, Ideal.map_span]
  rw [Set.image_singleton, hgen]

/-- Absolute and relative ramification indices satisfy `e(L) = e(K) e(L/K)`. -/
theorem FiniteExtension.absoluteRamificationIndex_eq_mul
    {K L : PointedMixedCharLocalField.{u}} (E : FiniteExtension K L) :
    absoluteRamificationIndex L =
      absoluteRamificationIndex K * E.relativeRamificationIndex := by
  letI := E.algebra
  letI := E.valuativeExtension
  apply localMaximalIdeal_pow_injective L
  calc
    localMaximalIdeal L ^ absoluteRamificationIndex L =
        residueCharIdeal L :=
      (residueCharIdeal_eq_maximalIdeal_pow L).symm
    _ = (residueCharIdeal K).map
          (algebraMap (LocalIntegerRing K) (LocalIntegerRing L)) :=
      E.map_residueCharIdeal.symm
    _ = (localMaximalIdeal K ^ absoluteRamificationIndex K).map
          (algebraMap (LocalIntegerRing K) (LocalIntegerRing L)) := by
      rw [← residueCharIdeal_eq_maximalIdeal_pow K]
    _ = ((localMaximalIdeal K).map
          (algebraMap (LocalIntegerRing K) (LocalIntegerRing L))) ^
            absoluteRamificationIndex K :=
      Ideal.map_pow _ _ _
    _ = (localMaximalIdeal L ^ E.relativeRamificationIndex) ^
          absoluteRamificationIndex K := by
      rw [E.map_localMaximalIdeal_eq_pow]
    _ = localMaximalIdeal L ^
          (absoluteRamificationIndex K * E.relativeRamificationIndex) := by
      calc
        (localMaximalIdeal L ^ E.relativeRamificationIndex) ^
            absoluteRamificationIndex K =
          localMaximalIdeal L ^
            (E.relativeRamificationIndex * absoluteRamificationIndex K) :=
          (pow_mul _ _ _).symm
        _ = _ := by rw [Nat.mul_comm]

end Anabelian.LCFT
