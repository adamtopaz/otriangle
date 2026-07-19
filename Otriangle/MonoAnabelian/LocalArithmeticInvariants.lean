import Otriangle.MonoAnabelian.DeepUnits
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Elementary arithmetic invariants of a mixed-characteristic local field

For a pointed mixed-characteristic local field `K`, its valuation ring is a discrete valuation
ring.  This file defines the residue degree `f(K)` and the absolute ramification index `e(K)`
directly from that DVR.  The defining factorization

`p 𝒪_K = 𝔪_K ^ e(K)`

then computes the cardinality of `𝒪_K / p 𝒪_K` as `p ^ (e(K) * f(K))`.  These are the arithmetic
integers which Hoshi recovers from the abelianized absolute Galois group in Definition 3.5.
-/

noncomputable section

namespace Anabelian.LCFT

open OTriangle ValuativeRel

universe u

/-- The valuation ring of a pointed local field. -/
abbrev LocalIntegerRing (K : PointedMixedCharLocalField.{u}) : Type u :=
  (valuation K).integer

/-- The maximal ideal of the valuation ring. -/
abbrev localMaximalIdeal (K : PointedMixedCharLocalField.{u}) :
    Ideal (LocalIntegerRing K) :=
  IsLocalRing.maximalIdeal (LocalIntegerRing K)

/-- The residue characteristic, regarded as an element of the valuation ring. -/
def residueCharInteger (K : PointedMixedCharLocalField.{u}) : LocalIntegerRing K :=
  ⟨(K.residueChar : K), valuation_natCast_le_one (valuation K) K.residueChar⟩

/-- The principal ideal `p O_K`. -/
def residueCharIdeal (K : PointedMixedCharLocalField.{u}) :
    Ideal (LocalIntegerRing K) :=
  Ideal.span {residueCharInteger K}

theorem residueCharInteger_ne_zero (K : PointedMixedCharLocalField.{u}) :
    residueCharInteger K ≠ 0 := by
  intro h
  have hcast := congrArg Subtype.val h
  change (K.residueChar : K) = 0 at hcast
  have hp : (K.residueChar : K) ≠ 0 := by
    exact_mod_cast (Fact.out : K.residueChar.Prime).ne_zero
  exact hp hcast

theorem residueCharIdeal_ne_bot (K : PointedMixedCharLocalField.{u}) :
    residueCharIdeal K ≠ ⊥ := by
  intro h
  apply residueCharInteger_ne_zero K
  exact Ideal.span_singleton_eq_bot.mp h

/-- A fixed irreducible element of the valuation ring.  Its principal ideal is the maximal
ideal, so it is a uniformizer in the DVR sense. -/
def localUniformizerInteger (K : PointedMixedCharLocalField.{u}) : LocalIntegerRing K :=
  (IsDiscreteValuationRing.exists_irreducible (LocalIntegerRing K)).choose

theorem localUniformizerInteger_irreducible (K : PointedMixedCharLocalField.{u}) :
    Irreducible (localUniformizerInteger K) :=
  (IsDiscreteValuationRing.exists_irreducible (LocalIntegerRing K)).choose_spec

private theorem exists_residueCharIdeal_eq_uniformizer_pow
    (K : PointedMixedCharLocalField.{u}) :
    ∃ n : ℕ, residueCharIdeal K = Ideal.span {(localUniformizerInteger K) ^ n} :=
  IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (residueCharIdeal_ne_bot K) (localUniformizerInteger_irreducible K)

/-- The absolute ramification index: the exponent of the maximal ideal in `p O_K`. -/
def absoluteRamificationIndex (K : PointedMixedCharLocalField.{u}) : ℕ :=
  Nat.find (exists_residueCharIdeal_eq_uniformizer_pow K)

theorem residueCharIdeal_eq_span_uniformizer_pow
    (K : PointedMixedCharLocalField.{u}) :
    residueCharIdeal K =
      Ideal.span {(localUniformizerInteger K) ^ absoluteRamificationIndex K} :=
  Nat.find_spec (exists_residueCharIdeal_eq_uniformizer_pow K)

theorem localMaximalIdeal_eq_span_uniformizer
    (K : PointedMixedCharLocalField.{u}) :
    localMaximalIdeal K = Ideal.span {localUniformizerInteger K} :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer
    (localUniformizerInteger K)).mp (localUniformizerInteger_irreducible K)

/-- The defining ideal factorization `p O_K = m_K ^ e(K)`. -/
theorem residueCharIdeal_eq_maximalIdeal_pow
    (K : PointedMixedCharLocalField.{u}) :
    residueCharIdeal K = localMaximalIdeal K ^ absoluteRamificationIndex K := by
  rw [residueCharIdeal_eq_span_uniformizer_pow,
    localMaximalIdeal_eq_span_uniformizer]
  exact (Ideal.span_singleton_pow (localUniformizerInteger K)
    (absoluteRamificationIndex K)).symm

theorem absoluteRamificationIndex_pos (K : PointedMixedCharLocalField.{u}) :
    0 < absoluteRamificationIndex K := by
  apply Nat.pos_of_ne_zero
  intro he
  have htop : residueCharIdeal K = ⊤ := by
    rw [residueCharIdeal_eq_maximalIdeal_pow, he, pow_zero,
      Ideal.one_eq_top]
  have hunit : IsUnit (residueCharInteger K) := by
    rw [← Ideal.span_singleton_eq_top]
    exact htop
  have hval : valuation K (K.residueChar : K) = 1 :=
    (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation K))).mp hunit
  exact (residueChar_cast_valuation_lt_one K).ne hval

/-- The residue degree over the prime field. -/
abbrev LocalResidueField (K : PointedMixedCharLocalField.{u}) : Type u :=
  IsLocalRing.ResidueField (LocalIntegerRing K)

noncomputable instance localResidueFieldAlgebra
    (K : PointedMixedCharLocalField.{u}) :
    Algebra (ZMod K.residueChar) (LocalResidueField K) :=
  ZMod.algebra _ _

/-- The residue degree over the prime field. -/
def localResidueDegree (K : PointedMixedCharLocalField.{u}) : ℕ :=
  Module.finrank (ZMod K.residueChar) (LocalResidueField K)

/-- The residue-field cardinality is `p ^ f(K)`. -/
theorem residueField_card_eq_residueChar_pow_residueDegree
    (K : PointedMixedCharLocalField.{u}) :
    Nat.card (LocalResidueField K) =
      K.residueChar ^ localResidueDegree K := by
  exact (FiniteField.pow_finrank_eq_natCard K.residueChar
    (LocalResidueField K)).symm

theorem localResidueDegree_pos (K : PointedMixedCharLocalField.{u}) :
    0 < localResidueDegree K := by
  exact Module.finrank_pos

/-- The quotient of the valuation ring by `p` has `p ^ (e f)` elements. -/
theorem residueCharIdeal_quotient_card
    (K : PointedMixedCharLocalField.{u}) :
    Nat.card (LocalIntegerRing K ⧸ residueCharIdeal K) =
      K.residueChar ^
        (absoluteRamificationIndex K * localResidueDegree K) := by
  rw [residueCharIdeal_eq_maximalIdeal_pow]
  change Submodule.cardQuot
      (localMaximalIdeal K ^ absoluteRamificationIndex K) = _
  rw [cardQuot_pow_of_prime
    (P := localMaximalIdeal K)
    (IsDiscreteValuationRing.not_a_field (LocalIntegerRing K))]
  change Nat.card (LocalResidueField K) ^ absoluteRamificationIndex K = _
  rw [residueField_card_eq_residueChar_pow_residueDegree, ← pow_mul]
  rw [Nat.mul_comm]

end Anabelian.LCFT
