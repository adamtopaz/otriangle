import Otriangle.MonoAnabelian.LocalExtensionRamification
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Explicit tame Kummer extensions

For every positive integer `n`, the polynomial obtained by adjoining an `n`th root of a local
uniformizer is Eisenstein.  When the base field contains the `n`th roots of unity, its splitting
field is the standard cyclic degree-`n` tame extension.  This is the explicit finite-level input
used to prove faithfulness of the unramified action on tame inertia.
-/

noncomputable section

namespace Anabelian.LCFT

open OTriangle ValuativeRel Polynomial

universe u

/-- `X ^ n - π` is Eisenstein, hence irreducible, for every positive `n` and every local
uniformizer `π`. -/
theorem localUniformizer_X_pow_sub_C_irreducible
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) (hn : 0 < n) :
    Irreducible (X ^ n - C (localUniformizerInteger K : K) : K[X]) := by
  let R := LocalIntegerRing K
  let m : Ideal R := localMaximalIdeal K
  let pi : R := localUniformizerInteger K
  let f : R[X] := X ^ n - C pi
  have hfmonic : f.Monic := monic_X_pow_sub_C pi hn.ne'
  have hmne : m ≠ ⊤ := Ideal.IsPrime.ne_top'
  have hfmem : ∀ {i}, i < f.natDegree → f.coeff i ∈ m := by
    intro i hi
    have hi' : i < n := by
      change i < (X ^ n - C pi).natDegree at hi
      rwa [natDegree_X_pow_sub_C] at hi
    by_cases hi0 : i = 0
    · subst i
      have : pi ∈ m := by
        dsimp only [m]
        rw [localMaximalIdeal_eq_span_uniformizer]
        exact Ideal.mem_span_singleton.mpr (dvd_refl pi)
      have hcoeff : f.coeff 0 = -pi := by
        dsimp only [f]
        rw [coeff_sub, coeff_X_pow, if_neg (Nat.ne_of_gt hn).symm, coeff_C_zero,
          zero_sub]
      rw [hcoeff]
      exact m.neg_mem this
    · have hin : i ≠ n := ne_of_lt hi'
      have hcoeff : f.coeff i = 0 := by
        dsimp only [f]
        rw [coeff_sub, coeff_X_pow, if_neg hin, coeff_C, if_neg hi0, sub_zero]
      rw [hcoeff]
      exact m.zero_mem
  have hpi_not : -pi ∉ m ^ 2 := by
    intro hpi
    have hle : m ≤ m ^ 2 := by
      dsimp only [m, pi] at hpi ⊢
      rw [localMaximalIdeal_eq_span_uniformizer]
      intro x hx
      rw [Ideal.mem_span_singleton] at hx
      obtain ⟨a, rfl⟩ := hx
      have hpipos := (localMaximalIdeal K ^ 2).neg_mem hpi
      rw [neg_neg] at hpipos
      rw [localMaximalIdeal_eq_span_uniformizer] at hpipos
      exact (Ideal.span {localUniformizerInteger K} ^ 2).mul_mem_right a hpipos
    have heq : m ^ 1 = m ^ 2 := by
      rw [pow_one]
      exact le_antisymm hle (by
        simpa only [pow_one] using
          (Ideal.pow_le_pow_right (I := m) (show 1 ≤ 2 by omega)))
    have := localMaximalIdeal_pow_injective K heq
    omega
  have hcoeff0 : f.coeff 0 = -pi := by
    dsimp only [f]
    rw [coeff_sub, coeff_X_pow, if_neg (Nat.ne_of_gt hn).symm, coeff_C_zero, zero_sub]
  have hfeis : f.IsEisensteinAt m :=
    hfmonic.isEisensteinAt_of_mem_of_notMem hmne hfmem (by
      rw [hcoeff0]
      exact hpi_not)
  have hfirr : Irreducible f := hfeis.irreducible inferInstance hfmonic.isPrimitive (by
    change 0 < (X ^ n - C pi).natDegree
    rwa [natDegree_X_pow_sub_C])
  have hcoe : algebraMap R K pi = (pi : K) := by rfl
  have hmap : f.map (algebraMap R K) =
      (X ^ n - C (pi : K) : K[X]) := by
    dsimp only [f]
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C, hcoe]
  rw [← hmap]
  exact hfmonic.irreducible_iff_irreducible_map_fraction_map.mp hfirr

/-- The splitting field of `X ^ n - π`, embedded in the chosen algebraic closure. -/
noncomputable def tameKummerIntermediateField
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) :
    IntermediateField K K.algebraicClosure := by
  let p : K[X] := X ^ n - C (localUniformizerInteger K : K)
  letI : IsAlgClosed K.algebraicClosure := IsAlgClosure.isAlgClosed K
  let i : p.SplittingField →ₐ[K] K.algebraicClosure := IsAlgClosed.lift
  exact i.fieldRange

/-- The embedded Kummer splitting field is finite Galois for positive `n`. -/
noncomputable def tameKummerFiniteGaloisIntermediateField
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) (hn : 0 < n) :
    FiniteGaloisIntermediateField K K.algebraicClosure := by
  let p : K[X] := X ^ n - C (localUniformizerInteger K : K)
  letI : IsAlgClosed K.algebraicClosure := IsAlgClosure.isAlgClosed K
  let i : p.SplittingField →ₐ[K] K.algebraicClosure := IsAlgClosed.lift
  let L : IntermediateField K K.algebraicClosure := i.fieldRange
  have hpi : (localUniformizerInteger K : K) ≠ 0 := by
    exact_mod_cast (localUniformizerInteger_irreducible K).ne_zero
  have hncast : (n : K) ≠ 0 := by exact_mod_cast hn.ne'
  letI : IsGalois K p.SplittingField :=
    IsGalois.of_separable_splitting_field
      (Polynomial.separable_X_pow_sub_C _ hncast hpi)
  letI : FiniteDimensional K L := Module.Finite.equiv i.equivFieldRange.toLinearEquiv
  letI : IsGalois K L := IsGalois.of_algEquiv i.equivFieldRange
  exact { toIntermediateField := L }

/-- If the base contains a primitive `n`th root of unity, the embedded tame Kummer field has
degree exactly `n`. -/
theorem tameKummerIntermediateField_finrank
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) (hn : 0 < n)
    (hroot : (primitiveRoots n K).Nonempty) :
    Module.finrank K (tameKummerIntermediateField K n) = n := by
  let p : K[X] := X ^ n - C (localUniformizerInteger K : K)
  letI : IsAlgClosed K.algebraicClosure := IsAlgClosure.isAlgClosed K
  let i : p.SplittingField →ₐ[K] K.algebraicClosure := IsAlgClosed.lift
  change Module.finrank K i.fieldRange = n
  rw [← i.equivFieldRange.toLinearEquiv.finrank_eq]
  exact finrank_of_isSplittingField_X_pow_sub_C hroot
    (localUniformizer_X_pow_sub_C_irreducible K n hn) p.SplittingField

/-- The distinguished `n`th root of the base uniformizer in the embedded splitting field. -/
noncomputable def tameKummerRoot
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) [NeZero n] :
    tameKummerIntermediateField K n := by
  let p : K[X] := X ^ n - C (localUniformizerInteger K : K)
  letI : IsAlgClosed K.algebraicClosure := IsAlgClosure.isAlgClosed K
  let i : p.SplittingField →ₐ[K] K.algebraicClosure := IsAlgClosed.lift
  let a : p.SplittingField :=
    rootOfSplitsXPowSubC (NeZero.pos n) (localUniformizerInteger K : K)
      p.SplittingField
  exact ⟨i a, ⟨a, rfl⟩⟩

theorem tameKummerRoot_pow
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) [NeZero n] :
    (tameKummerRoot K n) ^ n =
      algebraMap K (tameKummerIntermediateField K n)
        (localUniformizerInteger K : K) := by
  apply Subtype.ext
  let p : K[X] := X ^ n - C (localUniformizerInteger K : K)
  letI : IsAlgClosed K.algebraicClosure := IsAlgClosure.isAlgClosed K
  let i : p.SplittingField →ₐ[K] K.algebraicClosure := IsAlgClosed.lift
  change i (rootOfSplitsXPowSubC (NeZero.pos n)
      (localUniformizerInteger K : K) p.SplittingField) ^ n =
    algebraMap K K.algebraicClosure (localUniformizerInteger K : K)
  rw [← map_pow, rootOfSplitsXPowSubC_pow]
  exact i.commutes _

/-- The Kummer root is integral over the base valuation ring. -/
theorem tameKummerRoot_isIntegral
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) [NeZero n] :
    IsIntegral (LocalIntegerRing K) (tameKummerRoot K n) := by
  let f : (LocalIntegerRing K)[X] :=
    X ^ n - C (localUniformizerInteger K)
  refine ⟨f, monic_X_pow_sub_C _ (NeZero.ne n), ?_⟩
  change Polynomial.aeval (tameKummerRoot K n) f = 0
  rw [aeval_def, eval₂_sub, eval₂_X_pow, eval₂_C]
  change (tameKummerRoot K n) ^ n -
      algebraMap (LocalIntegerRing K) (tameKummerIntermediateField K n)
        (localUniformizerInteger K) = 0
  rw [tameKummerRoot_pow]
  apply sub_eq_zero.mpr
  rfl

/-- The generator of the cyclic Kummer Galois group determined by a chosen primitive root. -/
noncomputable def tameKummerGeneratorAutomorphism
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) (hn : 0 < n)
    (hroot : (primitiveRoots n K).Nonempty) :
    tameKummerIntermediateField K n ≃ₐ[K] tameKummerIntermediateField K n := by
  letI : NeZero n := ⟨hn.ne'⟩
  let p : K[X] := X ^ n - C (localUniformizerInteger K : K)
  letI : IsAlgClosed K.algebraicClosure := IsAlgClosure.isAlgClosed K
  let i : p.SplittingField →ₐ[K] K.algebraicClosure := IsAlgClosed.lift
  have hprimitive : IsPrimitiveRoot hroot.choose n :=
    (mem_primitiveRoots hn).mp hroot.choose_spec
  exact (AlgEquiv.autCongr i.equivFieldRange)
    ((autEquivZmod (localUniformizer_X_pow_sub_C_irreducible K n hn)
      p.SplittingField hprimitive).symm
        (Multiplicative.ofAdd (1 : ZMod n)))

/-- The chosen Kummer generator sends the distinguished root to `ζ · α`. -/
theorem tameKummerGeneratorAutomorphism_apply_root
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) [NeZero n] (hn : 0 < n)
    (hroot : (primitiveRoots n K).Nonempty) :
    tameKummerGeneratorAutomorphism K n hn hroot (tameKummerRoot K n) =
      algebraMap K (tameKummerIntermediateField K n) hroot.choose *
        tameKummerRoot K n := by
  let p : K[X] := X ^ n - C (localUniformizerInteger K : K)
  letI : IsAlgClosed K.algebraicClosure := IsAlgClosure.isAlgClosed K
  let i : p.SplittingField →ₐ[K] K.algebraicClosure := IsAlgClosed.lift
  have hprimitive : IsPrimitiveRoot hroot.choose n :=
    (mem_primitiveRoots hn).mp hroot.choose_spec
  dsimp only [tameKummerGeneratorAutomorphism, tameKummerRoot,
    tameKummerIntermediateField]
  change (AlgEquiv.autCongr i.equivFieldRange
      ((autEquivZmod
      (localUniformizer_X_pow_sub_C_irreducible K n hn)
      p.SplittingField hprimitive).symm
        (Multiplicative.ofAdd (1 : ZMod n))))
      (i.equivFieldRange
        (rootOfSplitsXPowSubC (NeZero.pos n) (localUniformizerInteger K : K)
          p.SplittingField)) =
    algebraMap K i.fieldRange hroot.choose *
      i.equivFieldRange
        (rootOfSplitsXPowSubC (NeZero.pos n) (localUniformizerInteger K : K)
          p.SplittingField)
  simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
    AlgEquiv.symm_apply_apply]
  have haction := autEquivZmod_symm_apply_natCast
    (localUniformizer_X_pow_sub_C_irreducible K n hn)
    p.SplittingField
    (rootOfSplitsXPowSubC_pow (localUniformizerInteger K : K) p.SplittingField)
    hprimitive 1
  have haction' :
      ((autEquivZmod
        (localUniformizer_X_pow_sub_C_irreducible K n hn)
        p.SplittingField hprimitive).symm
          (Multiplicative.ofAdd (1 : ZMod n)))
            (rootOfSplitsXPowSubC (NeZero.pos n)
              (localUniformizerInteger K : K) p.SplittingField) =
        hroot.choose ^ 1 •
          rootOfSplitsXPowSubC (NeZero.pos n)
            (localUniformizerInteger K : K) p.SplittingField := by
    simpa only [Nat.cast_one] using haction
  calc
    i.equivFieldRange
        (((autEquivZmod
          (localUniformizer_X_pow_sub_C_irreducible K n hn)
          p.SplittingField hprimitive).symm
            (Multiplicative.ofAdd (1 : ZMod n)))
              (rootOfSplitsXPowSubC (NeZero.pos n) (localUniformizerInteger K : K)
                p.SplittingField)) =
      i.equivFieldRange
        (hroot.choose ^ 1 •
          rootOfSplitsXPowSubC (NeZero.pos n) (localUniformizerInteger K : K)
            p.SplittingField) := congrArg i.equivFieldRange haction'
    _ = algebraMap K i.fieldRange hroot.choose *
        i.equivFieldRange
          (rootOfSplitsXPowSubC (NeZero.pos n) (localUniformizerInteger K : K)
            p.SplittingField) := by
      simp only [pow_one, Algebra.smul_def, map_mul,
        i.equivFieldRange.commutes]

end Anabelian.LCFT
