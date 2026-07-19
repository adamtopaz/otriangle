import Otriangle.MonoAnabelian.TameKummerExtension

/-!
# Kummer extensions for a specified uniformizer

The canonical local uniformizer chosen by typeclass data is not functorial in unramified
extensions.  For the Frobenius-conjugation calculation we must instead use the image of the base
uniformizer.  This module develops the algebraic Kummer splitting field for any integer generating
the maximal ideal.
-/

noncomputable section

namespace Anabelian.LCFT

open OTriangle ValuativeRel Polynomial

universe u

/-- `X ^ n - π` is irreducible whenever `π` generates the maximal ideal. -/
theorem uniformizer_X_pow_sub_C_irreducible
    (K : PointedMixedCharLocalField.{u}) (pi : LocalIntegerRing K)
    (hpi : Ideal.span {pi} = localMaximalIdeal K)
    (n : ℕ) (hn : 0 < n) :
    Irreducible (X ^ n - C (pi : K) : K[X]) := by
  let R := LocalIntegerRing K
  let m : Ideal R := localMaximalIdeal K
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
      have hpim : pi ∈ m := by
        change pi ∈ localMaximalIdeal K
        rw [← hpi]
        exact Ideal.mem_span_singleton.mpr (dvd_refl pi)
      have hcoeff : f.coeff 0 = -pi := by
        dsimp only [f]
        rw [coeff_sub, coeff_X_pow, if_neg (Nat.ne_of_gt hn).symm, coeff_C_zero,
          zero_sub]
      rw [hcoeff]
      exact m.neg_mem hpim
    · have hin : i ≠ n := ne_of_lt hi'
      have hcoeff : f.coeff i = 0 := by
        dsimp only [f]
        rw [coeff_sub, coeff_X_pow, if_neg hin, coeff_C, if_neg hi0, sub_zero]
      rw [hcoeff]
      exact m.zero_mem
  have hpi_not : -pi ∉ m ^ 2 := by
    intro hpipow
    have hle : m ≤ m ^ 2 := by
      dsimp only [m] at hpipow ⊢
      rw [← hpi]
      rw [← hpi] at hpipow
      intro x hx
      rw [Ideal.mem_span_singleton] at hx
      obtain ⟨a, rfl⟩ := hx
      have hpipos := (Ideal.span {pi} ^ 2).neg_mem hpipow
      rw [neg_neg] at hpipos
      exact (Ideal.span {pi} ^ 2).mul_mem_right a hpipos
    have heq : m ^ 1 = m ^ 2 := by
      rw [pow_one]
      exact le_antisymm hle (by
        simpa only [pow_one] using
          (Ideal.pow_le_pow_right (I := m) (show 1 ≤ 2 by omega)))
    have := localMaximalIdeal_pow_injective K heq
    omega
  have hcoeff0 : f.coeff 0 = -pi := by
    dsimp only [f]
    rw [coeff_sub, coeff_X_pow, if_neg (Nat.ne_of_gt hn).symm, coeff_C_zero,
      zero_sub]
  have hfeis : f.IsEisensteinAt m :=
    hfmonic.isEisensteinAt_of_mem_of_notMem hmne hfmem (by
      rw [hcoeff0]
      exact hpi_not)
  have hfirr : Irreducible f := hfeis.irreducible inferInstance hfmonic.isPrimitive (by
    change 0 < (X ^ n - C pi).natDegree
    rwa [natDegree_X_pow_sub_C])
  have hmap : f.map (algebraMap R K) = (X ^ n - C (pi : K) : K[X]) := by
    dsimp only [f]
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C]
    rfl
  rw [← hmap]
  exact hfmonic.irreducible_iff_irreducible_map_fraction_map.mp hfirr

/-- The splitting field of `X ^ n - π`, embedded in the chosen algebraic closure. -/
noncomputable def uniformizerKummerIntermediateField
    (K : PointedMixedCharLocalField.{u}) (pi : LocalIntegerRing K) (n : ℕ) :
    IntermediateField K K.algebraicClosure := by
  let p : K[X] := X ^ n - C (pi : K)
  letI : IsAlgClosed K.algebraicClosure := IsAlgClosure.isAlgClosed K
  let i : p.SplittingField →ₐ[K] K.algebraicClosure := IsAlgClosed.lift
  exact i.fieldRange

/-- The specified-uniformizer splitting field is finite Galois in positive degree. -/
noncomputable def uniformizerKummerFiniteGaloisIntermediateField
    (K : PointedMixedCharLocalField.{u}) (pi : LocalIntegerRing K)
    (hpi : pi ≠ 0) (n : ℕ) (hn : 0 < n) :
    FiniteGaloisIntermediateField K K.algebraicClosure := by
  let p : K[X] := X ^ n - C (pi : K)
  letI : IsAlgClosed K.algebraicClosure := IsAlgClosure.isAlgClosed K
  let i : p.SplittingField →ₐ[K] K.algebraicClosure := IsAlgClosed.lift
  let L : IntermediateField K K.algebraicClosure := i.fieldRange
  have hpifield : (pi : K) ≠ 0 := by exact_mod_cast hpi
  have hncast : (n : K) ≠ 0 := by exact_mod_cast hn.ne'
  letI : IsGalois K p.SplittingField :=
    IsGalois.of_separable_splitting_field
      (Polynomial.separable_X_pow_sub_C _ hncast hpifield)
  letI : FiniteDimensional K L := Module.Finite.equiv i.equivFieldRange.toLinearEquiv
  letI : IsGalois K L := IsGalois.of_algEquiv i.equivFieldRange
  exact { toIntermediateField := L }

/-- If the base contains a primitive `n`th root of unity, the specified-uniformizer Kummer field
has degree `n`. -/
theorem uniformizerKummerIntermediateField_finrank
    (K : PointedMixedCharLocalField.{u}) (pi : LocalIntegerRing K)
    (hpi : Ideal.span {pi} = localMaximalIdeal K)
    (n : ℕ) (hn : 0 < n) (hroot : (primitiveRoots n K).Nonempty) :
    Module.finrank K (uniformizerKummerIntermediateField K pi n) = n := by
  let p : K[X] := X ^ n - C (pi : K)
  letI : IsAlgClosed K.algebraicClosure := IsAlgClosure.isAlgClosed K
  let i : p.SplittingField →ₐ[K] K.algebraicClosure := IsAlgClosed.lift
  change Module.finrank K i.fieldRange = n
  rw [← i.equivFieldRange.toLinearEquiv.finrank_eq]
  exact finrank_of_isSplittingField_X_pow_sub_C hroot
    (uniformizer_X_pow_sub_C_irreducible K pi hpi n hn) p.SplittingField

/-- A distinguished `n`th root of the specified uniformizer. -/
noncomputable def uniformizerKummerRoot
    (K : PointedMixedCharLocalField.{u}) (pi : LocalIntegerRing K)
    (n : ℕ) [NeZero n] :
    uniformizerKummerIntermediateField K pi n := by
  let p : K[X] := X ^ n - C (pi : K)
  letI : IsAlgClosed K.algebraicClosure := IsAlgClosure.isAlgClosed K
  let i : p.SplittingField →ₐ[K] K.algebraicClosure := IsAlgClosed.lift
  let a : p.SplittingField :=
    rootOfSplitsXPowSubC (NeZero.pos n) (pi : K) p.SplittingField
  exact ⟨i a, ⟨a, rfl⟩⟩

theorem uniformizerKummerRoot_pow
    (K : PointedMixedCharLocalField.{u}) (pi : LocalIntegerRing K)
    (n : ℕ) [NeZero n] :
    uniformizerKummerRoot K pi n ^ n =
      algebraMap K (uniformizerKummerIntermediateField K pi n) (pi : K) := by
  apply Subtype.ext
  let p : K[X] := X ^ n - C (pi : K)
  letI : IsAlgClosed K.algebraicClosure := IsAlgClosure.isAlgClosed K
  let i : p.SplittingField →ₐ[K] K.algebraicClosure := IsAlgClosed.lift
  change i (rootOfSplitsXPowSubC (NeZero.pos n) (pi : K) p.SplittingField) ^ n =
    algebraMap K K.algebraicClosure (pi : K)
  rw [← map_pow, rootOfSplitsXPowSubC_pow]
  exact i.commutes _

/-- The distinguished Kummer root is integral over the specified base valuation ring. -/
theorem uniformizerKummerRoot_isIntegral
    (K : PointedMixedCharLocalField.{u}) (pi : LocalIntegerRing K)
    (n : ℕ) [NeZero n] :
    IsIntegral (LocalIntegerRing K) (uniformizerKummerRoot K pi n) := by
  let f : (LocalIntegerRing K)[X] := X ^ n - C pi
  refine ⟨f, monic_X_pow_sub_C _ (NeZero.ne n), ?_⟩
  change Polynomial.aeval (uniformizerKummerRoot K pi n) f = 0
  rw [aeval_def, eval₂_sub, eval₂_X_pow, eval₂_C]
  change uniformizerKummerRoot K pi n ^ n -
      algebraMap (LocalIntegerRing K) (uniformizerKummerIntermediateField K pi n) pi = 0
  rw [uniformizerKummerRoot_pow]
  apply sub_eq_zero.mpr
  rfl

/-- The generator of the specified-uniformizer Kummer Galois group determined by a primitive
root in the base. -/
noncomputable def uniformizerKummerGeneratorAutomorphism
    (K : PointedMixedCharLocalField.{u}) (pi : LocalIntegerRing K)
    (hpi : Ideal.span {pi} = localMaximalIdeal K)
    (n : ℕ) (hn : 0 < n) (hroot : (primitiveRoots n K).Nonempty) :
    uniformizerKummerIntermediateField K pi n ≃ₐ[K]
      uniformizerKummerIntermediateField K pi n := by
  letI : NeZero n := ⟨hn.ne'⟩
  let p : K[X] := X ^ n - C (pi : K)
  letI : IsAlgClosed K.algebraicClosure := IsAlgClosure.isAlgClosed K
  let i : p.SplittingField →ₐ[K] K.algebraicClosure := IsAlgClosed.lift
  have hprimitive : IsPrimitiveRoot hroot.choose n :=
    (mem_primitiveRoots hn).mp hroot.choose_spec
  exact (AlgEquiv.autCongr i.equivFieldRange)
    ((autEquivZmod (uniformizer_X_pow_sub_C_irreducible K pi hpi n hn)
      p.SplittingField hprimitive).symm
        (Multiplicative.ofAdd (1 : ZMod n)))

/-- The Kummer generator multiplies the distinguished root by the chosen primitive root. -/
theorem uniformizerKummerGeneratorAutomorphism_apply_root
    (K : PointedMixedCharLocalField.{u}) (pi : LocalIntegerRing K)
    (hpi : Ideal.span {pi} = localMaximalIdeal K)
    (n : ℕ) [NeZero n] (hn : 0 < n)
    (hroot : (primitiveRoots n K).Nonempty) :
    uniformizerKummerGeneratorAutomorphism K pi hpi n hn hroot
        (uniformizerKummerRoot K pi n) =
      algebraMap K (uniformizerKummerIntermediateField K pi n) hroot.choose *
        uniformizerKummerRoot K pi n := by
  let p : K[X] := X ^ n - C (pi : K)
  letI : IsAlgClosed K.algebraicClosure := IsAlgClosure.isAlgClosed K
  let i : p.SplittingField →ₐ[K] K.algebraicClosure := IsAlgClosed.lift
  have hprimitive : IsPrimitiveRoot hroot.choose n :=
    (mem_primitiveRoots hn).mp hroot.choose_spec
  dsimp only [uniformizerKummerGeneratorAutomorphism, uniformizerKummerRoot,
    uniformizerKummerIntermediateField]
  change (AlgEquiv.autCongr i.equivFieldRange
      ((autEquivZmod
      (uniformizer_X_pow_sub_C_irreducible K pi hpi n hn)
      p.SplittingField hprimitive).symm
        (Multiplicative.ofAdd (1 : ZMod n))))
      (i.equivFieldRange
        (rootOfSplitsXPowSubC (NeZero.pos n) (pi : K) p.SplittingField)) =
    algebraMap K i.fieldRange hroot.choose *
      i.equivFieldRange
        (rootOfSplitsXPowSubC (NeZero.pos n) (pi : K) p.SplittingField)
  simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
    AlgEquiv.symm_apply_apply]
  have haction := autEquivZmod_symm_apply_natCast
    (uniformizer_X_pow_sub_C_irreducible K pi hpi n hn)
    p.SplittingField
    (rootOfSplitsXPowSubC_pow (pi : K) p.SplittingField)
    hprimitive 1
  have haction' :
      ((autEquivZmod
        (uniformizer_X_pow_sub_C_irreducible K pi hpi n hn)
        p.SplittingField hprimitive).symm
          (Multiplicative.ofAdd (1 : ZMod n)))
            (rootOfSplitsXPowSubC (NeZero.pos n) (pi : K) p.SplittingField) =
        hroot.choose ^ 1 •
          rootOfSplitsXPowSubC (NeZero.pos n) (pi : K) p.SplittingField := by
    simpa only [Nat.cast_one] using haction
  calc
    i.equivFieldRange
        (((autEquivZmod
          (uniformizer_X_pow_sub_C_irreducible K pi hpi n hn)
          p.SplittingField hprimitive).symm
            (Multiplicative.ofAdd (1 : ZMod n)))
              (rootOfSplitsXPowSubC (NeZero.pos n) (pi : K)
                p.SplittingField)) =
      i.equivFieldRange
        (hroot.choose ^ 1 •
          rootOfSplitsXPowSubC (NeZero.pos n) (pi : K)
            p.SplittingField) := congrArg i.equivFieldRange haction'
    _ = algebraMap K i.fieldRange hroot.choose *
        i.equivFieldRange
          (rootOfSplitsXPowSubC (NeZero.pos n) (pi : K)
            p.SplittingField) := by
      simp only [pow_one, Algebra.smul_def, map_mul,
        i.equivFieldRange.commutes]

end Anabelian.LCFT
