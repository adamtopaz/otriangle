import Otriangle.MonoAnabelian.SpectralLocalField
import Mathlib.RingTheory.Henselian

/-!
# Prime-to-residue-characteristic divisibility of principal units

For a mixed-characteristic local field `K`, every prime-to-residue-characteristic prime-power
equation `x ^ l = u` with `u` a principal unit has a principal-unit solution.  This is the
Henselian part of the local multiplicative-group calculation underlying Hoshi's Lemma 1.2 and
Lemma 3.4.
-/

noncomputable section

namespace Anabelian
namespace LCFT

open OTriangle
open ValuativeRel

universe u

/-- If `l` differs from the residue characteristic, the `l`th-power map on principal units is
surjective. -/
theorem principalUnit_pow_surjective_of_ne_residueChar
    (K : PointedMixedCharLocalField.{u}) (l : ℕ) (hl : l.Prime)
    (hne : l ≠ K.residueChar) :
    Function.Surjective
      (powMonoidHom
        (α := (valuation K).valuationSubring.principalUnitGroup) l) := by
  letI := K.nontriviallyNormedField
  letI := K.isUltrametricDist
  letI := K.completeSpace
  let A : ValuationSubring K := (valuation K).valuationSubring
  letI : HenselianRing A (IsLocalRing.maximalIdeal A) := by
    change HenselianRing (valuation K).integer
      (IsLocalRing.maximalIdeal (valuation K).integer)
    infer_instance
  intro u
  let uKer : (Units.map (IsLocalRing.residue A).toMonoidHom).ker :=
    A.principalUnitGroupEquiv u
  let uA : A := ((uKer : Aˣ) : A)
  let f : Polynomial A := Polynomial.X ^ l - Polynomial.C uA
  have hf : f.Monic := by
    exact Polynomial.monic_X_pow_sub_C uA hl.ne_zero
  have huResidue : IsLocalRing.residue A uA = 1 := by
    have h := uKer.property
    rw [MonoidHom.mem_ker] at h
    exact Units.ext_iff.mp h
  have hfOne : f.eval 1 ∈ IsLocalRing.maximalIdeal A := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [f, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, one_pow, map_sub, map_one]
    change 1 - IsLocalRing.residue A uA = 0
    rw [huResidue, sub_self]
  letI : CharP (IsLocalRing.ResidueField A) K.residueChar := by
    change CharP (IsLocalRing.ResidueField (valuation K).integer) K.residueChar
    infer_instance
  have hlCast : (l : IsLocalRing.ResidueField A) ≠ 0 := by
    intro hzero
    have hdiv : K.residueChar ∣ l :=
      (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField A)
        K.residueChar l).mp hzero
    rcases (Nat.dvd_prime hl).mp hdiv with hOne | heq
    · exact (Fact.out : K.residueChar.Prime).ne_one hOne
    · exact hne heq.symm
  have hfDeriv : IsUnit
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (f.derivative.eval 1)) := by
    refine ⟨Units.mk0 (l : IsLocalRing.ResidueField A) hlCast, ?_⟩
    change (l : IsLocalRing.ResidueField A) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (f.derivative.eval 1)
    rw [show f.derivative.eval 1 = (l : A) by
      simp [f, Polynomial.derivative_X_pow]]
    exact (map_natCast (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) l).symm
  obtain ⟨a, haRoot, haOne⟩ :=
    HenselianRing.is_henselian f hf (1 : A) hfOne hfDeriv
  have haPow : a ^ l = uA := by
    apply sub_eq_zero.mp
    simpa [Polynomial.IsRoot, f] using haRoot
  have haResidue : IsLocalRing.residue A a = 1 := by
    have hzero : IsLocalRing.residue A (a - 1) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).2 haOne
    rwa [map_sub, map_one, sub_eq_zero] at hzero
  have haUnit : IsUnit a :=
    (IsLocalRing.residue_ne_zero_iff_isUnit a).mp (by simp [haResidue])
  let aKer : (Units.map (IsLocalRing.residue A).toMonoidHom).ker :=
    ⟨haUnit.unit, by
      rw [MonoidHom.mem_ker]
      apply Units.ext
      exact haResidue⟩
  let v : A.principalUnitGroup := A.principalUnitGroupEquiv.symm aKer
  refine ⟨v, ?_⟩
  change v ^ l = u
  apply A.principalUnitGroupEquiv.injective
  rw [map_pow]
  change aKer ^ l = uKer
  apply Subtype.ext
  apply Units.ext
  exact haPow

end LCFT
end Anabelian
