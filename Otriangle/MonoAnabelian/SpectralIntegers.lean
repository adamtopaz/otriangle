import Otriangle.MonoAnabelian.SpectralLocalField
import Mathlib.RingTheory.Valuation.Integral

/-!
# Integral elements for spectral valuations

For an algebraic extension of a pointed local field, the spectral valuation ring consists of
elements integral over the original valuation ring.  The proof lifts the minimal polynomial after
using the spectral-value coefficient bound.
-/

noncomputable section

namespace Anabelian
namespace OTriangle
namespace PointedMixedCharLocalField

open ValuativeRel

universe u v

/-- An element of the spectral valuation ring is integral over the original valuation ring. -/
theorem spectralInteger_isIntegral
    (K : PointedMixedCharLocalField.{u})
    (L : Type v) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (x :
      letI := K.nontriviallyNormedField
      letI := K.isUltrametricDist
      letI := K.completeSpace
      letI := SpectralLocalField.nontriviallyNormedField K L
      letI := SpectralLocalField.isUltrametricDist K L
      letI := SpectralLocalField.valuativeRel K L
      𝒪[L]) :
    letI := K.nontriviallyNormedField
    letI := K.isUltrametricDist
    letI := K.completeSpace
    letI := SpectralLocalField.nontriviallyNormedField K L
    letI := SpectralLocalField.isUltrametricDist K L
    letI := SpectralLocalField.valuativeRel K L
    letI := K.spectralValuativeExtension L
    IsIntegral 𝒪[K] x := by
  letI := K.nontriviallyNormedField
  letI := K.isUltrametricDist
  letI := K.completeSpace
  letI := SpectralLocalField.nontriviallyNormedField K L
  letI := SpectralLocalField.isUltrametricDist K L
  letI : ValuativeRel L := SpectralLocalField.valuativeRel K L
  letI : ValuativeExtension K L := K.spectralValuativeExtension L
  letI : (NormedField.valuation (K := L)).Compatible :=
    Valuation.Compatible.ofValuation _
  have hxnorm : spectralNorm K L (x : L) ≤ 1 := by
    have hx := x.property
    rw [Valuation.mem_integer_iff] at hx
    rw [← (valuation L).vle_one_iff] at hx
    rw [(NormedField.valuation (K := L)).vle_one_iff] at hx
    exact hx
  let p : Polynomial K := minpoly K (x : L)
  have hpcoeff : ∀ n : ℕ, ‖p.coeff n‖ ≤ 1 := by
    exact (spectralValue_le_one_iff (minpoly.monic
      (Algebra.IsIntegral.isIntegral (x : L)))).mp hxnorm
  have hplifts : p ∈ Polynomial.lifts (algebraMap 𝒪[K] K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    refine ⟨⟨p.coeff n, ?_⟩, rfl⟩
    rw [Valuation.mem_integer_iff]
    rw [← (valuation K).vle_one_iff]
    apply (K.norm_le_norm_iff_vle (p.coeff n) 1).mp
    simpa using hpcoeff n
  obtain ⟨q, hq, -, hqmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hplifts
      (minpoly.monic (Algebra.IsIntegral.isIntegral (x : L)))
  refine ⟨q, hqmonic, ?_⟩
  change (Polynomial.aeval x) q = 0
  have heval := Polynomial.map_aeval_eq_aeval_map
    (φ := algebraMap 𝒪[K] K)
    (ψ := algebraMap 𝒪[L] L)
    (by
      ext z
      exact IsScalarTower.algebraMap_apply 𝒪[K] K L z)
    q x
  have hroot : (Polynomial.aeval (x : L))
      (q.map (algebraMap 𝒪[K] K)) = 0 := by
    rw [hq]
    exact minpoly.aeval K (x : L)
  apply (Valuation.integer.integers (valuation L)).hom_inj
  simpa only [map_zero] using heval.trans hroot

/-- The spectral valuation ring is integral over the original valuation ring. -/
theorem spectralInteger_isIntegralAlgebra
    (K : PointedMixedCharLocalField.{u})
    (L : Type v) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] :
    letI := K.nontriviallyNormedField
    letI := K.isUltrametricDist
    letI := K.completeSpace
    letI := SpectralLocalField.nontriviallyNormedField K L
    letI := SpectralLocalField.isUltrametricDist K L
    letI := SpectralLocalField.valuativeRel K L
    letI := K.spectralValuativeExtension L
    Algebra.IsIntegral 𝒪[K] 𝒪[L] := by
  letI := K.nontriviallyNormedField
  letI := K.isUltrametricDist
  letI := K.completeSpace
  letI := SpectralLocalField.nontriviallyNormedField K L
  letI := SpectralLocalField.isUltrametricDist K L
  letI : ValuativeRel L := SpectralLocalField.valuativeRel K L
  letI : ValuativeExtension K L := K.spectralValuativeExtension L
  exact ⟨fun x => K.spectralInteger_isIntegral L x⟩

end PointedMixedCharLocalField
end OTriangle
end Anabelian
