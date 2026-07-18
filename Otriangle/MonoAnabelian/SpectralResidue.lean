import Otriangle.MonoAnabelian.SpectralLocalField

/-!
# Residue actions for spectral valuations

An automorphism of an algebraic tower preserves its spectral valuation.  Consequently it restricts
to the valuation ring and descends to the residue field.  This module packages that construction
as a homomorphism of absolute Galois groups; lifting and topological properties are kept separate.
-/

noncomputable section

namespace Anabelian
namespace OTriangle
namespace SpectralLocalField

open ValuativeRel

variable (K E A : Type*)
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Field E] [Algebra K E]
  [Field A] [Algebra K A] [Algebra.IsAlgebraic K A]
  [Algebra E A] [IsScalarTower K E A]

/-- An automorphism over an intermediate field preserves the spectral valuation ring. -/
theorem automorphism_mem_integer_iff
    (σ : A ≃ₐ[E] A) (x : A) :
    letI := nontriviallyNormedField K A
    letI := isUltrametricDist K A
    letI := valuativeRel K A
    x ∈ 𝒪[A] ↔ σ x ∈ 𝒪[A] := by
  letI := nontriviallyNormedField K A
  letI := isUltrametricDist K A
  letI : ValuativeRel A := valuativeRel K A
  letI : (NormedField.valuation (K := A)).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff]
  rw [← (valuation A).vle_one_iff, ← (valuation A).vle_one_iff]
  rw [(NormedField.valuation (K := A)).vle_one_iff,
    (NormedField.valuation (K := A)).vle_one_iff]
  change spectralNorm K A x ≤ 1 ↔ spectralNorm K A (σ x) ≤ 1
  have hσ : spectralNorm K A x = spectralNorm K A (σ x) := by
    simpa using spectralNorm_eq_of_equiv (σ.restrictScalars K) x
  rw [hσ]

/-- An automorphism of an algebraic tower restricts to the spectral valuation ring. -/
noncomputable def automorphismIntegerAlgEquiv
    [Algebra.IsAlgebraic K E] (σ : A ≃ₐ[E] A) :
    letI := nontriviallyNormedField K E
    letI := isUltrametricDist K E
    letI := valuativeRel K E
    letI := nontriviallyNormedField K A
    letI := isUltrametricDist K A
    letI := valuativeRel K A
    letI := valuativeExtension K (E := E) (A := A)
    𝒪[A] ≃ₐ[𝒪[E]] 𝒪[A] := by
  letI := nontriviallyNormedField K E
  letI := isUltrametricDist K E
  letI : ValuativeRel E := valuativeRel K E
  letI := nontriviallyNormedField K A
  letI := isUltrametricDist K A
  letI : ValuativeRel A := valuativeRel K A
  letI : ValuativeExtension E A := valuativeExtension K (E := E) (A := A)
  let e : 𝒪[A] ≃+* 𝒪[A] :=
    { toFun := fun x =>
        ⟨σ x, (automorphism_mem_integer_iff K E A σ x).mp x.property⟩
      invFun := fun x =>
        ⟨σ.symm x, (automorphism_mem_integer_iff K E A σ.symm x).mp x.property⟩
      left_inv := fun x => Subtype.ext (σ.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (σ.apply_symm_apply x)
      map_mul' := fun x y => Subtype.ext (map_mul σ (x : A) (y : A))
      map_add' := fun x y => Subtype.ext (map_add σ (x : A) (y : A)) }
  exact
    { toRingEquiv := e
      commutes' := fun x => Subtype.ext (σ.commutes (x : E)) }

/-- The residue action induced by the spectral valuation on an algebraic tower. -/
noncomputable def residueGaloisMap [Algebra.IsAlgebraic K E] :
    letI := nontriviallyNormedField K E
    letI := isUltrametricDist K E
    letI := valuativeRel K E
    letI := nontriviallyNormedField K A
    letI := isUltrametricDist K A
    letI := valuativeRel K A
    letI := valuativeExtension K (E := E) (A := A)
    (A ≃ₐ[E] A) →* (𝓀[A] ≃ₐ[𝓀[E]] 𝓀[A]) := by
  letI := nontriviallyNormedField K E
  letI := isUltrametricDist K E
  letI : ValuativeRel E := valuativeRel K E
  letI := nontriviallyNormedField K A
  letI := isUltrametricDist K A
  letI : ValuativeRel A := valuativeRel K A
  letI : ValuativeExtension E A := valuativeExtension K (E := E) (A := A)
  refine
    { toFun := fun σ => IsLocalRing.ResidueField.mapAlgEquiv'
        (automorphismIntegerAlgEquiv K E A σ)
      map_one' := ?_
      map_mul' := ?_ }
  · apply AlgEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    simp [automorphismIntegerAlgEquiv]
  · intro σ τ
    apply AlgEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    simp [automorphismIntegerAlgEquiv]

end SpectralLocalField
end OTriangle
end Anabelian
