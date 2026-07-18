import Otriangle.OTriangle.Core
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Spectral local-field structures on finite extensions

This module constructs the local-field structure on a finite extension from the spectral norm.
It supplies the arithmetic foundation needed to regard the fixed fields of open subgroups as
local fields, without adding that fact as data to a presentation.
-/

noncomputable section

namespace Anabelian
namespace OTriangle
namespace SpectralLocalField

open ValuativeRel
open scoped NNReal

universe u v

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]
variable (L : Type v) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- The spectral norm makes a finite extension into a normed field. -/
@[implicit_reducible]
noncomputable def normedField : NormedField L :=
  spectralNorm.normedField K L

/-- Nontriviality of the spectral norm inherited from the base field. -/
@[implicit_reducible]
noncomputable def nontriviallyNormedField : NontriviallyNormedField L :=
  spectralNorm.nontriviallyNormedField K L

/-- The spectral norm is nonarchimedean. -/
theorem isUltrametricDist :
    letI := nontriviallyNormedField K L
    IsUltrametricDist L := by
  letI := nontriviallyNormedField K L
  exact IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    isNonarchimedean_spectralNorm

/-- The valuative relation determined by the spectral valuation. -/
@[implicit_reducible]
noncomputable def valuativeRel : ValuativeRel L := by
  letI := nontriviallyNormedField K L
  letI := isUltrametricDist K L
  exact ValuativeRel.ofValuation NormedField.valuation

/-- The topology determined by the spectral norm. -/
@[implicit_reducible]
noncomputable def topologicalSpace : TopologicalSpace L :=
  (nontriviallyNormedField K L).toNormedField.toUniformSpace.toTopologicalSpace

/-- The norm topology agrees with the topology of the spectral valuative relation. -/
theorem isValuativeTopology :
    letI := nontriviallyNormedField K L
    letI := isUltrametricDist K L
    letI := valuativeRel K L
    letI := topologicalSpace K L
    IsValuativeTopology L := by
  letI := nontriviallyNormedField K L
  letI := isUltrametricDist K L
  letI : ValuativeRel L := valuativeRel K L
  letI : TopologicalSpace L := topologicalSpace K L
  letI : (NormedField.valuation (K := L)).Compatible :=
    Valuation.Compatible.ofValuation _
  letI : Valued L NNReal := NormedField.toValued (K := L)
  apply IsValuativeTopology.of_zero
  intro s
  rw [Valued.is_topological_valuation]
  constructor
  · rintro ⟨γ, hγ⟩
    let e := ValuativeRel.ValueGroupWithZero.orderMonoidIso
      (Valued.v : Valuation L NNReal)
    refine ⟨Units.mapEquiv e.symm.toMulEquiv γ, ?_⟩
    intro x hx
    apply hγ
    exact (ValuativeRel.valuation_lt_symm_orderMonoidIso
      (Valued.v : Valuation L NNReal) γ x).mp hx
  · rintro ⟨γ, hγ⟩
    let e := ValuativeRel.ValueGroupWithZero.orderMonoidIso
      (Valued.v : Valuation L NNReal)
    refine ⟨Units.mapEquiv e.toMulEquiv γ, ?_⟩
    intro x hx
    apply hγ
    have hx' := (ValuativeRel.valuation_lt_symm_orderMonoidIso
      (Valued.v : Valuation L NNReal) (Units.mapEquiv e.toMulEquiv γ :
        (MonoidWithZeroHom.ValueGroup₀
          (.ofClass (Valued.v : Valuation L NNReal)))ˣ).1 x).mpr hx
    simpa [e] using hx'

/-- Spectral valuative relations are compatible along an algebraic tower. -/
theorem valuativeExtension
    {E : Type v} [Field E] [Algebra K E] [Algebra.IsAlgebraic K E]
    {A : Type*} [Field A] [Algebra K A] [Algebra.IsAlgebraic K A]
    [Algebra E A] [IsScalarTower K E A] :
    letI := nontriviallyNormedField K E
    letI := isUltrametricDist K E
    letI := valuativeRel K E
    letI := nontriviallyNormedField K A
    letI := isUltrametricDist K A
    letI := valuativeRel K A
    ValuativeExtension E A := by
  letI := nontriviallyNormedField K E
  letI := isUltrametricDist K E
  letI : ValuativeRel E := valuativeRel K E
  letI := nontriviallyNormedField K A
  letI := isUltrametricDist K A
  letI : ValuativeRel A := valuativeRel K A
  constructor
  intro x y
  change ‖algebraMap E A x‖ ≤ ‖algebraMap E A y‖ ↔ ‖x‖ ≤ ‖y‖
  rw [show ‖algebraMap E A x‖ = ‖x‖ from (spectralNorm.eq_of_tower x).symm,
    show ‖algebraMap E A y‖ = ‖y‖ from (spectralNorm.eq_of_tower y).symm]

variable [LocallyCompactSpace K] [FiniteDimensional K L]

/-- A finite-dimensional spectral-norm extension of a locally compact field is locally compact. -/
theorem locallyCompactSpace :
    letI := nontriviallyNormedField K L
    letI := spectralNorm.normedSpace K L
    LocallyCompactSpace L := by
  letI := nontriviallyNormedField K L
  letI := spectralNorm.normedSpace K L
  exact LocallyCompactSpace.of_finiteDimensional_of_complete K L

/-- Every finite extension, equipped with its spectral norm and valuation, is a
nonarchimedean local field. -/
theorem isNonarchimedeanLocalField :
    letI := nontriviallyNormedField K L
    letI := isUltrametricDist K L
    letI := valuativeRel K L
    letI := topologicalSpace K L
    IsNonarchimedeanLocalField L := by
  letI := nontriviallyNormedField K L
  letI := isUltrametricDist K L
  letI : ValuativeRel L := valuativeRel K L
  letI : TopologicalSpace L := topologicalSpace K L
  letI : (NormedField.valuation (K := L)).Compatible :=
    Valuation.Compatible.ofValuation _
  letI : IsValuativeTopology L := isValuativeTopology K L
  letI : NormedSpace K L := spectralNorm.normedSpace K L
  letI : LocallyCompactSpace L := locallyCompactSpace K L
  refine
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := ?_ }
  rw [ValuativeRel.isNontrivial_iff_isNontrivial
    (NormedField.valuation (K := L))]
  infer_instance

end SpectralLocalField

namespace PointedMixedCharLocalField

open ValuativeRel

/-- The canonical rank-one normed-field model associated to the valuative topology of a pointed
local field.  Its topology is the topology already carried by the pointed field. -/
@[implicit_reducible]
noncomputable def nontriviallyNormedField (K : PointedMixedCharLocalField.{u}) :
    NontriviallyNormedField K := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : Valued K (ValueGroupWithZero K) := inferInstance
  letI : (Valued.v : Valuation K (ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  exact Valued.toNontriviallyNormedField K (ValueGroupWithZero K)

/-- The norm obtained from a pointed local field is nonarchimedean. -/
theorem isUltrametricDist (K : PointedMixedCharLocalField.{u}) :
    letI := K.nontriviallyNormedField
    IsUltrametricDist K := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : Valued K (ValueGroupWithZero K) := inferInstance
  letI : (Valued.v : Valuation K (ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI := K.nontriviallyNormedField
  infer_instance

/-- The normed model of a pointed local field is complete. -/
theorem completeSpace (K : PointedMixedCharLocalField.{u}) :
    letI := K.nontriviallyNormedField
    CompleteSpace K := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI := K.nontriviallyNormedField
  exact IsNonarchimedeanLocalField.instCompleteSpace K

end PointedMixedCharLocalField
end OTriangle
end Anabelian
