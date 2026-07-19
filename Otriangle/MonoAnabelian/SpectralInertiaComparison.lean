import Otriangle.MonoAnabelian.SpectralPointing
import Otriangle.MonoAnabelian.FiniteGaloisRamification
import Otriangle.MonoAnabelian.ClassicalRamification

/-!
# Comparison of the recorded and spectral inertia subgroups

The pointing records a residue action, while finite fixed fields use the canonical spectral
valuation.  Local reciprocity for the degree-one extension between these two pointings forces
their abelianized inertia subgroups to agree.  Since full inertia is the inverse image of
abelianized inertia, the two full inertia subgroups agree as well.
-/

noncomputable section

open scoped commutatorElement

namespace Anabelian.LCFT

open OTriangle

universe u

/-- The identity extension from the original pointing to its spectral-closure pointing. -/
noncomputable def spectralPointingExtension (K : PointedMixedCharLocalField.{u}) :
    FiniteExtension K K.spectralPointing := by
  refine { algebra := ?_, finiteDimensional := ?_, valuativeExtension := ?_ }
  · exact (RingHom.id K).toAlgebra
  · infer_instance
  · constructor
    intro x y
    rfl

/-- The norm of the identity extension between the two pointings is the identity. -/
@[simp]
theorem spectralPointingExtension_norm
    (K : PointedMixedCharLocalField.{u}) (x : K.spectralPointingˣ) :
    (spectralPointingExtension K).norm x = x := by
  apply Units.ext
  change Algebra.norm K (x : K) = x
  rw [Algebra.norm_self]
  exact MonoidHom.id_apply K (x : K)

/-- Conjugation between the identical algebraic closures becomes the identity after topological
abelianization. -/
@[simp]
theorem spectralPointingExtension_abelianizedGaloisMap
    (K : PointedMixedCharLocalField.{u})
    (x : AbelianizedAbsoluteGaloisGroup K.spectralPointing) :
    (spectralPointingExtension K).abelianizedGaloisMap x = x := by
  induction x using Quotient.inductionOn with
  | _ σ =>
    change (spectralPointingExtension K).abelianizedGaloisMap
        (QuotientGroup.mk' _ σ) = QuotientGroup.mk' _ σ
    rw [FiniteExtension.abelianizedGaloisMap_mk]
    let q := QuotientGroup.mk'
      (Subgroup.topologicalClosure (commutator (AbsoluteGaloisGroup K)))
    change q ((spectralPointingExtension K).galoisMap σ) = q σ
    let e : K.spectralPointing.algebraicClosure ≃ₐ[K] K.algebraicClosure :=
      IsAlgClosure.equiv K K.spectralPointing.algebraicClosure K.algebraicClosure
    have hg : (spectralPointingExtension K).galoisMap σ = e * σ * e⁻¹ := by
      ext z
      rfl
    rw [hg, map_mul, map_mul, map_inv]
    simp [mul_comm]

/-- Reciprocity does not depend on replacing the recorded residue pointing by the canonical
spectral pointing on the same field and algebraic closure. -/
theorem LocalReciprocityFamily.map_spectralPointing
    (reciprocity : LocalReciprocityFamily.{u})
    (K : PointedMixedCharLocalField.{u}) (x : Kˣ) :
    (reciprocity.map K).toMonoidHom x =
      (reciprocity.map K.spectralPointing).toMonoidHom x := by
  let E := spectralPointingExtension K
  have hx := DFunLike.congr_fun (reciprocity.norm_naturality
    K K.spectralPointing E) x
  change (reciprocity.map K).toMonoidHom (E.norm x) =
    E.abelianizedGaloisMap
      ((reciprocity.map K.spectralPointing).toMonoidHom x) at hx
  rw [spectralPointingExtension_norm,
    spectralPointingExtension_abelianizedGaloisMap] at hx
  exact hx

end Anabelian.LCFT

namespace Anabelian.OTriangle

open LCFT

universe u

/-- Canonical spectral inertia in the absolute Galois group of the presentation. -/
noncomputable def LocalGaloisGroup.spectralInertiaSubgroup
    (G : LocalGaloisGroup.{u}) : Subgroup G.toProfiniteGrp :=
  ClassicalRamification.inertiaSubgroup G.presentation.spectralPointing

/-- Full inertia is the inverse image of abelianized inertia under the topological
abelianization map. -/
theorem ClassicalRamification.inertiaSubgroup_eq_comap_abelianized
    (K : PointedMixedCharLocalField.{u}) :
    ClassicalRamification.inertiaSubgroup K =
      Subgroup.comap
        (QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator (AbsoluteGaloisGroup K))))
        (LCFT.inertiaSubgroup K) := by
  rfl

/-- Local reciprocity identifies the residue action recorded by a pointing with the canonical
spectral residue action, at the level of their inertia kernels. -/
theorem ClassicalRamification.inertiaSubgroup_eq_spectralPointing
    (reciprocity : LocalReciprocityFamily.{u})
    (K : PointedMixedCharLocalField.{u}) :
    ClassicalRamification.inertiaSubgroup K =
      ClassicalRamification.inertiaSubgroup K.spectralPointing := by
  have hIab : LCFT.inertiaSubgroup K =
      LCFT.inertiaSubgroup K.spectralPointing := by
    ext y
    constructor
    · intro hy
      obtain ⟨u, hu⟩ := (reciprocity.map K).mapsUnits.unitsEquiv.surjective
        ⟨y, hy⟩
      have hKu := DFunLike.congr_fun
        (reciprocity.map K).mapsUnits.compatibility u
      have hSu := DFunLike.congr_fun
        (reciprocity.map K.spectralPointing).mapsUnits.compatibility u
      change ((reciprocity.map K).mapsUnits.unitsEquiv u :
        AbelianizedAbsoluteGaloisGroup K) =
          (reciprocity.map K).toMonoidHom
            (integerUnitsToFieldUnits K u) at hKu
      change ((reciprocity.map K.spectralPointing).mapsUnits.unitsEquiv u :
        AbelianizedAbsoluteGaloisGroup K.spectralPointing) =
          (reciprocity.map K.spectralPointing).toMonoidHom
            (integerUnitsToFieldUnits K.spectralPointing u) at hSu
      have hyrec : y = (reciprocity.map K).toMonoidHom
          (integerUnitsToFieldUnits K u) := by
        rw [← hKu, hu]
      rw [hyrec, reciprocity.map_spectralPointing]
      rw [show integerUnitsToFieldUnits K u =
        integerUnitsToFieldUnits K.spectralPointing u by rfl]
      rw [← hSu]
      exact ((reciprocity.map K.spectralPointing).mapsUnits.unitsEquiv u).property
    · intro hy
      obtain ⟨u, hu⟩ :=
        (reciprocity.map K.spectralPointing).mapsUnits.unitsEquiv.surjective
          ⟨y, hy⟩
      have hKu := DFunLike.congr_fun
        (reciprocity.map K).mapsUnits.compatibility u
      have hSu := DFunLike.congr_fun
        (reciprocity.map K.spectralPointing).mapsUnits.compatibility u
      change ((reciprocity.map K).mapsUnits.unitsEquiv u :
        AbelianizedAbsoluteGaloisGroup K) =
          (reciprocity.map K).toMonoidHom
            (integerUnitsToFieldUnits K u) at hKu
      change ((reciprocity.map K.spectralPointing).mapsUnits.unitsEquiv u :
        AbelianizedAbsoluteGaloisGroup K.spectralPointing) =
          (reciprocity.map K.spectralPointing).toMonoidHom
            (integerUnitsToFieldUnits K.spectralPointing u) at hSu
      have hyrec : y = (reciprocity.map K.spectralPointing).toMonoidHom
          (integerUnitsToFieldUnits K.spectralPointing u) := by
        rw [← hSu, hu]
      rw [hyrec, ← reciprocity.map_spectralPointing]
      rw [show integerUnitsToFieldUnits K.spectralPointing u =
        integerUnitsToFieldUnits K u by rfl]
      rw [← hKu]
      exact ((reciprocity.map K).mapsUnits.unitsEquiv u).property
  rw [ClassicalRamification.inertiaSubgroup_eq_comap_abelianized,
    ClassicalRamification.inertiaSubgroup_eq_comap_abelianized, hIab]
  have hcomm : Subgroup.topologicalClosure
      (commutator (AbsoluteGaloisGroup K)) =
      Subgroup.topologicalClosure
        (commutator (AbsoluteGaloisGroup K.spectralPointing)) := by
    rfl
  cases hcomm
  rfl

/-- The same comparison expressed in the profinite group carried by a local Galois-group
presentation. -/
theorem LocalGaloisGroup.classicalInertiaSubgroup_eq_spectral
    (G : LocalGaloisGroup.{u}) (reciprocity : LocalReciprocityFamily.{u}) :
    G.classicalInertiaSubgroup =
      G.spectralInertiaSubgroup :=
  ClassicalRamification.inertiaSubgroup_eq_spectralPointing
    reciprocity G.presentation

/-- A reciprocity image of a uniformizer admits a full Galois lift which is simultaneously
arithmetic Frobenius for the recorded residue pointing and for the canonical spectral pointing. -/
theorem LocalGaloisGroup.exists_commonFrobeniusLift
    (G : LocalGaloisGroup.{u}) (reciprocity : LocalReciprocityFamily.{u}) :
    ∃ sigma : G.toProfiniteGrp,
      G.classicalResidueGaloisMap sigma =
          residueFrobenius G.presentation ∧
        G.presentation.spectralResidueGaloisMap sigma =
          residueFrobenius G.presentation.spectralPointing := by
  let K := G.presentation
  let pi := uniformizerUnit K
  let y := (reciprocity.map K).toMonoidHom pi
  obtain ⟨sigma, hsigma⟩ := QuotientGroup.mk'_surjective
    (Subgroup.topologicalClosure (commutator G.toProfiniteGrp)) y
  have hrecorded := (reciprocity.map K).unramifiedProjection_uniformizer
    pi (uniformizerUnit_isUniformizer K)
  have hclassical : G.classicalResidueGaloisMap sigma = residueFrobenius K := by
    rw [← G.unramifiedProjection_toAbelianization]
    change unramifiedProjection K
      ((QuotientGroup.mk'
        (Subgroup.topologicalClosure (commutator G.toProfiniteGrp))) sigma) = _
    rw [hsigma]
    exact hrecorded
  let Gsp := LocalGaloisGroup.mk K.spectralPointing
  have hspectralRec :=
    (reciprocity.map K.spectralPointing).unramifiedProjection_uniformizer
      pi (uniformizerUnit_isUniformizer K)
  have hsigmaSp : Gsp.toAbelianization sigma =
      (reciprocity.map K.spectralPointing).toMonoidHom pi := by
    change (QuotientGroup.mk'
      (Subgroup.topologicalClosure (commutator G.toProfiniteGrp))) sigma = _
    rw [hsigma]
    exact reciprocity.map_spectralPointing K pi
  have hspectral : K.spectralResidueGaloisMap sigma =
      residueFrobenius K.spectralPointing := by
    change Gsp.classicalResidueGaloisMap sigma = _
    rw [← Gsp.unramifiedProjection_toAbelianization, hsigmaSp]
    exact hspectralRec
  exact ⟨sigma, hclassical, hspectral⟩

end Anabelian.OTriangle
