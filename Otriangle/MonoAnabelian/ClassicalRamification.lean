import Otriangle.MonoAnabelian.IntrinsicRamification

/-!
# Classical ramification objects

This module packages the classical inertia and Frobenius objects attached to the local-field
presentation of a `LocalGaloisGroup`.  It also proves that full inertia maps exactly onto the
abelianized inertia subgroup used by the one-field reconstruction.  The comparison with Hoshi's
intrinsic intersections is deliberately not assumed here.
-/

noncomputable section

open scoped commutatorElement

namespace Anabelian
namespace OTriangle
namespace ClassicalRamification

open LCFT

universe u

/-- Classical inertia in the full absolute Galois group: the kernel of the residue action. -/
noncomputable def inertiaSubgroup (K : PointedMixedCharLocalField.{u}) :
    Subgroup (AbsoluteGaloisGroup K) :=
  K.residueGaloisMap.ker

instance inertiaSubgroupNormal (K : PointedMixedCharLocalField.{u}) :
    (inertiaSubgroup K).Normal :=
  K.residueGaloisMap.normal_ker

/-- Passing a full Galois automorphism to the topological abelianization and then to the
unramified quotient is its residue action. -/
@[simp]
theorem unramifiedProjection_mk (K : PointedMixedCharLocalField.{u})
    (σ : AbsoluteGaloisGroup K) :
    unramifiedProjection K
        (QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator (AbsoluteGaloisGroup K))) σ) =
      K.residueGaloisMap σ :=
  rfl

/-- Full classical inertia maps exactly onto classical inertia in the topological
abelianization. -/
theorem map_inertiaSubgroup (K : PointedMixedCharLocalField.{u}) :
    (inertiaSubgroup K).map
        (QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator (AbsoluteGaloisGroup K)))) =
      LCFT.inertiaSubgroup K := by
  ext y
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    rw [← unramifiedProjection_eq_one_iff]
    change K.residueGaloisMap σ = 1
    exact hσ
  · intro hy
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk'_surjective
      (Subgroup.topologicalClosure (commutator (AbsoluteGaloisGroup K))) y
    refine ⟨σ, ?_, rfl⟩
    change K.residueGaloisMap σ = 1
    simpa only [unramifiedProjection_mk] using
      (unramifiedProjection_eq_one_iff K _).mpr hy

/-- The classical full unramified quotient. -/
abbrev inertiaQuotient (K : PointedMixedCharLocalField.{u}) : Type u :=
  AbsoluteGaloisGroup K ⧸ inertiaSubgroup K

/-- The full quotient by classical inertia is canonically the absolute Galois group of the
residue field. -/
noncomputable def inertiaQuotientEquivResidue (K : PointedMixedCharLocalField.{u}) :
    inertiaQuotient K ≃* ResidueAbsoluteGaloisGroup K :=
  QuotientGroup.quotientKerEquivOfSurjective K.residueGaloisMap
    K.residueGaloisMap_surjective

@[simp]
theorem inertiaQuotientEquivResidue_mk (K : PointedMixedCharLocalField.{u})
    (σ : AbsoluteGaloisGroup K) :
    inertiaQuotientEquivResidue K
        ((QuotientGroup.mk' (inertiaSubgroup K)) σ) =
      K.residueGaloisMap σ :=
  rfl

/-- The classical arithmetic Frobenius class in the full quotient by inertia. -/
noncomputable def frobeniusClass (K : PointedMixedCharLocalField.{u}) :
    inertiaQuotient K :=
  (inertiaQuotientEquivResidue K).symm (residueFrobenius K)

@[simp]
theorem inertiaQuotientEquivResidue_frobeniusClass
    (K : PointedMixedCharLocalField.{u}) :
    inertiaQuotientEquivResidue K (frobeniusClass K) = residueFrobenius K :=
  (inertiaQuotientEquivResidue K).apply_symm_apply _

/-- The full-to-abelian quotient map descends through the respective inertia subgroups. -/
noncomputable def inertiaQuotientToAbelianized (K : PointedMixedCharLocalField.{u}) :
    inertiaQuotient K →*
      (AbelianizedAbsoluteGaloisGroup K ⧸ LCFT.inertiaSubgroup K) :=
  QuotientGroup.map (inertiaSubgroup K) (LCFT.inertiaSubgroup K)
    (QuotientGroup.mk'
      (Subgroup.topologicalClosure (commutator (AbsoluteGaloisGroup K)))) (by
        rw [← Subgroup.map_le_iff_le_comap, map_inertiaSubgroup])

@[simp]
theorem inertiaQuotientToAbelianized_mk (K : PointedMixedCharLocalField.{u})
    (σ : AbsoluteGaloisGroup K) :
    inertiaQuotientToAbelianized K ((QuotientGroup.mk' (inertiaSubgroup K)) σ) =
      (QuotientGroup.mk' (LCFT.inertiaSubgroup K))
        (QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator (AbsoluteGaloisGroup K))) σ) :=
  rfl

/-- The full-to-abelian quotient map commutes with the two identifications of the unramified
quotient with the residue-field absolute Galois group. -/
theorem unramifiedQuotientEquiv_inertiaQuotientToAbelianized
    (K : PointedMixedCharLocalField.{u}) (x : inertiaQuotient K) :
    unramifiedQuotientEquiv K (inertiaQuotientToAbelianized K x) =
      inertiaQuotientEquivResidue K x := by
  induction x using Quotient.inductionOn with
  | _ σ => rfl

/-- In particular, full arithmetic Frobenius maps to arithmetic Frobenius in the abelianized
unramified quotient. -/
theorem unramifiedQuotientEquiv_frobeniusClass (K : PointedMixedCharLocalField.{u}) :
    unramifiedQuotientEquiv K
        (inertiaQuotientToAbelianized K (frobeniusClass K)) =
      residueFrobenius K := by
  rw [unramifiedQuotientEquiv_inertiaQuotientToAbelianized,
    inertiaQuotientEquivResidue_frobeniusClass]

end ClassicalRamification

namespace LocalGaloisGroup

/-- The classical residue action, with its domain expressed using the profinite-group structure
carried by a `LocalGaloisGroup`. -/
noncomputable def classicalResidueGaloisMap (G : LocalGaloisGroup.{u}) :
    G.toProfiniteGrp →* LCFT.ResidueAbsoluteGaloisGroup G.presentation where
  toFun := G.presentation.residueGaloisMap
  map_one' := map_one G.presentation.residueGaloisMap
  map_mul' := map_mul G.presentation.residueGaloisMap

theorem classicalResidueGaloisMap_surjective (G : LocalGaloisGroup.{u}) :
    Function.Surjective G.classicalResidueGaloisMap :=
  G.presentation.residueGaloisMap_surjective

/-- Classical inertia, expressed as a subgroup of the profinite group underlying a
`LocalGaloisGroup`. -/
noncomputable def classicalInertiaSubgroup (G : LocalGaloisGroup.{u}) :
    Subgroup G.toProfiniteGrp :=
  G.classicalResidueGaloisMap.ker

instance classicalInertiaSubgroupNormal (G : LocalGaloisGroup.{u}) :
    G.classicalInertiaSubgroup.Normal :=
  G.classicalResidueGaloisMap.normal_ker

/-- The classical unramified quotient, using the profinite-group presentation. -/
abbrev classicalInertiaQuotient (G : LocalGaloisGroup.{u}) : Type u :=
  G.toProfiniteGrp ⧸ G.classicalInertiaSubgroup

/-- The classical unramified quotient is the residue-field absolute Galois group. -/
noncomputable def classicalInertiaQuotientEquivResidue (G : LocalGaloisGroup.{u}) :
    G.classicalInertiaQuotient ≃*
      LCFT.ResidueAbsoluteGaloisGroup G.presentation :=
  QuotientGroup.quotientKerEquivOfSurjective G.classicalResidueGaloisMap
    G.classicalResidueGaloisMap_surjective

@[simp]
theorem classicalInertiaQuotientEquivResidue_mk (G : LocalGaloisGroup.{u})
    (σ : G.toProfiniteGrp) :
    G.classicalInertiaQuotientEquivResidue
        ((QuotientGroup.mk' G.classicalInertiaSubgroup) σ) =
      G.classicalResidueGaloisMap σ :=
  rfl

/-- The classical arithmetic Frobenius class, expressed in the profinite-group quotient. -/
noncomputable def classicalFrobeniusClass (G : LocalGaloisGroup.{u}) :
    G.classicalInertiaQuotient :=
  G.classicalInertiaQuotientEquivResidue.symm
    (LCFT.residueFrobenius G.presentation)

@[simp]
theorem classicalInertiaQuotientEquivResidue_frobeniusClass
    (G : LocalGaloisGroup.{u}) :
    G.classicalInertiaQuotientEquivResidue G.classicalFrobeniusClass =
      LCFT.residueFrobenius G.presentation :=
  G.classicalInertiaQuotientEquivResidue.apply_symm_apply _

/-- The canonical map from the profinite Galois group to the topological abelianization used by
its local-field presentation. -/
noncomputable def toAbelianization (G : LocalGaloisGroup.{u}) :
    G.toProfiniteGrp →* LCFT.AbelianizedAbsoluteGaloisGroup G.presentation :=
  QuotientGroup.mk'
    (Subgroup.topologicalClosure (commutator G.toProfiniteGrp))

@[simp]
theorem unramifiedProjection_toAbelianization (G : LocalGaloisGroup.{u})
    (σ : G.toProfiniteGrp) :
    LCFT.unramifiedProjection G.presentation (G.toAbelianization σ) =
      G.classicalResidueGaloisMap σ :=
  rfl

/-- Classical full inertia maps exactly onto the presentation's abelianized inertia when the
domain is expressed using the profinite-group structure. -/
theorem map_classicalInertiaSubgroup_toAbelianization (G : LocalGaloisGroup.{u}) :
    G.classicalInertiaSubgroup.map G.toAbelianization =
      LCFT.inertiaSubgroup G.presentation := by
  ext y
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    rw [← LCFT.unramifiedProjection_eq_one_iff]
    exact hσ
  · intro hy
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk'_surjective
      (Subgroup.topologicalClosure (commutator G.toProfiniteGrp)) y
    refine ⟨σ, ?_, rfl⟩
    change G.classicalResidueGaloisMap σ = 1
    exact (LCFT.unramifiedProjection_eq_one_iff G.presentation _).mpr hy

/-- The full-to-abelian map descends through classical inertia. -/
noncomputable def classicalInertiaQuotientToAbelianized (G : LocalGaloisGroup.{u}) :
    G.classicalInertiaQuotient →*
      (LCFT.AbelianizedAbsoluteGaloisGroup G.presentation ⧸
        LCFT.inertiaSubgroup G.presentation) :=
  QuotientGroup.map G.classicalInertiaSubgroup
    (LCFT.inertiaSubgroup G.presentation) G.toAbelianization (by
      rw [← Subgroup.map_le_iff_le_comap,
        G.map_classicalInertiaSubgroup_toAbelianization])

@[simp]
theorem classicalInertiaQuotientToAbelianized_mk (G : LocalGaloisGroup.{u})
    (σ : G.toProfiniteGrp) :
    G.classicalInertiaQuotientToAbelianized
        ((QuotientGroup.mk' G.classicalInertiaSubgroup) σ) =
      (QuotientGroup.mk' (LCFT.inertiaSubgroup G.presentation))
        (G.toAbelianization σ) :=
  rfl

/-- The profinite full-to-abelian quotient map commutes with identification with the residue-field
absolute Galois group. -/
theorem unramifiedQuotientEquiv_classicalInertiaQuotientToAbelianized
    (G : LocalGaloisGroup.{u}) (x : G.classicalInertiaQuotient) :
    LCFT.unramifiedQuotientEquiv G.presentation
        (G.classicalInertiaQuotientToAbelianized x) =
      G.classicalInertiaQuotientEquivResidue x := by
  induction x using Quotient.inductionOn with
  | _ σ => rfl

/-- The profinite presentation's full Frobenius class maps to arithmetic Frobenius in the
abelianized unramified quotient. -/
theorem unramifiedQuotientEquiv_classicalFrobeniusClass
    (G : LocalGaloisGroup.{u}) :
    LCFT.unramifiedQuotientEquiv G.presentation
        (G.classicalInertiaQuotientToAbelianized G.classicalFrobeniusClass) =
      LCFT.residueFrobenius G.presentation := by
  rw [G.unramifiedQuotientEquiv_classicalInertiaQuotientToAbelianized,
    G.classicalInertiaQuotientEquivResidue_frobeniusClass]

end LocalGaloisGroup
end OTriangle
end Anabelian
