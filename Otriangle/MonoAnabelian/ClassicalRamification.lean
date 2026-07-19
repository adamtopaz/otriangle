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
end OTriangle
end Anabelian
