import Otriangle.MonoAnabelian.DiagramTransport

/-!
# Compatibility of Hoshi transport with conjugation

This module compares the group-theoretic transport attached to an inner automorphism with the
fixed-field conjugation maps defining the reconstructed Galois action.
-/

noncomputable section

open CategoryTheory

namespace Anabelian
namespace OTriangle
namespace LocalGaloisGroup

open ValuativeRel

universe u

/-- Two choices of algebraic-closure comparison induce the same map after abelianization. -/
theorem topologicalAbelianization_mk_autCongr_eq
    {k A B : Type*} [Field k] [Field A] [Field B]
    [Algebra k A] [Algebra k B]
    (c d : A ≃ₐ[k] B) (θ : A ≃ₐ[k] A) :
    QuotientGroup.mk' (Subgroup.topologicalClosure (commutator (B ≃ₐ[k] B)))
        (AlgEquiv.autCongr c θ) =
      QuotientGroup.mk' (Subgroup.topologicalClosure (commutator (B ≃ₐ[k] B)))
        (AlgEquiv.autCongr d θ) := by
  let a : B ≃ₐ[k] B := d.symm.trans c
  have h : AlgEquiv.autCongr c θ =
      AlgEquiv.autCongr a (AlgEquiv.autCongr d θ) := by
    symm
    change ((AlgEquiv.autCongr d).trans (AlgEquiv.autCongr a)) θ =
      AlgEquiv.autCongr c θ
    rw [AlgEquiv.autCongr_trans]
    congr 2
    ext x
    simp [a]
  rw [h, topologicalAbelianization_mk_autCongr]

/-- Compute an abelianized Galois restriction using any chosen comparison of the two algebraic
closures.  Independence of that comparison is exactly inner-conjugacy in the target
abelianization. -/
theorem finiteExtension_abelianizedGaloisMap_mk_eq_of_equiv
    {K L : PointedMixedCharLocalField.{u}} (E : LCFT.FiniteExtension K L)
    (d : letI : Algebra K L := E.algebra
      letI : Algebra K L.algebraicClosure :=
        ((algebraMap L L.algebraicClosure).comp (algebraMap K L)).toAlgebra
      L.algebraicClosure ≃ₐ[K] K.algebraicClosure)
    (τL : LCFT.AbsoluteGaloisGroup L) (τK : LCFT.AbsoluteGaloisGroup K)
    (hd : letI : Algebra K L := E.algebra
      letI : Algebra K L.algebraicClosure :=
        ((algebraMap L L.algebraicClosure).comp (algebraMap K L)).toAlgebra
      letI : IsScalarTower K L L.algebraicClosure :=
        IsScalarTower.of_algebraMap_eq' rfl
      AlgEquiv.autCongr d (τL.restrictScalars K) = τK) :
    E.abelianizedGaloisMap
        (QuotientGroup.mk'
          (Subgroup.topologicalClosure
            (commutator (LCFT.AbsoluteGaloisGroup L))) τL) =
      QuotientGroup.mk'
        (Subgroup.topologicalClosure
          (commutator (LCFT.AbsoluteGaloisGroup K))) τK := by
  letI : Algebra K L := E.algebra
  letI : FiniteDimensional K L := E.finiteDimensional
  letI : Algebra K L.algebraicClosure :=
    ((algebraMap L L.algebraicClosure).comp (algebraMap K L)).toAlgebra
  letI : IsScalarTower K L L.algebraicClosure := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsAlgClosure K L.algebraicClosure :=
    IsAlgClosure.ofAlgebraic K L L.algebraicClosure
  let c : L.algebraicClosure ≃ₐ[K] K.algebraicClosure :=
    IsAlgClosure.equiv K L.algebraicClosure K.algebraicClosure
  rw [LCFT.FiniteExtension.abelianizedGaloisMap_mk]
  change QuotientGroup.mk'
      (Subgroup.topologicalClosure
        (commutator (LCFT.AbsoluteGaloisGroup K)))
      (AlgEquiv.autCongr c (τL.restrictScalars K)) = _
  calc
    _ = QuotientGroup.mk'
        (Subgroup.topologicalClosure
          (commutator (LCFT.AbsoluteGaloisGroup K)))
        (AlgEquiv.autCongr d (τL.restrictScalars K)) :=
      topologicalAbelianization_mk_autCongr_eq c d _
    _ = _ := congrArg _ hd

variable (G : LocalGaloisGroup.{u})

/-- Conjugate fixed fields are isomorphic valued extensions.  We regard the conjugating field
equivalence as a degree-one finite extension so that the transfer naturality axiom can be applied
to it. -/
noncomputable def fixedFieldConjugationFiniteExtension
    (σ : G.toProfiniteGrp) (U : G.OpenSubgroupIndex) :
    LCFT.FiniteExtension (G.fixedFieldPointed U)
      (G.fixedFieldPointed (G.conjugationIndex σ U)) := by
  let e := G.fixedFieldConjugationEquiv σ U
  letI := G.presentation.nontriviallyNormedField
  letI := G.presentation.isUltrametricDist
  letI := G.presentation.completeSpace
  letI := G.fixedFieldNontriviallyNormedField U
  letI := G.fixedFieldIsUltrametricDist U
  letI : ValuativeRel (G.fixedField U) := G.fixedFieldValuativeRel U
  letI := G.fixedFieldNontriviallyNormedField (G.conjugationIndex σ U)
  letI := G.fixedFieldIsUltrametricDist (G.conjugationIndex σ U)
  letI : ValuativeRel (G.fixedField (G.conjugationIndex σ U)) :=
    G.fixedFieldValuativeRel (G.conjugationIndex σ U)
  letI : Algebra (G.fixedField U) (G.fixedField (G.conjugationIndex σ U)) :=
    e.toRingHom.toAlgebra
  let eLinear : G.fixedField U ≃ₗ[G.fixedField U]
      G.fixedField (G.conjugationIndex σ U) :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        intro c x
        change e (c * x) = e c * e x
        exact e.map_mul c x }
  letI : FiniteDimensional (G.fixedField U)
      (G.fixedField (G.conjugationIndex σ U)) :=
    Module.Finite.equiv eLinear
  letI : ValuativeExtension (G.fixedField U)
      (G.fixedField (G.conjugationIndex σ U)) := by
    constructor
    intro a b
    change spectralNorm G.presentation
        (G.fixedField (G.conjugationIndex σ U)) (e a) ≤
          spectralNorm G.presentation
            (G.fixedField (G.conjugationIndex σ U)) (e b) ↔
      spectralNorm G.presentation (G.fixedField U) a ≤
        spectralNorm G.presentation (G.fixedField U) b
    rw [SpectralLocalField.spectralNorm_eq_of_algEquiv e a,
      SpectralLocalField.spectralNorm_eq_of_algEquiv e b]
  exact
    { algebra := inferInstance
      finiteDimensional := inferInstance
      valuativeExtension := inferInstance }

@[simp]
theorem fixedFieldConjugationFiniteExtension_algebraMap
    (σ : G.toProfiniteGrp) (U : G.OpenSubgroupIndex)
    (x : G.fixedField U) :
    let E := G.fixedFieldConjugationFiniteExtension σ U
    @algebraMap (G.fixedField U) (G.fixedField (G.conjugationIndex σ U))
        _ _ E.algebra x = G.fixedFieldConjugationEquiv σ U x := by
  rfl

/-- Restriction along the identity fixed-field extension is the identity after
abelianization. -/
theorem fixedFieldFiniteExtension_refl_abelianizedGaloisMap
    (U : G.OpenSubgroupIndex) :
    (G.fixedFieldFiniteExtension (U := U) (V := U) le_rfl).abelianizedGaloisMap =
      MonoidHom.id (LCFT.AbelianizedAbsoluteGaloisGroup
        (G.fixedFieldPointed U)) := by
  ext x
  let τ : (OrderDual.ofDual U).toSubgroup :=
    (G.fixedFieldGaloisContinuousEquiv U).symm x
  have hx : G.fixedFieldGaloisContinuousEquiv U τ = x :=
    (G.fixedFieldGaloisContinuousEquiv U).apply_symm_apply x
  rw [← hx]
  change (G.fixedFieldFiniteExtension (U := U) (V := U) le_rfl).abelianizedGaloisMap
      (QuotientGroup.mk'
        (Subgroup.topologicalClosure
          (commutator (LCFT.AbsoluteGaloisGroup (G.fixedFieldPointed U))))
        (G.fixedFieldGaloisContinuousEquiv U τ)) = _
  rw [G.fixedField_abelianizedGaloisMap_mk le_rfl τ]
  congr 2

/-- On the common algebraic closure, fixed-field Galois transport along inner conjugation is
literal conjugation. -/
theorem fixedFieldGroupHom_conjugation_apply
    (σ : G.toProfiniteGrp) (U : G.OpenSubgroupIndex)
    (τ : LCFT.AbsoluteGaloisGroup (G.fixedFieldPointed U))
    (x : G.presentation.algebraicClosure) :
    (show G.presentation.algebraicClosure ≃ₐ[
        G.fixedField (G.conjugationIndex σ U)] G.presentation.algebraicClosure from
      (G.fixedFieldGroupHom (G.conjugationHom σ) U).equiv τ) x =
      G.galoisElementAlgEquiv σ
        (τ ((G.galoisElementAlgEquiv σ).symm x)) := by
  rfl

/-- The canonical comparison of the two common algebraic closures for the degree-one
conjugation extension is application of the inverse Galois element. -/
noncomputable def fixedFieldConjugationAlgebraicClosureEquiv
    (σ : G.toProfiniteGrp) (U : G.OpenSubgroupIndex) :
    let E := G.fixedFieldConjugationFiniteExtension σ U
    let sourceAlgebra : Algebra (G.fixedField U)
        (G.fixedFieldPointed (G.conjugationIndex σ U)).algebraicClosure :=
      (((@algebraMap (G.fixedField (G.conjugationIndex σ U))
        (G.fixedFieldPointed (G.conjugationIndex σ U)).algebraicClosure
        _ _ (G.fixedFieldPointed (G.conjugationIndex σ U)).algebra).comp
        (@algebraMap (G.fixedField U)
          (G.fixedField (G.conjugationIndex σ U)) _ _ E.algebra))).toAlgebra
    @AlgEquiv (G.fixedField U)
      (G.fixedFieldPointed (G.conjugationIndex σ U)).algebraicClosure
      (G.fixedFieldPointed U).algebraicClosure _ _ _
      sourceAlgebra (G.fixedFieldPointed U).algebra := by
  let E := G.fixedFieldConjugationFiniteExtension σ U
  let sourceAlgebra : Algebra (G.fixedField U)
      (G.fixedFieldPointed (G.conjugationIndex σ U)).algebraicClosure :=
    (((@algebraMap (G.fixedField (G.conjugationIndex σ U))
      (G.fixedFieldPointed (G.conjugationIndex σ U)).algebraicClosure
      _ _ (G.fixedFieldPointed (G.conjugationIndex σ U)).algebra).comp
      (@algebraMap (G.fixedField U)
        (G.fixedField (G.conjugationIndex σ U)) _ _ E.algebra))).toAlgebra
  exact @AlgEquiv.mk (G.fixedField U)
    (G.fixedFieldPointed (G.conjugationIndex σ U)).algebraicClosure
    (G.fixedFieldPointed U).algebraicClosure _ _ _
    sourceAlgebra (G.fixedFieldPointed U).algebra
    (G.galoisElementAlgEquiv σ).symm.toEquiv
    (fun x y ↦ (G.galoisElementAlgEquiv σ).symm.map_mul x y)
    (fun x y ↦ (G.galoisElementAlgEquiv σ).symm.map_add x y)
    (by
      intro x
      have hxsource :
          @algebraMap (G.fixedField U)
              (G.fixedFieldPointed (G.conjugationIndex σ U)).algebraicClosure
              _ _ sourceAlgebra x =
            G.galoisElementAlgEquiv σ x := by
        rfl
      have hxtarget :
          @algebraMap (G.fixedField U) (G.fixedFieldPointed U).algebraicClosure
              _ _ (G.fixedFieldPointed U).algebra x = x := by
        exact G.fixedFieldPointed_algebraMap_apply U x
      rw [hxsource, hxtarget]
      exact (G.galoisElementAlgEquiv σ).symm_apply_apply x)

/-- Restriction along the degree-one conjugation extension is inverse to the abelianized
fixed-field transport induced by inner conjugation. -/
theorem fixedFieldConjugationFiniteExtension_abelianizedGaloisMap_comp
    (σ : G.toProfiniteGrp) (U : G.OpenSubgroupIndex) :
    (G.fixedFieldConjugationFiniteExtension σ U).abelianizedGaloisMap.comp
        (G.fixedFieldAbelianizationEquiv (G.conjugationHom σ) U).toMonoidHom =
      MonoidHom.id (LCFT.AbelianizedAbsoluteGaloisGroup
        (G.fixedFieldPointed U)) := by
  ext τ
  change (G.fixedFieldConjugationFiniteExtension σ U).abelianizedGaloisMap
      (G.fixedFieldAbelianizationEquiv (G.conjugationHom σ) U
        (QuotientGroup.mk'
          (Subgroup.topologicalClosure
            (commutator (LCFT.AbsoluteGaloisGroup (G.fixedFieldPointed U)))) τ)) =
    QuotientGroup.mk'
      (Subgroup.topologicalClosure
        (commutator (LCFT.AbsoluteGaloisGroup (G.fixedFieldPointed U)))) τ
  rw [fixedFieldAbelianizationEquiv_mk]
  let E := G.fixedFieldConjugationFiniteExtension σ U
  refine finiteExtension_abelianizedGaloisMap_mk_eq_of_equiv E
    (G.fixedFieldConjugationAlgebraicClosureEquiv σ U)
    ((G.fixedFieldGroupHom (G.conjugationHom σ) U).equiv τ) τ ?_
  apply AlgEquiv.ext
  intro x
  change (G.galoisElementAlgEquiv σ).symm
      ((show G.presentation.algebraicClosure ≃ₐ[
          G.fixedField (G.conjugationIndex σ U)]
          G.presentation.algebraicClosure from
        (G.fixedFieldGroupHom (G.conjugationHom σ) U).equiv τ)
        (G.galoisElementAlgEquiv σ x)) = τ x
  rw [G.fixedFieldGroupHom_conjugation_apply σ U τ]
  simp

/-- Local reciprocity is equivariant for the field equivalence induced by conjugating a fixed
field inside the common algebraic closure. -/
theorem fixedField_reciprocity_conjugation
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (σ : G.toProfiniteGrp) (U : G.OpenSubgroupIndex)
    (a : (G.fixedField U)ˣ) :
    G.fixedFieldAbelianizationEquiv (G.conjugationHom σ) U
        ((reciprocity.map (G.fixedFieldPointed U)).toMonoidHom a) =
      (reciprocity.map (G.fixedFieldPointed (G.conjugationIndex σ U))).toMonoidHom
        ((G.fixedFieldConjugationFiniteExtension σ U).fieldUnitsMap a) := by
  let K := G.fixedFieldPointed U
  let L := G.fixedFieldPointed (G.conjugationIndex σ U)
  let E₀ := G.fixedFieldFiniteExtension (U := U) (V := U) le_rfl
  let E := G.fixedFieldConjugationFiniteExtension σ U
  let eL := G.fixedFieldAbelianizationEquiv (G.conjugationHom σ) U
  have hrestriction :
      (MulEquiv.refl (LCFT.AbelianizedAbsoluteGaloisGroup K)).toMonoidHom.comp
          E₀.abelianizedGaloisMap =
        E.abelianizedGaloisMap.comp eL.toMonoidHom := by
    rw [G.fixedFieldFiniteExtension_refl_abelianizedGaloisMap U,
      G.fixedFieldConjugationFiniteExtension_abelianizedGaloisMap_comp σ U]
    ext y
    rfl
  have htransport := reciprocity.transfer_equiv_naturality K K K L E₀ E
    (MulEquiv.refl (LCFT.AbelianizedAbsoluteGaloisGroup K)) eL hrestriction
  have hrefl := DFunLike.congr_fun (reciprocity.transfer_naturality K K E₀) a
  have hconj := DFunLike.congr_fun (reciprocity.transfer_naturality K L E) a
  have hE₀ : E₀.fieldUnitsMap a = a := by
    apply Units.ext
    rfl
  have hrefl' : reciprocity.transferMap K K E₀
      ((reciprocity.map K).toMonoidHom a) =
        (reciprocity.map K).toMonoidHom a := by
    simpa only [MonoidHom.comp_apply, hE₀] using hrefl
  have hconj' : reciprocity.transferMap K L E
      ((reciprocity.map K).toMonoidHom a) =
        (reciprocity.map L).toMonoidHom (E.fieldUnitsMap a) := by
    simpa only [MonoidHom.comp_apply] using hconj
  have hx := DFunLike.congr_fun htransport
    ((reciprocity.map K).toMonoidHom a)
  change eL (reciprocity.transferMap K K E₀
      ((reciprocity.map K).toMonoidHom a)) =
    reciprocity.transferMap K L E ((reciprocity.map K).toMonoidHom a) at hx
  change eL ((reciprocity.map K).toMonoidHom a) =
    (reciprocity.map L).toMonoidHom (E.fieldUnitsMap a)
  calc
    eL ((reciprocity.map K).toMonoidHom a) =
        eL (reciprocity.transferMap K K E₀
          ((reciprocity.map K).toMonoidHom a)) := congrArg eL hrefl'.symm
    _ = reciprocity.transferMap K L E
          ((reciprocity.map K).toMonoidHom a) := hx
    _ = (reciprocity.map L).toMonoidHom (E.fieldUnitsMap a) := hconj'

/-- On the intrinsic Frobenius-positive cone, transfer along the degree-one conjugation
extension is precisely abelianized subgroup conjugation. -/
theorem fixedFieldAbelianizationEquiv_conjugation_eq_transfer
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (σ : G.toProfiniteGrp) (U : G.OpenSubgroupIndex)
    (x : reciprocity.reconstructedBaseIntegerMonoid (G.fixedFieldPointed U)) :
    G.fixedFieldAbelianizationEquiv (G.conjugationHom σ) U x.1 =
      reciprocity.transferMap (G.fixedFieldPointed U)
        (G.fixedFieldPointed (G.conjugationIndex σ U))
        (G.fixedFieldConjugationFiniteExtension σ U) x.1 := by
  let K := G.fixedFieldPointed U
  let L := G.fixedFieldPointed (G.conjugationIndex σ U)
  let E₀ := G.fixedFieldFiniteExtension (U := U) (V := U) le_rfl
  let E := G.fixedFieldConjugationFiniteExtension σ U
  let eL := G.fixedFieldAbelianizationEquiv (G.conjugationHom σ) U
  have hrestriction :
      (MulEquiv.refl (LCFT.AbelianizedAbsoluteGaloisGroup K)).toMonoidHom.comp
          E₀.abelianizedGaloisMap =
        E.abelianizedGaloisMap.comp eL.toMonoidHom := by
    rw [G.fixedFieldFiniteExtension_refl_abelianizedGaloisMap U,
      G.fixedFieldConjugationFiniteExtension_abelianizedGaloisMap_comp σ U]
    ext y
    rfl
  have htransfer := reciprocity.transfer_equiv_naturality K K K L E₀ E
    (MulEquiv.refl (LCFT.AbelianizedAbsoluteGaloisGroup K)) eL hrestriction
  have hrefl : reciprocity.reconstructedBaseIntegerMonoidMap E₀ x = x := by
    change (G.fixedFieldFiniteExtensionSystem).reconstructedTransition
      reciprocity U U le_rfl x = x
    exact DirectedSystem.map_self'
      (fun i j h ↦ (G.fixedFieldFiniteExtensionSystem).reconstructedTransition
        reciprocity i j h) x
  have htransferRefl : reciprocity.transferMap K K E₀ x.1 = x.1 := by
    rw [← reciprocity.reconstructedBaseIntegerMonoidMap_coe E₀ x]
    exact congrArg Subtype.val hrefl
  have hx := DFunLike.congr_fun htransfer x.1
  change eL (reciprocity.transferMap K K E₀ x.1) =
    reciprocity.transferMap K L E x.1 at hx
  rw [htransferRefl] at hx
  exact hx

/-- The field-theoretic conjugation of a reconstructed node is the reconstructed map attached to
the degree-one conjugation extension. -/
theorem reconstructedNodeConjugationEquiv_eq_conjugationExtensionMap
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (σ : G.toProfiniteGrp) (U : G.OpenSubgroupIndex)
    (x : (G.fixedFieldFiniteExtensionSystem).reconstructedNode reciprocity U) :
    G.reconstructedNodeConjugationEquiv reciprocity σ U x =
      reciprocity.reconstructedBaseIntegerMonoidMap
        (G.fixedFieldConjugationFiniteExtension σ U) x := by
  apply Subtype.ext
  rfl

/-- Hoshi transport along an inner automorphism agrees with the node map defining the intrinsic
reconstructed Galois action. -/
theorem fixedFieldReconstructedNodeEquiv_conjugation
    (reciprocity : LCFT.LocalReciprocityFamily.{u})
    (hoshi : HoshiRamificationComparisonFamily.{u})
    (σ : G.toProfiniteGrp) (U : G.OpenSubgroupIndex) :
    fixedFieldReconstructedNodeEquiv (G.conjugationHom σ) U reciprocity hoshi =
      G.reconstructedNodeConjugationEquiv reciprocity σ U := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rw [fixedFieldReconstructedNodeEquiv_apply_coe]
  have hconj := congrArg Subtype.val
    (G.reconstructedNodeConjugationEquiv_eq_conjugationExtensionMap
      reciprocity σ U x)
  change G.fixedFieldAbelianizationEquiv (G.conjugationHom σ) U x.1 =
    (G.reconstructedNodeConjugationEquiv reciprocity σ U x).1
  rw [hconj, reciprocity.reconstructedBaseIntegerMonoidMap_coe]
  exact G.fixedFieldAbelianizationEquiv_conjugation_eq_transfer reciprocity σ U x

/-- Inner conjugation is natural under every morphism of local Galois groups. -/
theorem conjugationHom_natural {H : LocalGaloisGroup.{u}} (f : G ⟶ H)
    (σ : G.toProfiniteGrp) :
    G.conjugationHom σ ≫ f = f ≫ H.conjugationHom (f.equiv σ) := by
  apply LocalGaloisGroup.Hom.ext
  apply ContinuousMulEquiv.ext
  intro τ
  change f.equiv (σ * τ * σ⁻¹) =
    f.equiv σ * f.equiv τ * (f.equiv σ)⁻¹
  simp only [map_mul, map_inv]

end LocalGaloisGroup
end OTriangle
end Anabelian
