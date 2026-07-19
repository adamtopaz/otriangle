import Otriangle.MonoAnabelian.UniformizerKummerExtension
import Otriangle.MonoAnabelian.TameKummerRamification

/-!
# Ramification of Kummer extensions for a specified uniformizer

This is the ramification-theoretic companion to `UniformizerKummerExtension`.  Its hypotheses say
directly that the selected integer generates the maximal ideal, which is stable under unramified
base change.
-/

noncomputable section

namespace Anabelian.LCFT

open OTriangle ValuativeRel Polynomial
open OTriangle.FiniteTameRamification

universe u

theorem uniformizer_ne_zero
    (K : PointedMixedCharLocalField.{u}) (pi : LocalIntegerRing K)
    (hpi : Ideal.span {pi} = localMaximalIdeal K) : pi ≠ 0 := by
  intro hzero
  apply localMaximalIdeal_ne_bot K
  rw [← hpi, hzero, Ideal.span_singleton_eq_bot]

/-- The normal open subgroup fixing the specified-uniformizer Kummer field. -/
noncomputable def uniformizerKummerOpenSubgroup
    (K : PointedMixedCharLocalField.{u}) (pi : LocalIntegerRing K)
    (hpi : Ideal.span {pi} = localMaximalIdeal K)
    (n : ℕ) (hn : 0 < n) :
    OpenSubgroup (OTriangle.LocalGaloisGroup.mk K).toProfiniteGrp := by
  let L := uniformizerKummerFiniteGaloisIntermediateField K pi
    (uniformizer_ne_zero K pi hpi) n hn
  exact ⟨L.toIntermediateField.fixingSubgroup,
    L.toIntermediateField.fixingSubgroup_isOpen⟩

theorem uniformizerKummerOpenSubgroup_normal
    (K : PointedMixedCharLocalField.{u}) (pi : LocalIntegerRing K)
    (hpi : Ideal.span {pi} = localMaximalIdeal K)
    (n : ℕ) (hn : 0 < n) :
    (uniformizerKummerOpenSubgroup K pi hpi n hn).toSubgroup.Normal := by
  let L := uniformizerKummerFiniteGaloisIntermediateField K pi
    (uniformizer_ne_zero K pi hpi) n hn
  change L.toIntermediateField.fixingSubgroup.Normal
  infer_instance

theorem uniformizerKummer_fixedField_eq
    (K : PointedMixedCharLocalField.{u}) (pi : LocalIntegerRing K)
    (hpi : Ideal.span {pi} = localMaximalIdeal K)
    (n : ℕ) (hn : 0 < n) :
    let G := OTriangle.LocalGaloisGroup.mk K
    G.fixedField (OrderDual.toDual
      (uniformizerKummerOpenSubgroup K pi hpi n hn)) =
        uniformizerKummerIntermediateField K pi n := by
  let G := OTriangle.LocalGaloisGroup.mk K
  let L := uniformizerKummerFiniteGaloisIntermediateField K pi
    (uniformizer_ne_zero K pi hpi) n hn
  change IntermediateField.fixedField L.toIntermediateField.fixingSubgroup =
    uniformizerKummerIntermediateField K pi n
  rw [InfiniteGalois.fixedField_fixingSubgroup]
  rfl

noncomputable def uniformizerKummerFixedFieldEquiv
    (K : PointedMixedCharLocalField.{u}) (pi : LocalIntegerRing K)
    (hpi : Ideal.span {pi} = localMaximalIdeal K)
    (n : ℕ) (hn : 0 < n) :
    let G := OTriangle.LocalGaloisGroup.mk K
    G.fixedField (OrderDual.toDual
      (uniformizerKummerOpenSubgroup K pi hpi n hn)) ≃ₐ[K]
        uniformizerKummerIntermediateField K pi n :=
  IntermediateField.equivOfEq (uniformizerKummer_fixedField_eq K pi hpi n hn)

/-- The distinguished root transported to the literal fixed field. -/
noncomputable def uniformizerKummerFixedRoot
    (K : PointedMixedCharLocalField.{u}) (pi : LocalIntegerRing K)
    (hpi : Ideal.span {pi} = localMaximalIdeal K)
    (n : ℕ) (hn : 0 < n) :
    let G := OTriangle.LocalGaloisGroup.mk K
    G.fixedField (OrderDual.toDual
      (uniformizerKummerOpenSubgroup K pi hpi n hn)) := by
  letI : NeZero n := ⟨hn.ne'⟩
  exact (uniformizerKummerFixedFieldEquiv K pi hpi n hn).symm
    (uniformizerKummerRoot K pi n)

theorem uniformizerKummerFixedRoot_pow
    (K : PointedMixedCharLocalField.{u}) (pi : LocalIntegerRing K)
    (hpi : Ideal.span {pi} = localMaximalIdeal K)
    (n : ℕ) (hn : 0 < n) :
    let G := OTriangle.LocalGaloisGroup.mk K
    let V : G.OpenSubgroupIndex := OrderDual.toDual
      (uniformizerKummerOpenSubgroup K pi hpi n hn)
    uniformizerKummerFixedRoot K pi hpi n hn ^ n =
      algebraMap K (G.fixedField V) (pi : K) := by
  letI : NeZero n := ⟨hn.ne'⟩
  let e := uniformizerKummerFixedFieldEquiv K pi hpi n hn
  apply e.injective
  simp only [map_pow, e.apply_symm_apply, e.commutes]
  exact uniformizerKummerRoot_pow K pi n

/-- The fixed root as an element of the spectral valuation ring. -/
noncomputable def uniformizerKummerFixedIntegerRoot
    (K : PointedMixedCharLocalField.{u}) (pi : LocalIntegerRing K)
    (hpi : Ideal.span {pi} = localMaximalIdeal K)
    (n : ℕ) (hn : 0 < n) :
    let G := OTriangle.LocalGaloisGroup.mk K
    let V : G.OpenSubgroupIndex := OrderDual.toDual
      (uniformizerKummerOpenSubgroup K pi hpi n hn)
    LocalIntegerRing (G.fixedFieldPointed V) := by
  let G := OTriangle.LocalGaloisGroup.mk K
  let V : G.OpenSubgroupIndex := OrderDual.toDual
    (uniformizerKummerOpenSubgroup K pi hpi n hn)
  let L := G.fixedFieldPointed V
  let E := G.fixedFieldBaseExtension V
  letI := G.presentation.nontriviallyNormedField
  letI := G.presentation.isUltrametricDist
  letI := G.presentation.completeSpace
  letI := G.fixedFieldNontriviallyNormedField V
  letI := G.fixedFieldIsUltrametricDist V
  letI : ValuativeRel L := G.fixedFieldValuativeRel V
  letI : Algebra K (G.fixedField V) := E.algebra
  letI : ValuativeExtension K (G.fixedField V) := E.valuativeExtension
  letI : IsScalarTower (LocalIntegerRing K) 𝒪[G.fixedField V]
      (G.fixedField V) := IsScalarTower.of_algebraMap_eq' rfl
  let f : (LocalIntegerRing K)[X] := X ^ n - C pi
  have hintegral : IsIntegral (LocalIntegerRing K)
      (uniformizerKummerFixedRoot K pi hpi n hn) := by
    refine ⟨f, monic_X_pow_sub_C _ hn.ne', ?_⟩
    change Polynomial.aeval (uniformizerKummerFixedRoot K pi hpi n hn) f = 0
    rw [aeval_def, eval₂_sub, eval₂_X_pow, eval₂_C]
    change uniformizerKummerFixedRoot K pi hpi n hn ^ n -
      algebraMap (LocalIntegerRing K) (G.fixedField V) pi = 0
    rw [uniformizerKummerFixedRoot_pow]
    exact sub_self _
  exact ⟨uniformizerKummerFixedRoot K pi hpi n hn,
    Valuation.Integers.mem_of_integral
      (Valuation.integer.integers (valuation L)) hintegral.tower_top⟩

/-- The cyclic Kummer generator transported to the literal fixed field. -/
noncomputable def uniformizerKummerFixedGeneratorAutomorphism
    (K : PointedMixedCharLocalField.{u}) (pi : LocalIntegerRing K)
    (hpi : Ideal.span {pi} = localMaximalIdeal K)
    (n : ℕ) (hn : 0 < n) (hroot : (primitiveRoots n K).Nonempty) :
    let G := OTriangle.LocalGaloisGroup.mk K
    let V : G.OpenSubgroupIndex := OrderDual.toDual
      (uniformizerKummerOpenSubgroup K pi hpi n hn)
    G.fixedField V ≃ₐ[K] G.fixedField V :=
  (AlgEquiv.autCongr (uniformizerKummerFixedFieldEquiv K pi hpi n hn)).symm
    (uniformizerKummerGeneratorAutomorphism K pi hpi n hn hroot)

theorem uniformizerKummerFixedGeneratorAutomorphism_apply_root
    (K : PointedMixedCharLocalField.{u}) (pi : LocalIntegerRing K)
    (hpi : Ideal.span {pi} = localMaximalIdeal K)
    (n : ℕ) (hn : 0 < n) (hroot : (primitiveRoots n K).Nonempty) :
    let G := OTriangle.LocalGaloisGroup.mk K
    let V : G.OpenSubgroupIndex := OrderDual.toDual
      (uniformizerKummerOpenSubgroup K pi hpi n hn)
    uniformizerKummerFixedGeneratorAutomorphism K pi hpi n hn hroot
        (uniformizerKummerFixedRoot K pi hpi n hn) =
      algebraMap K (G.fixedField V) hroot.choose *
        uniformizerKummerFixedRoot K pi hpi n hn := by
  letI : NeZero n := ⟨hn.ne'⟩
  let e := uniformizerKummerFixedFieldEquiv K pi hpi n hn
  apply e.injective
  change uniformizerKummerGeneratorAutomorphism K pi hpi n hn hroot
      (uniformizerKummerRoot K pi n) =
    algebraMap K (uniformizerKummerIntermediateField K pi n) hroot.choose *
      uniformizerKummerRoot K pi n
  exact uniformizerKummerGeneratorAutomorphism_apply_root K pi hpi n hn hroot

/-- The specified-uniformizer Kummer extension is totally ramified of degree `n`. -/
theorem uniformizerKummer_relativeRamificationIndex_eq
    (K : PointedMixedCharLocalField.{u}) (pi : LocalIntegerRing K)
    (hpi : Ideal.span {pi} = localMaximalIdeal K)
    (n : ℕ) (hn : 0 < n) (hroot : (primitiveRoots n K).Nonempty) :
    let G := OTriangle.LocalGaloisGroup.mk K
    let U := uniformizerKummerOpenSubgroup K pi hpi n hn
    (G.fixedFieldBaseExtension (OrderDual.toDual U)).relativeRamificationIndex = n := by
  let G := OTriangle.LocalGaloisGroup.mk K
  let U := uniformizerKummerOpenSubgroup K pi hpi n hn
  let V : G.OpenSubgroupIndex := OrderDual.toDual U
  let L := G.fixedFieldPointed V
  let E := G.fixedFieldBaseExtension V
  letI : NeZero n := ⟨hn.ne'⟩
  letI := G.presentation.nontriviallyNormedField
  letI := G.presentation.isUltrametricDist
  letI := G.presentation.completeSpace
  letI := G.fixedFieldNontriviallyNormedField V
  letI := G.fixedFieldIsUltrametricDist V
  letI : ValuativeRel L := G.fixedFieldValuativeRel V
  letI : TopologicalSpace L := G.fixedFieldTopologicalSpace V
  letI : IsNonarchimedeanLocalField L := G.fixedFieldIsNonarchimedeanLocalField V
  letI : Algebra K L := E.algebra
  letI : ValuativeExtension K L := E.valuativeExtension
  letI : FiniteDimensional K L := E.finiteDimensional
  letI : Algebra.IsAlgebraic K L := by infer_instance
  letI : IsGalois K (G.fixedField V) := G.fixedField_isGalois_of_normal U
    (uniformizerKummerOpenSubgroup_normal K pi hpi n hn)
  letI : IsScalarTower G.presentation G.presentation (G.fixedField V) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : MulSemiringAction
      ((G.fixedField V) ≃ₐ[G.presentation] (G.fixedField V)) 𝒪[G.fixedField V] :=
    SpectralLocalField.integerMulSemiringAction
      G.presentation G.presentation (G.fixedField V)
  let hfield : G.fixedField V = uniformizerKummerIntermediateField K pi n :=
    uniformizerKummer_fixedField_eq K pi hpi n hn
  have hfinrank : Module.finrank K L = n := by
    change Module.finrank K (G.fixedField V) = n
    rw [hfield]
    exact uniformizerKummerIntermediateField_finrank K pi hpi n hn hroot
  let alpha : L := ⟨(uniformizerKummerRoot K pi n : K.algebraicClosure), by
    rw [hfield]
    exact (uniformizerKummerRoot K pi n).property⟩
  have halpha_pow : alpha ^ n = algebraMap K L (pi : K) := by
    apply Subtype.ext
    change (uniformizerKummerRoot K pi n : K.algebraicClosure) ^ n =
      algebraMap K K.algebraicClosure (pi : K)
    exact congrArg Subtype.val (uniformizerKummerRoot_pow K pi n)
  have halpha_integral : IsIntegral (LocalIntegerRing K) alpha := by
    let f : (LocalIntegerRing K)[X] := X ^ n - C pi
    refine ⟨f, monic_X_pow_sub_C _ hn.ne', ?_⟩
    change Polynomial.aeval alpha f = 0
    rw [aeval_def, eval₂_sub, eval₂_X_pow, eval₂_C]
    change alpha ^ n - algebraMap (LocalIntegerRing K) L pi = 0
    rw [halpha_pow]
    apply sub_eq_zero.mpr
    rfl
  let alphaO : LocalIntegerRing L :=
    ⟨alpha, Valuation.Integers.mem_of_integral
      (Valuation.integer.integers (valuation L)) halpha_integral.tower_top⟩
  have halphaO_pow : alphaO ^ n =
      algebraMap (LocalIntegerRing K) (LocalIntegerRing L) pi := by
    apply Subtype.ext
    exact halpha_pow
  have hpimem : pi ∈ localMaximalIdeal K := by
    rw [← hpi]
    exact Ideal.mem_span_singleton.mpr (dvd_refl _)
  have hpimap : algebraMap (LocalIntegerRing K) (LocalIntegerRing L) pi ∈
      localMaximalIdeal L := by
    exact IsLocalRing.map_maximalIdeal_le
      (algebraMap (LocalIntegerRing K) (LocalIntegerRing L))
      (Ideal.mem_map_of_mem _ hpimem)
  have halpha_mem : alphaO ∈ localMaximalIdeal L := by
    have hpow : alphaO ^ n ∈ localMaximalIdeal L := by
      rw [halphaO_pow]
      exact hpimap
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance n hpow
  have hmap_le : (localMaximalIdeal K).map
      (algebraMap (LocalIntegerRing K) (LocalIntegerRing L)) ≤
        localMaximalIdeal L ^ n := by
    rw [← hpi, Ideal.map_span, Set.image_singleton, ← halphaO_pow,
      ← Ideal.span_singleton_pow]
    exact Ideal.pow_right_mono
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr halpha_mem)) n
  have hlower : n ≤ E.relativeRamificationIndex := by
    have hpow_le : localMaximalIdeal L ^ E.relativeRamificationIndex ≤
        localMaximalIdeal L ^ n := by
      rw [← E.map_localMaximalIdeal_eq_pow]
      exact hmap_le
    have hc := Order.coheight_anti hpow_le
    simpa only [IsDiscreteValuationRing.coheight_pow_maximalIdeal,
      ENat.coe_le_coe] using hc
  have hupper : E.relativeRamificationIndex ≤ n := by
    calc
      E.relativeRamificationIndex = Nat.card
          ((IsLocalRing.maximalIdeal 𝒪[G.fixedField V]).inertia
            ((G.fixedField V) ≃ₐ[G.presentation] (G.fixedField V))) := by
        symm
        exact G.fixedFieldFiniteInertia_card U
          (uniformizerKummerOpenSubgroup_normal K pi hpi n hn)
      _ ≤ Nat.card ((G.fixedField V) ≃ₐ[G.presentation] (G.fixedField V)) :=
        Nat.card_le_card_of_injective (fun x => x.1) Subtype.val_injective
      _ = Module.finrank K (G.fixedField V) :=
        IsGalois.card_aut_eq_finrank G.presentation (G.fixedField V)
      _ = n := hfinrank
  exact Nat.le_antisymm hupper hlower

/-- In the totally ramified specified-uniformizer extension, the distinguished root is itself a
uniformizer. -/
theorem uniformizerKummerFixedIntegerRoot_irreducible
    (K : PointedMixedCharLocalField.{u}) (pi : LocalIntegerRing K)
    (hpi : Ideal.span {pi} = localMaximalIdeal K)
    (n : ℕ) (hn : 0 < n) (hroot : (primitiveRoots n K).Nonempty) :
    let G := OTriangle.LocalGaloisGroup.mk K
    let V : G.OpenSubgroupIndex := OrderDual.toDual
      (uniformizerKummerOpenSubgroup K pi hpi n hn)
    letI := G.presentation.nontriviallyNormedField
    letI := G.presentation.isUltrametricDist
    letI := G.presentation.completeSpace
    letI := G.fixedFieldNontriviallyNormedField V
    letI := G.fixedFieldIsUltrametricDist V
    letI : ValuativeRel (G.fixedField V) := G.fixedFieldValuativeRel V
    Irreducible (uniformizerKummerFixedIntegerRoot K pi hpi n hn) := by
  let G := OTriangle.LocalGaloisGroup.mk K
  let U := uniformizerKummerOpenSubgroup K pi hpi n hn
  let V : G.OpenSubgroupIndex := OrderDual.toDual U
  let L := G.fixedFieldPointed V
  let E := G.fixedFieldBaseExtension V
  letI : NeZero n := ⟨hn.ne'⟩
  letI := G.presentation.nontriviallyNormedField
  letI := G.presentation.isUltrametricDist
  letI := G.presentation.completeSpace
  letI := G.fixedFieldNontriviallyNormedField V
  letI := G.fixedFieldIsUltrametricDist V
  letI : ValuativeRel L := G.fixedFieldValuativeRel V
  letI : Algebra K L := E.algebra
  letI : ValuativeExtension K L := E.valuativeExtension
  let alphaO := uniformizerKummerFixedIntegerRoot K pi hpi n hn
  have halphaO_pow : alphaO ^ n =
      algebraMap (LocalIntegerRing K) (LocalIntegerRing L) pi := by
    apply Subtype.ext
    exact uniformizerKummerFixedRoot_pow K pi hpi n hn
  have hpows : Ideal.span {alphaO} ^ n = localMaximalIdeal L ^ n := by
    calc
      Ideal.span {alphaO} ^ n = Ideal.span {alphaO ^ n} :=
        Ideal.span_singleton_pow alphaO n
      _ = Ideal.span
          {algebraMap (LocalIntegerRing K) (LocalIntegerRing L) pi} := by
        rw [halphaO_pow]
      _ = (localMaximalIdeal K).map
          (algebraMap (LocalIntegerRing K) (LocalIntegerRing L)) := by
        rw [← hpi, Ideal.map_span, Set.image_singleton]
      _ = localMaximalIdeal L ^ E.relativeRamificationIndex :=
        E.map_localMaximalIdeal_eq_pow
      _ = localMaximalIdeal L ^ n := by
        rw [uniformizerKummer_relativeRamificationIndex_eq K pi hpi n hn hroot]
  have hspan : Ideal.span {alphaO} = localMaximalIdeal L :=
    pow_left_injective hn.ne' hpows
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer alphaO).mpr hspan.symm

/-- The explicit cyclic generator is finite inertia and its tame character is the reduction of
the selected primitive root. -/
theorem exists_uniformizerKummerInertiaGenerator_tameCharacter
    (K : PointedMixedCharLocalField.{u}) (pi : LocalIntegerRing K)
    (hpi : Ideal.span {pi} = localMaximalIdeal K)
    (n : ℕ) (hn : 0 < n) (hroot : (primitiveRoots n K).Nonempty) :
    let G := OTriangle.LocalGaloisGroup.mk K
    let U := uniformizerKummerOpenSubgroup K pi hpi n hn
    let V : G.OpenSubgroupIndex := OrderDual.toDual U
    let L := G.fixedField V
    letI := G.presentation.nontriviallyNormedField
    letI := G.presentation.isUltrametricDist
    letI := G.presentation.completeSpace
    letI := G.fixedFieldNontriviallyNormedField V
    letI := G.fixedFieldIsUltrametricDist V
    letI : ValuativeRel L := G.fixedFieldValuativeRel V
    letI : TopologicalSpace L := G.fixedFieldTopologicalSpace V
    letI : IsNonarchimedeanLocalField L := G.fixedFieldIsNonarchimedeanLocalField V
    letI : ValuativeExtension K L := G.fixedFieldValuativeExtensionFromPresentation V
    letI : FiniteDimensional K L := G.fixedField_finiteDimensional V
    letI : Algebra.IsAlgebraic K L := by infer_instance
    letI : IsGalois K L := G.fixedField_isGalois_of_normal U
      (uniformizerKummerOpenSubgroup_normal K pi hpi n hn)
    letI : IsScalarTower K K L := IsScalarTower.of_algebraMap_eq' rfl
    letI : MulSemiringAction (L ≃ₐ[K] L) 𝒪[L] :=
      SpectralLocalField.integerMulSemiringAction K K L
    ∃ τ : (IsLocalRing.maximalIdeal 𝒪[L]).inertia (L ≃ₐ[K] L),
      ∃ zeta : 𝒪[L]ˣ,
        (zeta : L) = algebraMap K L hroot.choose ∧
        tameCharacter 𝒪[L] (L ≃ₐ[K] L) τ =
          Units.map (IsLocalRing.residue 𝒪[L]).toMonoidHom zeta := by
  let G := OTriangle.LocalGaloisGroup.mk K
  let U := uniformizerKummerOpenSubgroup K pi hpi n hn
  let V : G.OpenSubgroupIndex := OrderDual.toDual U
  let L := G.fixedField V
  let LP := G.fixedFieldPointed V
  let E := G.fixedFieldBaseExtension V
  letI : NeZero n := ⟨hn.ne'⟩
  letI := G.presentation.nontriviallyNormedField
  letI := G.presentation.isUltrametricDist
  letI := G.presentation.completeSpace
  letI := G.fixedFieldNontriviallyNormedField V
  letI := G.fixedFieldIsUltrametricDist V
  letI : ValuativeRel L := G.fixedFieldValuativeRel V
  letI : TopologicalSpace L := G.fixedFieldTopologicalSpace V
  letI : IsNonarchimedeanLocalField L := G.fixedFieldIsNonarchimedeanLocalField V
  letI : ValuativeExtension K (G.fixedField V) :=
    G.fixedFieldValuativeExtensionFromPresentation V
  letI : FiniteDimensional K (G.fixedField V) :=
    G.fixedField_finiteDimensional V
  letI : FiniteDimensional K L := G.fixedField_finiteDimensional V
  letI : IsGalois K (G.fixedField V) := G.fixedField_isGalois_of_normal U
    (uniformizerKummerOpenSubgroup_normal K pi hpi n hn)
  letI : IsScalarTower K K L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (LocalIntegerRing K) 𝒪[L] L :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : MulSemiringAction (L ≃ₐ[K] L) 𝒪[L] :=
    SpectralLocalField.integerMulSemiringAction K K L
  letI : CharP (IsLocalRing.ResidueField 𝒪[L]) K.residueChar :=
    (G.fixedFieldPointed V).residueFieldCharP
  let I := (IsLocalRing.maximalIdeal 𝒪[G.fixedField V]).inertia
    ((G.fixedField V) ≃ₐ[K] (G.fixedField V))
  have hfinrank : Module.finrank K L = n := by
    change Module.finrank K (G.fixedField V) = n
    rw [uniformizerKummer_fixedField_eq K pi hpi n hn]
    exact uniformizerKummerIntermediateField_finrank K pi hpi n hn hroot
  have hIcard : Nat.card I = n := by
    calc
      Nat.card I = E.relativeRamificationIndex :=
        G.fixedFieldFiniteInertia_card U
          (uniformizerKummerOpenSubgroup_normal K pi hpi n hn)
      _ = n := uniformizerKummer_relativeRamificationIndex_eq K pi hpi n hn hroot
  have hGcard : Nat.card ((G.fixedField V) ≃ₐ[K] (G.fixedField V)) = n := by
    rw [IsGalois.card_aut_eq_finrank K (G.fixedField V), hfinrank]
  have hItop : I = ⊤ := Subgroup.eq_top_of_card_eq I (hIcard.trans hGcard.symm)
  let sigma : (G.fixedField V) ≃ₐ[K] (G.fixedField V) :=
    uniformizerKummerFixedGeneratorAutomorphism K pi hpi n hn hroot
  let tau : I := ⟨sigma, by rw [hItop]; trivial⟩
  let alphaO : 𝒪[L] := uniformizerKummerFixedIntegerRoot K pi hpi n hn
  have halpha_irred : Irreducible alphaO :=
    uniformizerKummerFixedIntegerRoot_irreducible K pi hpi n hn hroot
  let f : (LocalIntegerRing K)[X] := X ^ n - C 1
  have hzeta_integral : IsIntegral (LocalIntegerRing K)
      (algebraMap K L hroot.choose) := by
    refine ⟨f, monic_X_pow_sub_C _ hn.ne', ?_⟩
    change Polynomial.aeval (algebraMap K L hroot.choose) f = 0
    rw [aeval_def, eval₂_sub, eval₂_X_pow, eval₂_C]
    rw [← map_pow, (mem_primitiveRoots hn).mp hroot.choose_spec |>.pow_eq_one]
    simp only [map_one, sub_self]
  let zetaO : 𝒪[L] := ⟨algebraMap K L hroot.choose,
    Valuation.Integers.mem_of_integral
      (Valuation.integer.integers (valuation L)) hzeta_integral.tower_top⟩
  have hzetaO_pow : zetaO ^ n = 1 := by
    apply Subtype.ext
    change (algebraMap K L hroot.choose) ^ n = 1
    rw [← map_pow, (mem_primitiveRoots hn).mp hroot.choose_spec |>.pow_eq_one,
      map_one]
  have hzetaO_unit : IsUnit zetaO := by
    rw [isUnit_iff_dvd_one]
    refine ⟨zetaO ^ (n - 1), ?_⟩
    rw [mul_comm, ← pow_succ,
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn.ne'), hzetaO_pow]
  let zeta : 𝒪[L]ˣ := hzetaO_unit.unit
  have hzeta_val : (zeta : L) = algebraMap K L hroot.choose := by
    change ((zeta : 𝒪[L]) : L) = _
    rw [IsUnit.unit_spec]
  have halpha_mul : alphaO * (zeta : 𝒪[L]) = tau.1 • alphaO := by
    apply Subtype.ext
    change uniformizerKummerFixedRoot K pi hpi n hn *
        algebraMap K L hroot.choose =
      sigma (uniformizerKummerFixedRoot K pi hpi n hn)
    have hsigma := uniformizerKummerFixedGeneratorAutomorphism_apply_root
      K pi hpi n hn hroot
    change sigma (uniformizerKummerFixedRoot K pi hpi n hn) =
      algebraMap K L hroot.choose *
        uniformizerKummerFixedRoot K pi hpi n hn at hsigma
    rw [hsigma]
    exact mul_comm _ _
  refine ⟨tau, zeta, hzeta_val, ?_⟩
  exact tameCharacter_eq_residue_of_uniformizer_mul 𝒪[L] (L ≃ₐ[K] L)
    tau alphaO halpha_irred zeta halpha_mul

end Anabelian.LCFT
