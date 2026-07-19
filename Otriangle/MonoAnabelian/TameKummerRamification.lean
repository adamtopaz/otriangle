import Otriangle.MonoAnabelian.TameKummerExtension
import Otriangle.MonoAnabelian.FiniteGaloisRamification
import Otriangle.MonoAnabelian.FiniteTameRamification
import Otriangle.MonoAnabelian.PrimeToTorsionUnits

/-!
# Ramification of the explicit Kummer extensions

The fixed-field presentation of the splitting field of `X ^ n - π` has relative ramification
index `n`.  The lower bound comes directly from the equation `α ^ n = π`; the upper bound is
the finite inertia-cardinality theorem together with the degree computation.
-/

noncomputable section

namespace Anabelian
namespace LCFT

open OTriangle ValuativeRel Polynomial
open OTriangle.FiniteTameRamification

universe u

/-- The normal open subgroup fixing the embedded tame Kummer field. -/
noncomputable def tameKummerOpenSubgroup
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) (hn : 0 < n) :
    OpenSubgroup (OTriangle.LocalGaloisGroup.mk K).toProfiniteGrp := by
  let L := tameKummerFiniteGaloisIntermediateField K n hn
  exact ⟨L.toIntermediateField.fixingSubgroup,
    L.toIntermediateField.fixingSubgroup_isOpen⟩

theorem tameKummerOpenSubgroup_normal
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) (hn : 0 < n) :
    (tameKummerOpenSubgroup K n hn).toSubgroup.Normal := by
  let L := tameKummerFiniteGaloisIntermediateField K n hn
  change L.toIntermediateField.fixingSubgroup.Normal
  infer_instance

theorem tameKummer_fixedField_eq
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) (hn : 0 < n) :
    let G := OTriangle.LocalGaloisGroup.mk K
    G.fixedField (OrderDual.toDual (tameKummerOpenSubgroup K n hn)) =
      tameKummerIntermediateField K n := by
  let G := OTriangle.LocalGaloisGroup.mk K
  let L := tameKummerFiniteGaloisIntermediateField K n hn
  change IntermediateField.fixedField L.toIntermediateField.fixingSubgroup =
    tameKummerIntermediateField K n
  rw [InfiniteGalois.fixedField_fixingSubgroup]
  rfl

/-- The fixed-field presentation of the Kummer extension is canonically equivalent to its
splitting-field presentation. -/
noncomputable def tameKummerFixedFieldEquiv
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) (hn : 0 < n) :
    let G := OTriangle.LocalGaloisGroup.mk K
    G.fixedField (OrderDual.toDual (tameKummerOpenSubgroup K n hn)) ≃ₐ[K]
      tameKummerIntermediateField K n :=
  IntermediateField.equivOfEq (tameKummer_fixedField_eq K n hn)

/-- The distinguished Kummer root, transported to the literal fixed field. -/
noncomputable def tameKummerFixedRoot
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) (hn : 0 < n) :
    let G := OTriangle.LocalGaloisGroup.mk K
    G.fixedField (OrderDual.toDual (tameKummerOpenSubgroup K n hn)) := by
  letI : NeZero n := ⟨hn.ne'⟩
  exact (tameKummerFixedFieldEquiv K n hn).symm (tameKummerRoot K n)

theorem tameKummerFixedRoot_pow
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) (hn : 0 < n) :
    let G := OTriangle.LocalGaloisGroup.mk K
    let V : G.OpenSubgroupIndex :=
      OrderDual.toDual (tameKummerOpenSubgroup K n hn)
    tameKummerFixedRoot K n hn ^ n =
      algebraMap K (G.fixedField V) (localUniformizerInteger K : K) := by
  letI : NeZero n := ⟨hn.ne'⟩
  let e := tameKummerFixedFieldEquiv K n hn
  apply e.injective
  simp only [map_pow, e.apply_symm_apply, e.commutes]
  exact tameKummerRoot_pow K n

theorem tameKummerFixedRoot_isIntegral
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) (hn : 0 < n) :
    let G := OTriangle.LocalGaloisGroup.mk K
    let V : G.OpenSubgroupIndex :=
      OrderDual.toDual (tameKummerOpenSubgroup K n hn)
    IsIntegral (LocalIntegerRing K) (tameKummerFixedRoot K n hn) := by
  let G := OTriangle.LocalGaloisGroup.mk K
  let V : G.OpenSubgroupIndex :=
    OrderDual.toDual (tameKummerOpenSubgroup K n hn)
  let f : (LocalIntegerRing K)[X] :=
    X ^ n - C (localUniformizerInteger K)
  refine ⟨f, monic_X_pow_sub_C _ hn.ne', ?_⟩
  change Polynomial.aeval (tameKummerFixedRoot K n hn) f = 0
  rw [aeval_def, eval₂_sub, eval₂_X_pow, eval₂_C]
  change tameKummerFixedRoot K n hn ^ n -
    algebraMap (LocalIntegerRing K) (G.fixedField V)
      (localUniformizerInteger K) = 0
  rw [tameKummerFixedRoot_pow]
  apply sub_eq_zero.mpr
  rfl

/-- The Kummer root as an element of the spectral valuation ring on the fixed field. -/
noncomputable def tameKummerFixedIntegerRoot
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) (hn : 0 < n) :
    let G := OTriangle.LocalGaloisGroup.mk K
    let V : G.OpenSubgroupIndex :=
      OrderDual.toDual (tameKummerOpenSubgroup K n hn)
    LocalIntegerRing (G.fixedFieldPointed V) := by
  let G := OTriangle.LocalGaloisGroup.mk K
  let V : G.OpenSubgroupIndex :=
    OrderDual.toDual (tameKummerOpenSubgroup K n hn)
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
  letI : IsScalarTower (LocalIntegerRing K)
      𝒪[G.fixedField V] (G.fixedField V) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact ⟨tameKummerFixedRoot K n hn,
    Valuation.Integers.mem_of_integral
      (Valuation.integer.integers (valuation L))
      (tameKummerFixedRoot_isIntegral K n hn).tower_top⟩

/-- The cyclic Kummer generator, transported to the literal fixed field. -/
noncomputable def tameKummerFixedGeneratorAutomorphism
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) (hn : 0 < n)
    (hroot : (primitiveRoots n K).Nonempty) :
    let G := OTriangle.LocalGaloisGroup.mk K
    let V : G.OpenSubgroupIndex :=
      OrderDual.toDual (tameKummerOpenSubgroup K n hn)
    G.fixedField V ≃ₐ[K] G.fixedField V :=
  (AlgEquiv.autCongr (tameKummerFixedFieldEquiv K n hn)).symm
    (tameKummerGeneratorAutomorphism K n hn hroot)

theorem tameKummerFixedGeneratorAutomorphism_apply_root
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) (hn : 0 < n)
    (hroot : (primitiveRoots n K).Nonempty) :
    let G := OTriangle.LocalGaloisGroup.mk K
    let V : G.OpenSubgroupIndex :=
      OrderDual.toDual (tameKummerOpenSubgroup K n hn)
    tameKummerFixedGeneratorAutomorphism K n hn hroot
        (tameKummerFixedRoot K n hn) =
      algebraMap K (G.fixedField V) hroot.choose *
        tameKummerFixedRoot K n hn := by
  letI : NeZero n := ⟨hn.ne'⟩
  let e := tameKummerFixedFieldEquiv K n hn
  apply e.injective
  change tameKummerGeneratorAutomorphism K n hn hroot
      (tameKummerRoot K n) =
    algebraMap K (tameKummerIntermediateField K n) hroot.choose *
      tameKummerRoot K n
  exact tameKummerGeneratorAutomorphism_apply_root K n hn hroot

/-- The explicit Kummer fixed field is totally ramified of degree `n`. -/
theorem tameKummer_relativeRamificationIndex_eq
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) (hn : 0 < n)
    (hroot : (primitiveRoots n K).Nonempty) :
    let G := OTriangle.LocalGaloisGroup.mk K
    let U := tameKummerOpenSubgroup K n hn
    (G.fixedFieldBaseExtension (OrderDual.toDual U)).relativeRamificationIndex = n := by
  let G := OTriangle.LocalGaloisGroup.mk K
  let U := tameKummerOpenSubgroup K n hn
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
    (tameKummerOpenSubgroup_normal K n hn)
  letI : IsScalarTower G.presentation G.presentation (G.fixedField V) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : MulSemiringAction
      ((G.fixedField V) ≃ₐ[G.presentation] (G.fixedField V))
        𝒪[G.fixedField V] :=
    SpectralLocalField.integerMulSemiringAction
      G.presentation G.presentation (G.fixedField V)
  let hfield : G.fixedField V = tameKummerIntermediateField K n :=
    tameKummer_fixedField_eq K n hn
  have hfinrank : Module.finrank K L = n := by
    change Module.finrank K (G.fixedField V) = n
    rw [hfield]
    exact tameKummerIntermediateField_finrank K n hn hroot
  let alpha : L := ⟨(tameKummerRoot K n : K.algebraicClosure), by
    rw [hfield]
    exact (tameKummerRoot K n).property⟩
  have halpha_pow : alpha ^ n =
      algebraMap K L (localUniformizerInteger K : K) := by
    apply Subtype.ext
    change (tameKummerRoot K n : K.algebraicClosure) ^ n =
      algebraMap K K.algebraicClosure (localUniformizerInteger K : K)
    exact congrArg Subtype.val (tameKummerRoot_pow K n)
  have halpha_integral : IsIntegral (LocalIntegerRing K) alpha := by
    let f : (LocalIntegerRing K)[X] :=
      X ^ n - C (localUniformizerInteger K)
    refine ⟨f, monic_X_pow_sub_C _ hn.ne', ?_⟩
    change Polynomial.aeval alpha f = 0
    rw [aeval_def, eval₂_sub, eval₂_X_pow, eval₂_C]
    change alpha ^ n - algebraMap (LocalIntegerRing K) L
      (localUniformizerInteger K) = 0
    rw [halpha_pow]
    apply sub_eq_zero.mpr
    rfl
  let alphaO : LocalIntegerRing L :=
    ⟨alpha, Valuation.Integers.mem_of_integral
      (Valuation.integer.integers (valuation L)) halpha_integral.tower_top⟩
  have halphaO_pow : alphaO ^ n =
      algebraMap (LocalIntegerRing K) (LocalIntegerRing L)
        (localUniformizerInteger K) := by
    apply Subtype.ext
    exact halpha_pow
  have hpi_base : localUniformizerInteger K ∈ localMaximalIdeal K := by
    rw [localMaximalIdeal_eq_span_uniformizer]
    exact Ideal.mem_span_singleton.mpr (dvd_refl _)
  have hpi_mem : algebraMap (LocalIntegerRing K) (LocalIntegerRing L)
      (localUniformizerInteger K) ∈ localMaximalIdeal L := by
    exact IsLocalRing.map_maximalIdeal_le
      (algebraMap (LocalIntegerRing K) (LocalIntegerRing L))
      (Ideal.mem_map_of_mem _ hpi_base)
  have halpha_mem : alphaO ∈ localMaximalIdeal L := by
    have hpow : alphaO ^ n ∈ localMaximalIdeal L := by
      rw [halphaO_pow]
      exact hpi_mem
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance n hpow
  have hmap_le : (localMaximalIdeal K).map
      (algebraMap (LocalIntegerRing K) (LocalIntegerRing L)) ≤
        localMaximalIdeal L ^ n := by
    rw [localMaximalIdeal_eq_span_uniformizer, Ideal.map_span,
      Set.image_singleton, ← halphaO_pow, ← Ideal.span_singleton_pow]
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
          (tameKummerOpenSubgroup_normal K n hn)
      _ ≤ Nat.card
          ((G.fixedField V) ≃ₐ[G.presentation] (G.fixedField V)) :=
        Nat.card_le_card_of_injective (fun x => x.1) Subtype.val_injective
      _ = Module.finrank K (G.fixedField V) :=
        IsGalois.card_aut_eq_finrank G.presentation (G.fixedField V)
      _ = n := hfinrank
  exact Nat.le_antisymm hupper hlower

/-- In the totally ramified Kummer fixed field, the distinguished root is a uniformizer. -/
theorem tameKummerFixedIntegerRoot_irreducible
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) (hn : 0 < n)
    (hroot : (primitiveRoots n K).Nonempty) :
    let G := OTriangle.LocalGaloisGroup.mk K
    let V : G.OpenSubgroupIndex :=
      OrderDual.toDual (tameKummerOpenSubgroup K n hn)
    letI := G.presentation.nontriviallyNormedField
    letI := G.presentation.isUltrametricDist
    letI := G.presentation.completeSpace
    letI := G.fixedFieldNontriviallyNormedField V
    letI := G.fixedFieldIsUltrametricDist V
    letI : ValuativeRel (G.fixedField V) := G.fixedFieldValuativeRel V
    Irreducible (tameKummerFixedIntegerRoot K n hn) := by
  let G := OTriangle.LocalGaloisGroup.mk K
  let U := tameKummerOpenSubgroup K n hn
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
  let alphaO := tameKummerFixedIntegerRoot K n hn
  have halphaO_pow : alphaO ^ n =
      algebraMap (LocalIntegerRing K) (LocalIntegerRing L)
        (localUniformizerInteger K) := by
    apply Subtype.ext
    exact tameKummerFixedRoot_pow K n hn
  have hpows : Ideal.span {alphaO} ^ n = localMaximalIdeal L ^ n := by
    calc
      Ideal.span {alphaO} ^ n = Ideal.span {alphaO ^ n} :=
        Ideal.span_singleton_pow alphaO n
      _ = Ideal.span
          {algebraMap (LocalIntegerRing K) (LocalIntegerRing L)
            (localUniformizerInteger K)} := by rw [halphaO_pow]
      _ = (localMaximalIdeal K).map
          (algebraMap (LocalIntegerRing K) (LocalIntegerRing L)) := by
        rw [localMaximalIdeal_eq_span_uniformizer, Ideal.map_span,
          Set.image_singleton]
      _ = localMaximalIdeal L ^ E.relativeRamificationIndex :=
        E.map_localMaximalIdeal_eq_pow
      _ = localMaximalIdeal L ^ n := by
        rw [tameKummer_relativeRamificationIndex_eq K n hn hroot]
  have hspan : Ideal.span {alphaO} = localMaximalIdeal L :=
    pow_left_injective hn.ne' hpows
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer alphaO).mpr hspan.symm

/-- The explicit cyclic generator belongs to finite inertia, and its tame character is the
reduction of the chosen primitive root of unity. -/
theorem exists_tameKummerInertiaGenerator_tameCharacter
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) (hn : 0 < n)
    (hroot : (primitiveRoots n K).Nonempty) :
    let G := OTriangle.LocalGaloisGroup.mk K
    let U := tameKummerOpenSubgroup K n hn
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
      (tameKummerOpenSubgroup_normal K n hn)
    letI : IsScalarTower K K L := IsScalarTower.of_algebraMap_eq' rfl
    letI : MulSemiringAction (L ≃ₐ[K] L) 𝒪[L] :=
      SpectralLocalField.integerMulSemiringAction K K L
    ∃ τ : (IsLocalRing.maximalIdeal 𝒪[L]).inertia (L ≃ₐ[K] L),
      ∃ zeta : 𝒪[L]ˣ,
        (zeta : L) = algebraMap K L hroot.choose ∧
        tameCharacter 𝒪[L] (L ≃ₐ[K] L) τ =
          Units.map (IsLocalRing.residue 𝒪[L]).toMonoidHom zeta := by
  let G := OTriangle.LocalGaloisGroup.mk K
  let U := tameKummerOpenSubgroup K n hn
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
    (tameKummerOpenSubgroup_normal K n hn)
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
    rw [tameKummer_fixedField_eq K n hn]
    exact tameKummerIntermediateField_finrank K n hn hroot
  have hIcard : Nat.card I = n := by
    calc
      Nat.card I = E.relativeRamificationIndex :=
        G.fixedFieldFiniteInertia_card U
          (tameKummerOpenSubgroup_normal K n hn)
      _ = n := tameKummer_relativeRamificationIndex_eq K n hn hroot
  have hGcard : Nat.card
      ((G.fixedField V) ≃ₐ[K] (G.fixedField V)) = n := by
    rw [IsGalois.card_aut_eq_finrank K (G.fixedField V), hfinrank]
  have hItop : I = ⊤ := Subgroup.eq_top_of_card_eq I (hIcard.trans hGcard.symm)
  let sigma : (G.fixedField V) ≃ₐ[K] (G.fixedField V) :=
    tameKummerFixedGeneratorAutomorphism K n hn hroot
  let tau : I := ⟨sigma, by rw [hItop]; trivial⟩
  let alphaO : 𝒪[L] := tameKummerFixedIntegerRoot K n hn
  have halpha_irred : Irreducible alphaO :=
    tameKummerFixedIntegerRoot_irreducible K n hn hroot
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
    change tameKummerFixedRoot K n hn * algebraMap K L hroot.choose =
      sigma (tameKummerFixedRoot K n hn)
    have hsigma := tameKummerFixedGeneratorAutomorphism_apply_root K n hn hroot
    change sigma (tameKummerFixedRoot K n hn) =
      algebraMap K L hroot.choose * tameKummerFixedRoot K n hn at hsigma
    rw [hsigma]
    exact mul_comm _ _
  refine ⟨tau, zeta, hzeta_val, ?_⟩
  exact tameCharacter_eq_residue_of_uniformizer_mul 𝒪[L] (L ≃ₐ[K] L)
    tau alphaO halpha_irred zeta halpha_mul

/-- When the Kummer degree is prime to the residue characteristic, the explicit generator has
tame character of exact order `n`. -/
theorem exists_tameKummerInertiaGenerator_tameCharacter_isPrimitiveRoot
    (K : PointedMixedCharLocalField.{u}) (n : ℕ) (hn : 0 < n)
    (hcop : Nat.Coprime n K.residueChar)
    (hroot : (primitiveRoots n K).Nonempty) :
    let G := OTriangle.LocalGaloisGroup.mk K
    let U := tameKummerOpenSubgroup K n hn
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
      (tameKummerOpenSubgroup_normal K n hn)
    letI : IsScalarTower K K L := IsScalarTower.of_algebraMap_eq' rfl
    letI : MulSemiringAction (L ≃ₐ[K] L) 𝒪[L] :=
      SpectralLocalField.integerMulSemiringAction K K L
    ∃ τ : (IsLocalRing.maximalIdeal 𝒪[L]).inertia (L ≃ₐ[K] L),
      IsPrimitiveRoot (tameCharacter 𝒪[L] (L ≃ₐ[K] L) τ) n := by
  let G := OTriangle.LocalGaloisGroup.mk K
  let U := tameKummerOpenSubgroup K n hn
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
    (tameKummerOpenSubgroup_normal K n hn)
  letI : IsScalarTower K K L := IsScalarTower.of_algebraMap_eq' rfl
  letI : MulSemiringAction (L ≃ₐ[K] L) 𝒪[L] :=
    SpectralLocalField.integerMulSemiringAction K K L
  letI : CharP (IsLocalRing.ResidueField 𝒪[L]) K.residueChar :=
    (G.fixedFieldPointed V).residueFieldCharP
  obtain ⟨tau, zeta, hzeta, htame⟩ :=
    exists_tameKummerInertiaGenerator_tameCharacter K n hn hroot
  have hprimK : IsPrimitiveRoot hroot.choose n :=
    (mem_primitiveRoots hn).mp hroot.choose_spec
  have hprimL : IsPrimitiveRoot (algebraMap K L hroot.choose) n :=
    hprimK.map_of_injective (algebraMap K L).injective
  let coeToField : 𝒪[L]ˣ →* L :=
    (valuation L).valuationSubring.subtype.toMonoidHom.comp (Units.coeHom 𝒪[L])
  have hcoeToField : Function.Injective coeToField :=
    Subtype.coe_injective.comp Units.val_injective
  have hprimZeta : IsPrimitiveRoot zeta n := by
    apply IsPrimitiveRoot.of_map_of_injective (f := coeToField) _ hcoeToField
    change IsPrimitiveRoot ((zeta : 𝒪[L]) : L) n
    rw [hzeta]
    exact hprimL
  have horder := orderOf_unitsMap_residue_eq_of_coprime
    𝒪[L] K.residueChar n zeta hn
      (IsPrimitiveRoot.iff_orderOf.mp hprimZeta) hcop
  refine ⟨tau, IsPrimitiveRoot.iff_orderOf.mpr ?_⟩
  rw [htame]
  exact horder

end LCFT
end Anabelian
