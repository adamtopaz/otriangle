import Otriangle.MonoAnabelian.UnramifiedFixedFieldsOf
import Otriangle.MonoAnabelian.UniformizerKummerRamification
import Otriangle.MonoAnabelian.FixedFieldSystem

/-!
# Normal unramified--Kummer composita

The splitting field of `X ^ n - π_K` over the base is normal but may not yet contain the roots
of unity needed for the cyclic Kummer description.  Adjoining it to a finite unramified fixed
field produces a finite Galois extension of the original field; over the unramified layer it is
the specified-uniformizer Kummer splitting field.
-/

noncomputable section

namespace Anabelian.OTriangle.LocalGaloisGroup

open LCFT ValuativeRel Polynomial

universe u

variable (G : LocalGaloisGroup.{u})

/-- The finite Galois compositum of an unramified fixed field and the base splitting field of
`X ^ n - π`. -/
noncomputable def unramifiedKummerCompositum
    (E : G.ResidueFiniteGaloisIntermediateField)
    (pi : LocalIntegerRing G.presentation)
    (hpi : Ideal.span {pi} = localMaximalIdeal G.presentation)
    (n : ℕ) (hn : 0 < n) :
    FiniteGaloisIntermediateField G.presentation G.presentation.algebraicClosure :=
  G.residueUnramifiedFiniteGaloisIntermediateFieldOf E ⊔
    LCFT.uniformizerKummerFiniteGaloisIntermediateField G.presentation pi
      (LCFT.uniformizer_ne_zero G.presentation pi hpi) n hn

theorem residueUnramifiedFiniteGaloisIntermediateFieldOf_le_unramifiedKummerCompositum
    (E : G.ResidueFiniteGaloisIntermediateField)
    (pi : LocalIntegerRing G.presentation)
    (hpi : Ideal.span {pi} = localMaximalIdeal G.presentation)
    (n : ℕ) (hn : 0 < n) :
    G.residueUnramifiedFiniteGaloisIntermediateFieldOf E ≤
      G.unramifiedKummerCompositum E pi hpi n hn :=
  le_sup_left

theorem uniformizerKummerFiniteGaloisIntermediateField_le_unramifiedKummerCompositum
    (E : G.ResidueFiniteGaloisIntermediateField)
    (pi : LocalIntegerRing G.presentation)
    (hpi : Ideal.span {pi} = localMaximalIdeal G.presentation)
    (n : ℕ) (hn : 0 < n) :
    LCFT.uniformizerKummerFiniteGaloisIntermediateField G.presentation pi
        (LCFT.uniformizer_ne_zero G.presentation pi hpi) n hn ≤
      G.unramifiedKummerCompositum E pi hpi n hn :=
  le_sup_right

/-- The normal open subgroup that fixes the unramified--Kummer compositum. -/
noncomputable def unramifiedKummerOpenSubgroup
    (E : G.ResidueFiniteGaloisIntermediateField)
    (pi : LocalIntegerRing G.presentation)
    (hpi : Ideal.span {pi} = localMaximalIdeal G.presentation)
    (n : ℕ) (hn : 0 < n) :
    OpenSubgroup G.toProfiniteGrp :=
  ⟨(G.unramifiedKummerCompositum E pi hpi n hn).toIntermediateField.fixingSubgroup,
    IntermediateField.fixingSubgroup_isOpen _⟩

theorem unramifiedKummerOpenSubgroup_normal
    (E : G.ResidueFiniteGaloisIntermediateField)
    (pi : LocalIntegerRing G.presentation)
    (hpi : Ideal.span {pi} = localMaximalIdeal G.presentation)
    (n : ℕ) (hn : 0 < n) :
    (G.unramifiedKummerOpenSubgroup E pi hpi n hn).toSubgroup.Normal := by
  change (G.unramifiedKummerCompositum E pi hpi n hn).toIntermediateField.fixingSubgroup.Normal
  infer_instance

/-- The fixed field of the compositum subgroup is the compositum itself. -/
theorem unramifiedKummer_fixedField_eq
    (E : G.ResidueFiniteGaloisIntermediateField)
    (pi : LocalIntegerRing G.presentation)
    (hpi : Ideal.span {pi} = localMaximalIdeal G.presentation)
    (n : ℕ) (hn : 0 < n) :
    G.fixedField (OrderDual.toDual
      (G.unramifiedKummerOpenSubgroup E pi hpi n hn)) =
        (G.unramifiedKummerCompositum E pi hpi n hn).toIntermediateField := by
  change IntermediateField.fixedField
      (G.unramifiedKummerCompositum E pi hpi n hn).toIntermediateField.fixingSubgroup = _
  exact InfiniteGalois.fixedField_fixingSubgroup _

/-- The compositum subgroup is contained in the unramified subgroup, equivalently the latter
fixed field embeds into the compositum. -/
theorem unramifiedKummerOpenSubgroup_le_residueUnramifiedOpenSubgroupOf
    (E : G.ResidueFiniteGaloisIntermediateField)
    (pi : LocalIntegerRing G.presentation)
    (hpi : Ideal.span {pi} = localMaximalIdeal G.presentation)
    (n : ℕ) (hn : 0 < n) :
    G.unramifiedKummerOpenSubgroup E pi hpi n hn ≤
      G.residueUnramifiedOpenSubgroupOf E := by
  let U := G.residueUnramifiedOpenSubgroupOf E
  let V : G.OpenSubgroupIndex := OrderDual.toDual U
  have hfix : (G.fixedField V).fixingSubgroup = U.toSubgroup :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨U.toSubgroup, U.isClosed⟩
  change (G.unramifiedKummerCompositum E pi hpi n hn).toIntermediateField.fixingSubgroup ≤
    U.toSubgroup
  rw [← hfix]
  exact IntermediateField.fixingSubgroup_antitone
    (G.residueUnramifiedFiniteGaloisIntermediateFieldOf_le_unramifiedKummerCompositum
      E pi hpi n hn)

theorem residueUnramifiedIndex_le_unramifiedKummerIndex
    (E : G.ResidueFiniteGaloisIntermediateField)
    (pi : LocalIntegerRing G.presentation)
    (hpi : Ideal.span {pi} = localMaximalIdeal G.presentation)
    (n : ℕ) (hn : 0 < n) :
    OrderDual.toDual (G.residueUnramifiedOpenSubgroupOf E) ≤
      OrderDual.toDual (G.unramifiedKummerOpenSubgroup E pi hpi n hn) :=
  G.unramifiedKummerOpenSubgroup_le_residueUnramifiedOpenSubgroupOf E pi hpi n hn

set_option maxHeartbeats 800000 in
-- The equality unfolds the fixed-field pointing and two scalar-restricted root adjunctions.
/-- Over the unramified layer, the normal compositum is exactly the splitting field of the same
uniformizer polynomial. -/
theorem uniformizerKummer_restrictScalars_eq_unramifiedKummerCompositum
    (E : G.ResidueFiniteGaloisIntermediateField)
    (pi : LocalIntegerRing G.presentation)
    (hpi : Ideal.span {pi} = localMaximalIdeal G.presentation)
    (n : ℕ) (hn : 0 < n) :
    let U := G.residueUnramifiedOpenSubgroupOf E
    let V : G.OpenSubgroupIndex := OrderDual.toDual U
    let K := G.presentation
    let L := G.fixedField V
    let LP := G.fixedFieldPointed V
    let A := K.algebraicClosure
    letI := K.nontriviallyNormedField
    letI := K.isUltrametricDist
    letI := K.completeSpace
    letI := G.fixedFieldNontriviallyNormedField V
    letI := G.fixedFieldIsUltrametricDist V
    letI : ValuativeRel L := G.fixedFieldValuativeRel V
    letI := G.spectralAlgebraicClosureNontriviallyNormedField
    letI := G.spectralAlgebraicClosureIsUltrametricDist
    letI : ValuativeRel A := G.spectralAlgebraicClosureValuativeRel
    letI : Algebra K LP := (G.fixedField V).algebra'
    letI : ValuativeExtension K LP :=
      G.fixedFieldValuativeExtensionFromPresentation V
    letI : ValuativeExtension K A := K.spectralValuativeExtension A
    letI : ValuativeExtension L A := G.fixedFieldValuativeExtension V
    letI : IsScalarTower K LP A := IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      change algebraMap K A x =
        @algebraMap (G.fixedField V) (G.fixedFieldPointed V).algebraicClosure
          _ _ (G.fixedFieldPointed V).algebra
          (algebraMap K (G.fixedField V) x)
      rw [G.fixedFieldPointed_algebraMap_apply]
      exact (IntermediateField.coe_algebraMap_apply (G.fixedField V) x).symm)
    let piL : LocalIntegerRing LP := algebraMap (LocalIntegerRing K) 𝒪[L] pi
    (LCFT.uniformizerKummerIntermediateField LP piL n).restrictScalars K =
      (G.unramifiedKummerCompositum E pi hpi n hn).toIntermediateField := by
  let U := G.residueUnramifiedOpenSubgroupOf E
  let V : G.OpenSubgroupIndex := OrderDual.toDual U
  let K := G.presentation
  let L := G.fixedField V
  let LP := G.fixedFieldPointed V
  let A := K.algebraicClosure
  letI := K.nontriviallyNormedField
  letI := K.isUltrametricDist
  letI := K.completeSpace
  letI := G.fixedFieldNontriviallyNormedField V
  letI := G.fixedFieldIsUltrametricDist V
  letI : ValuativeRel L := G.fixedFieldValuativeRel V
  letI := G.spectralAlgebraicClosureNontriviallyNormedField
  letI := G.spectralAlgebraicClosureIsUltrametricDist
  letI : ValuativeRel A := G.spectralAlgebraicClosureValuativeRel
  letI : Algebra K LP := (G.fixedField V).algebra'
  letI : ValuativeExtension K LP :=
    G.fixedFieldValuativeExtensionFromPresentation V
  letI : ValuativeExtension K A := K.spectralValuativeExtension A
  letI : ValuativeExtension L A := G.fixedFieldValuativeExtension V
  letI : IsScalarTower K LP A := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro x
    change algebraMap K A x =
      @algebraMap (G.fixedField V) (G.fixedFieldPointed V).algebraicClosure
        _ _ (G.fixedFieldPointed V).algebra
        (algebraMap K (G.fixedField V) x)
    rw [G.fixedFieldPointed_algebraMap_apply]
    exact (IntermediateField.coe_algebraMap_apply (G.fixedField V) x).symm)
  let piL : LocalIntegerRing LP := algebraMap (LocalIntegerRing K) 𝒪[L] pi
  change (LCFT.uniformizerKummerIntermediateField LP piL n).restrictScalars K =
    (G.unramifiedKummerCompositum E pi hpi n hn).toIntermediateField
  rw [LCFT.uniformizerKummerIntermediateField_eq_adjoin_rootSet]
  change IntermediateField.restrictScalars K
      (IntermediateField.adjoin (G.fixedField V)
        ((X ^ n - C (piL : L) : L[X]).rootSet A)) =
    (G.unramifiedKummerCompositum E pi hpi n hn).toIntermediateField
  rw [IntermediateField.restrictScalars_adjoin_eq_sup]
  have hroots :
      (X ^ n - C (piL : L) : L[X]).rootSet A =
        (X ^ n - C (pi : K) : K[X]).rootSet A := by
    change (X ^ n - C (algebraMap K L (pi : K)) : L[X]).rootSet A = _
    exact LCFT.rootSet_X_pow_sub_C_algebraMap (pi : K) n hn
  rw [hroots, ← LCFT.uniformizerKummerIntermediateField_eq_adjoin_rootSet]
  rfl

set_option maxHeartbeats 800000 in
-- The identity passes through a dependent fixed-field pointing and an explicit scalar tower.
/-- The compositum has relative degree `n` over its unramified layer. -/
theorem unramifiedKummer_fixedField_finrank_over_unramified
    (E : G.ResidueFiniteGaloisIntermediateField)
    (pi : LocalIntegerRing G.presentation)
    (hpi : Ideal.span {pi} = localMaximalIdeal G.presentation)
    (n : ℕ) (hn : 0 < n)
    (hroot : (primitiveRoots n (G.fixedFieldPointed
      (OrderDual.toDual (G.residueUnramifiedOpenSubgroupOf E)))).Nonempty) :
    let V : G.OpenSubgroupIndex := OrderDual.toDual
      (G.residueUnramifiedOpenSubgroupOf E)
    let W : G.OpenSubgroupIndex := OrderDual.toDual
      (G.unramifiedKummerOpenSubgroup E pi hpi n hn)
    let B := G.fixedFieldFiniteExtension
      (G.residueUnramifiedIndex_le_unramifiedKummerIndex E pi hpi n hn)
    letI := B.algebra
    Module.finrank (G.fixedFieldPointed V) (G.fixedFieldPointed W) = n := by
  let U := G.residueUnramifiedOpenSubgroupOf E
  let V : G.OpenSubgroupIndex := OrderDual.toDual U
  let W : G.OpenSubgroupIndex := OrderDual.toDual
    (G.unramifiedKummerOpenSubgroup E pi hpi n hn)
  let K := G.presentation
  let L := G.fixedField V
  let LP := G.fixedFieldPointed V
  let A := K.algebraicClosure
  let BK := G.fixedFieldBaseExtension V
  let B := G.fixedFieldFiniteExtension
    (G.residueUnramifiedIndex_le_unramifiedKummerIndex E pi hpi n hn)
  letI : Algebra K L := BK.algebra
  letI := B.algebra
  letI := B.finiteDimensional
  letI := B.valuativeExtension
  letI := K.nontriviallyNormedField
  letI := K.isUltrametricDist
  letI := K.completeSpace
  letI := G.fixedFieldNontriviallyNormedField V
  letI := G.fixedFieldIsUltrametricDist V
  letI : ValuativeRel L := G.fixedFieldValuativeRel V
  letI : ValuativeExtension K L := BK.valuativeExtension
  letI : Algebra LP A := LP.algebra
  letI : IsScalarTower K LP A := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro x
    change algebraMap K A x =
      @algebraMap (G.fixedField V) (G.fixedFieldPointed V).algebraicClosure
        _ _ (G.fixedFieldPointed V).algebra
        (algebraMap K (G.fixedField V) x)
    rw [G.fixedFieldPointed_algebraMap_apply]
    exact (IntermediateField.coe_algebraMap_apply (G.fixedField V) x).symm)
  let piL : LocalIntegerRing LP := algebraMap (LocalIntegerRing K) 𝒪[L] pi
  have hcomp := G.uniformizerKummer_restrictScalars_eq_unramifiedKummerCompositum
    E pi hpi n hn
  let M := G.fixedField W
  let N := LCFT.uniformizerKummerIntermediateField LP piL n
  have hMN : N.restrictScalars K = M :=
    hcomp.trans (G.unramifiedKummer_fixedField_eq E pi hpi n hn).symm
  let f : M →ₐ[LP] N :=
    { toFun := fun x => ⟨x, by
        have hx : (x : K.algebraicClosure) ∈ M := x.property
        exact Eq.mp
          (congrArg (fun F : IntermediateField K A =>
            ((x : K.algebraicClosure) ∈ F)) hMN.symm) hx⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have hval := congrArg (fun z : N => (z : A)) hxy
      exact Subtype.ext hval
    · intro y
      have hy : (y : K.algebraicClosure) ∈ N.restrictScalars K := y.property
      have hy' : (y : K.algebraicClosure) ∈ M := Eq.mp
        (congrArg (fun F : IntermediateField K A =>
          ((y : K.algebraicClosure) ∈ F)) hMN) hy
      exact ⟨⟨y, hy'⟩, Subtype.ext rfl⟩
  let e : M ≃ₐ[LP] N := AlgEquiv.ofBijective f hf
  change Module.finrank LP M = n
  rw [e.toLinearEquiv.finrank_eq]
  apply LCFT.uniformizerKummerIntermediateField_finrank LP piL _ n hn hroot
  exact G.residueUnramifiedOf_map_uniformizer_span E pi hpi

set_option maxHeartbeats 1600000 in
-- The inertia-cardinality upper bound unfolds both nested spectral fixed-field structures.
/-- The unramified--Kummer compositum has ramification index exactly `n` over the original
field. The unramified layer contributes no ramification, while its Kummer layer contributes
exactly `n`. -/
theorem unramifiedKummer_relativeRamificationIndex_eq
    (E : G.ResidueFiniteGaloisIntermediateField)
    (pi : LocalIntegerRing G.presentation)
    (hpi : Ideal.span {pi} = localMaximalIdeal G.presentation)
    (n : ℕ) (hn : 0 < n)
    (hroot : (primitiveRoots n (G.fixedFieldPointed
      (OrderDual.toDual (G.residueUnramifiedOpenSubgroupOf E)))).Nonempty) :
    (G.fixedFieldBaseExtension (OrderDual.toDual
      (G.unramifiedKummerOpenSubgroup E pi hpi n hn))).relativeRamificationIndex = n := by
  let U := G.residueUnramifiedOpenSubgroupOf E
  let V : G.OpenSubgroupIndex := OrderDual.toDual U
  let T := G.unramifiedKummerOpenSubgroup E pi hpi n hn
  let W : G.OpenSubgroupIndex := OrderDual.toDual T
  let K := G.presentation
  let L := G.fixedField V
  let M := G.fixedField W
  let MP := G.fixedFieldPointed W
  let A := K.algebraicClosure
  let EKL := G.fixedFieldBaseExtension V
  let EKM := G.fixedFieldBaseExtension W
  let ELM := G.fixedFieldFiniteExtension
    (G.residueUnramifiedIndex_le_unramifiedKummerIndex E pi hpi n hn)
  letI : NeZero n := ⟨hn.ne'⟩
  letI := K.nontriviallyNormedField
  letI := K.isUltrametricDist
  letI := K.completeSpace
  letI := G.fixedFieldNontriviallyNormedField V
  letI := G.fixedFieldIsUltrametricDist V
  letI : ValuativeRel L := G.fixedFieldValuativeRel V
  letI := G.fixedFieldNontriviallyNormedField W
  letI := G.fixedFieldIsUltrametricDist W
  letI : ValuativeRel M := G.fixedFieldValuativeRel W
  letI : TopologicalSpace M := G.fixedFieldTopologicalSpace W
  letI : IsNonarchimedeanLocalField M := G.fixedFieldIsNonarchimedeanLocalField W
  letI : Algebra K L := EKL.algebra
  letI : ValuativeExtension K L := EKL.valuativeExtension
  letI : Algebra K M := EKM.algebra
  letI : ValuativeExtension K M := EKM.valuativeExtension
  letI : FiniteDimensional K M := EKM.finiteDimensional
  letI : Algebra L M := ELM.algebra
  letI : ValuativeExtension L M := ELM.valuativeExtension
  letI : FiniteDimensional L M := ELM.finiteDimensional
  letI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro x
    rfl)
  letI : IsGalois K M :=
    G.fixedField_isGalois_of_normal T
      (G.unramifiedKummerOpenSubgroup_normal E pi hpi n hn)
  letI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  letI : IsScalarTower K K M := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (LocalIntegerRing K) 𝒪[M] M :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra M A := MP.algebra
  letI : IsScalarTower K M A := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro x
    change algebraMap K A x =
      @algebraMap (G.fixedField W) (G.fixedFieldPointed W).algebraicClosure
        _ _ (G.fixedFieldPointed W).algebra
        (algebraMap K (G.fixedField W) x)
    rw [G.fixedFieldPointed_algebraMap_apply]
    exact (IntermediateField.coe_algebraMap_apply (G.fixedField W) x).symm)
  letI : MulSemiringAction (M ≃ₐ[K] M) 𝒪[M] :=
    SpectralLocalField.integerMulSemiringAction K K M
  let I : Subgroup (M ≃ₐ[K] M) :=
    (IsLocalRing.maximalIdeal 𝒪[M]).inertia (M ≃ₐ[K] M)
  have hlower : n ≤ EKM.relativeRamificationIndex := by
    let alpha : M := ⟨(LCFT.uniformizerKummerRoot K pi n : A), by
      have hmem : (LCFT.uniformizerKummerRoot K pi n : A) ∈
          (G.unramifiedKummerCompositum E pi hpi n hn).toIntermediateField :=
        G.uniformizerKummerFiniteGaloisIntermediateField_le_unramifiedKummerCompositum
          E pi hpi n hn (LCFT.uniformizerKummerRoot K pi n).property
      exact Eq.mp
        (congrArg (fun F : IntermediateField K A =>
          ((LCFT.uniformizerKummerRoot K pi n : A) ∈ F))
          (G.unramifiedKummer_fixedField_eq E pi hpi n hn).symm) hmem⟩
    have halpha_pow : alpha ^ n = algebraMap K M (pi : K) := by
      apply Subtype.ext
      change (LCFT.uniformizerKummerRoot K pi n : A) ^ n =
        algebraMap K A (pi : K)
      exact congrArg Subtype.val (LCFT.uniformizerKummerRoot_pow K pi n)
    have halpha_integral : IsIntegral (LocalIntegerRing K) alpha := by
      let f : (LocalIntegerRing K)[X] := X ^ n - C pi
      refine ⟨f, monic_X_pow_sub_C _ hn.ne', ?_⟩
      change Polynomial.aeval alpha f = 0
      rw [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
        Polynomial.eval₂_C]
      change alpha ^ n - algebraMap (LocalIntegerRing K) M pi = 0
      rw [halpha_pow]
      exact sub_self _
    let alphaO : LocalIntegerRing MP :=
      ⟨alpha, Valuation.Integers.mem_of_integral
        (Valuation.integer.integers (valuation M)) halpha_integral.tower_top⟩
    have halphaO_pow : alphaO ^ n =
        algebraMap (LocalIntegerRing K) (LocalIntegerRing MP) pi := by
      apply Subtype.ext
      exact halpha_pow
    have hpimem : pi ∈ localMaximalIdeal K := by
      rw [← hpi]
      exact Ideal.mem_span_singleton.mpr (dvd_refl _)
    have hpimap : algebraMap (LocalIntegerRing K) (LocalIntegerRing MP) pi ∈
        localMaximalIdeal MP :=
      IsLocalRing.map_maximalIdeal_le
        (algebraMap (LocalIntegerRing K) (LocalIntegerRing MP))
        (Ideal.mem_map_of_mem _ hpimem)
    have halpha_mem : alphaO ∈ localMaximalIdeal MP := by
      apply Ideal.IsPrime.mem_of_pow_mem inferInstance n
      rw [halphaO_pow]
      exact hpimap
    have hmap_le : (localMaximalIdeal K).map
        (algebraMap (LocalIntegerRing K) (LocalIntegerRing MP)) ≤
          localMaximalIdeal MP ^ n := by
      rw [← hpi, Ideal.map_span, Set.image_singleton, ← halphaO_pow,
        ← Ideal.span_singleton_pow]
      exact Ideal.pow_right_mono
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr halpha_mem)) n
    have hpow_le : localMaximalIdeal MP ^ EKM.relativeRamificationIndex ≤
        localMaximalIdeal MP ^ n := by
      rw [← EKM.map_localMaximalIdeal_eq_pow]
      exact hmap_le
    have hc := Order.coheight_anti hpow_le
    simpa only [IsDiscreteValuationRing.coheight_pow_maximalIdeal,
      ENat.coe_le_coe] using hc
  have hmapI : G.spectralInertiaSubgroup.map
      (AlgEquiv.restrictNormalHom M) = I :=
    G.map_spectralInertiaSubgroup_restrictNormalHom T
      (G.unramifiedKummerOpenSubgroup_normal E pi hpi n hn)
  have hfixL (tau : I) (x : L) : tau.1 (algebraMap L M x) = algebraMap L M x := by
    have htau : tau.1 ∈ G.spectralInertiaSubgroup.map
        (AlgEquiv.restrictNormalHom M) := by
      rw [hmapI]
      exact tau.property
    obtain ⟨sigma, hsigma, hsigma_tau⟩ := htau
    have hsigmaU : sigma ∈ U.toSubgroup :=
      G.spectralInertiaSubgroup_le_residueUnramifiedOpenSubgroupOf E hsigma
    apply Subtype.ext
    rw [← hsigma_tau]
    change algebraMap M A
        ((AlgEquiv.restrictNormalHom M sigma) (algebraMap L M x)) =
      algebraMap M A (algebraMap L M x)
    have hy : algebraMap M A (algebraMap L M x) = ((x : L) : A) := by
      change @algebraMap (G.fixedField W)
          (G.fixedFieldPointed W).algebraicClosure _ _
          (G.fixedFieldPointed W).algebra (algebraMap L M x) = ((x : L) : A)
      rw [G.fixedFieldPointed_algebraMap_apply]
      rfl
    calc
      algebraMap M A
          ((AlgEquiv.restrictNormalHom M sigma) (algebraMap L M x)) =
          sigma (algebraMap M A (algebraMap L M x)) :=
        AlgEquiv.restrictNormal_commutes sigma M (algebraMap L M x)
      _ = sigma ((x : L) : A) := by rw [hy]
      _ = ((x : L) : A) := (IntermediateField.mem_fixedField_iff
        (H := U.toSubgroup) ((x : L) : A)).mp x.property sigma hsigmaU
      _ = algebraMap M A (algebraMap L M x) := hy.symm
  let f : I → (M ≃ₐ[L] M) := fun tau =>
    { toRingEquiv := tau.1.toRingEquiv
      commutes' := hfixL tau }
  have hf : Function.Injective f := by
    intro sigma tau h
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    exact DFunLike.congr_fun h x
  have hupper : EKM.relativeRamificationIndex ≤ n := by
    calc
      EKM.relativeRamificationIndex = Nat.card I := by
        symm
        exact G.fixedFieldFiniteInertia_card T
          (G.unramifiedKummerOpenSubgroup_normal E pi hpi n hn)
      _ ≤ Nat.card (M ≃ₐ[L] M) := Nat.card_le_card_of_injective f hf
      _ = Module.finrank L M := IsGalois.card_aut_eq_finrank L M
      _ = n := G.unramifiedKummer_fixedField_finrank_over_unramified
        E pi hpi n hn hroot
  exact Nat.le_antisymm hupper hlower

end Anabelian.OTriangle.LocalGaloisGroup
