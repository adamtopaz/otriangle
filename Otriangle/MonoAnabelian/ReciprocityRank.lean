import Otriangle.MonoAnabelian.MultiplicativeRank
import Otriangle.MonoAnabelian.UnramifiedTorsionFree

/-!
# Mod-power ranks transported by local reciprocity

Local reciprocity carries the torsion-free mod-power quotient of the local multiplicative group
onto the corresponding quotient of the topological abelianized absolute Galois group.  Away from
the residue characteristic this computes the latter quotient exactly.
-/

noncomputable section

namespace Anabelian.LCFT

open OTriangle

universe u

abbrev AbelianizedTorsionFreeQuotient
    (K : PointedMixedCharLocalField.{u}) :=
  AbelianizedAbsoluteGaloisGroup K ⧸
    CommGroup.torsion (AbelianizedAbsoluteGaloisGroup K)

abbrev AbelianizedTorsionFreeModPowerQuotient
    (K : PointedMixedCharLocalField.{u}) (l : ℕ) :=
  AbelianizedTorsionFreeQuotient K ⧸
    (powMonoidHom (α := AbelianizedTorsionFreeQuotient K) l).range

noncomputable def reciprocityTorsionFreeMap
    {K : PointedMixedCharLocalField.{u}} (rec : LocalReciprocityMap K) :
    FieldTorsionFreeQuotient K →* AbelianizedTorsionFreeQuotient K :=
  QuotientGroup.map (CommGroup.torsion Kˣ)
    (CommGroup.torsion (AbelianizedAbsoluteGaloisGroup K))
    rec.toMonoidHom (by
      intro x hx
      obtain ⟨n, hn, hpow⟩ := hx.exists_pow_eq_one
      apply isOfFinOrder_iff_pow_eq_one.mpr
      exact ⟨n, hn, by rw [← map_pow, hpow, map_one]⟩)

noncomputable def reciprocityModPowerMap
    {K : PointedMixedCharLocalField.{u}} (rec : LocalReciprocityMap K) (l : ℕ) :
    FieldTorsionFreeModPowerQuotient K l →*
      AbelianizedTorsionFreeModPowerQuotient K l :=
  QuotientGroup.map
    (powMonoidHom (α := FieldTorsionFreeQuotient K) l).range
    (powMonoidHom (α := AbelianizedTorsionFreeQuotient K) l).range
    (reciprocityTorsionFreeMap rec) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨reciprocityTorsionFreeMap rec x, by simp⟩)

theorem unramifiedProjection_surjective
    (K : PointedMixedCharLocalField.{u}) :
    Function.Surjective (unramifiedProjection K) := by
  intro σ
  obtain ⟨y, hy⟩ := (unramifiedQuotientEquiv K).surjective σ
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (inertiaSubgroup K) y
  exact ⟨x, hy⟩

theorem reciprocityModPowerMap_surjective
    {K : PointedMixedCharLocalField.{u}} (rec : LocalReciprocityMap K)
    (l : ℕ) (hl : l.Prime) :
    Function.Surjective (reciprocityModPowerMap rec l) := by
  let B := AbelianizedAbsoluteGaloisGroup K
  let BT := AbelianizedTorsionFreeQuotient K
  let BQ := AbelianizedTorsionFreeModPowerQuotient K l
  let qBT : B →* BT := QuotientGroup.mk' (CommGroup.torsion B)
  let qBP : BT →* BQ := QuotientGroup.mk' (powMonoidHom (α := BT) l).range
  let RQ := ResidueAbsoluteGaloisGroup K ⧸
    (powMonoidHom (α := ResidueAbsoluteGaloisGroup K) l).range
  let qR : ResidueAbsoluteGaloisGroup K →* RQ :=
    QuotientGroup.mk' (powMonoidHom (α := ResidueAbsoluteGaloisGroup K) l).range
  intro y
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom (α := BT) l).range y
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective
    (CommGroup.torsion B) z
  letI := Fintype.ofFinite (ResidueField K)
  letI : IsGalois (ResidueField K) (AlgebraicClosureResidueField K) := ⟨⟩
  have htop : Subgroup.zpowers (qR (residueFrobenius K)) = ⊤ :=
    OTriangle.TopologicalProcyclic.quotient_zpowers_eq_top
      (residueFrobenius K) (residueFrobenius_zpowers_topologicalClosure K)
      l hl.pos
  have hbmem : qR (unramifiedProjection K b) ∈
      Subgroup.zpowers (qR (residueFrobenius K)) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨n, hn⟩ := hbmem
  have hn' : qR (residueFrobenius K ^ n) =
      qR (unramifiedProjection K b) := by
    simpa only [map_zpow] using hn
  change ((residueFrobenius K ^ n : ResidueAbsoluteGaloisGroup K) : RQ) =
    ((unramifiedProjection K b : ResidueAbsoluteGaloisGroup K) : RQ) at hn'
  rw [QuotientGroup.eq_iff_div_mem] at hn'
  have hratio :=
    (powMonoidHom (α := ResidueAbsoluteGaloisGroup K) l).range.inv_mem hn'
  obtain ⟨σ, hσ⟩ := hratio
  have hσ' : unramifiedProjection K b * (residueFrobenius K ^ n)⁻¹ = σ ^ l := by
    simpa [div_eq_mul_inv, mul_comm] using hσ.symm
  obtain ⟨c, hc⟩ := unramifiedProjection_surjective K σ
  let π := uniformizerUnit K
  let d : B := b * (rec.toMonoidHom (π ^ n))⁻¹ * (c ^ l)⁻¹
  have hdproj : unramifiedProjection K d = 1 := by
    simp only [d, map_mul, map_inv, map_pow]
    rw [map_zpow, map_zpow, rec.unramifiedProjection_uniformizer
      π (uniformizerUnit_isUniformizer K), hc]
    rw [← hσ']
    simp
  have hd : d ∈ inertiaSubgroup K :=
    (unramifiedProjection_eq_one_iff K d).mp hdproj
  obtain ⟨a, ha⟩ := rec.mapsUnits.unitsEquiv.surjective ⟨d, hd⟩
  let unit : Kˣ := integerUnitsToFieldUnits K a
  have hunit : rec.toMonoidHom unit = d := by
    have hcompat := DFunLike.congr_fun rec.mapsUnits.compatibility a
    exact hcompat.symm.trans (congrArg Subtype.val ha)
  let x : Kˣ := π ^ n * unit
  refine ⟨((x : FieldTorsionFreeQuotient K) :
    FieldTorsionFreeModPowerQuotient K l), ?_⟩
  change qBP (qBT (rec.toMonoidHom x)) = qBP (qBT b)
  change ((qBT (rec.toMonoidHom x) : BT) : BQ) = ((qBT b : BT) : BQ)
  rw [QuotientGroup.eq_iff_div_mem]
  refine ⟨qBT (c⁻¹), ?_⟩
  simp only [powMonoidHom_apply, div_eq_mul_inv]
  rw [← map_pow, ← map_inv, ← map_mul]
  apply congrArg qBT
  simp only [x, map_mul, map_zpow, hunit, d]
  rw [inv_pow]
  calc
    (c ^ l)⁻¹ =
        ((rec.toMonoidHom π) ^ n * ((rec.toMonoidHom π) ^ n)⁻¹) *
          (b * b⁻¹) * (c ^ l)⁻¹ := by simp
    _ = (rec.toMonoidHom π) ^ n *
        (b * ((rec.toMonoidHom π) ^ n)⁻¹ * (c ^ l)⁻¹) * b⁻¹ := by
      ac_rfl

noncomputable def abelianizedTorsionFreeToResidue
    (K : PointedMixedCharLocalField.{u}) :
    AbelianizedTorsionFreeQuotient K →* ResidueTorsionFreeQuotient K :=
  QuotientGroup.map
    (CommGroup.torsion (AbelianizedAbsoluteGaloisGroup K))
    (CommGroup.torsion (ResidueAbsoluteGaloisGroup K))
    (unramifiedProjection K) (by
      intro x hx
      obtain ⟨n, hn, hpow⟩ := hx.exists_pow_eq_one
      apply isOfFinOrder_iff_pow_eq_one.mpr
      exact ⟨n, hn, by rw [← map_pow, hpow, map_one]⟩)

noncomputable def abelianizedModPowerToResidue
    (K : PointedMixedCharLocalField.{u}) (l : ℕ) :
    AbelianizedTorsionFreeModPowerQuotient K l →*
      ResidueTorsionFreeModPowerQuotient K l :=
  QuotientGroup.map
    (powMonoidHom (α := AbelianizedTorsionFreeQuotient K) l).range
    (powMonoidHom (α := ResidueTorsionFreeQuotient K) l).range
    (abelianizedTorsionFreeToResidue K) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨abelianizedTorsionFreeToResidue K x, by simp⟩)

noncomputable def residueFrobeniusModPower
    (K : PointedMixedCharLocalField.{u}) (l : ℕ) :
    ResidueTorsionFreeModPowerQuotient K l :=
  ((residueFrobenius K : ResidueAbsoluteGaloisGroup K) :
    ResidueTorsionFreeQuotient K)

theorem residueFrobeniusModPower_ne_one
    (K : PointedMixedCharLocalField.{u}) (l : ℕ) (hl : l.Prime) :
    residueFrobeniusModPower K l ≠ 1 := by
  intro hg
  let qT : ResidueAbsoluteGaloisGroup K →*
      ResidueTorsionFreeQuotient K :=
    QuotientGroup.mk' (CommGroup.torsion (ResidueAbsoluteGaloisGroup K))
  have hmem : qT (residueFrobenius K) ∈
      (powMonoidHom (α := ResidueTorsionFreeQuotient K) l).range := by
    rw [← QuotientGroup.eq_one_iff]
    exact hg
  obtain ⟨z, hz⟩ := hmem
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk'_surjective
    (CommGroup.torsion (ResidueAbsoluteGaloisGroup K)) z
  change qT (σ ^ l) = qT (residueFrobenius K) at hz
  change ((σ ^ l : ResidueAbsoluteGaloisGroup K) :
      ResidueTorsionFreeQuotient K) =
    ((residueFrobenius K : ResidueAbsoluteGaloisGroup K) :
      ResidueTorsionFreeQuotient K) at hz
  rw [QuotientGroup.eq_iff_div_mem] at hz
  apply residueFrobenius_not_pow_mod_torsion K l hl σ
  have hinv := (CommGroup.torsion (ResidueAbsoluteGaloisGroup K)).inv_mem hz
  simpa [div_eq_mul_inv, mul_comm] using hinv

noncomputable def abelianizedUniformizerModPower
    {K : PointedMixedCharLocalField.{u}} (rec : LocalReciprocityMap K) (l : ℕ) :
    AbelianizedTorsionFreeModPowerQuotient K l :=
  reciprocityModPowerMap rec l (fieldUniformizerModPower K l)

theorem abelianizedModPowerToResidue_uniformizer
    {K : PointedMixedCharLocalField.{u}} (rec : LocalReciprocityMap K) (l : ℕ) :
    abelianizedModPowerToResidue K l
        (abelianizedUniformizerModPower rec l) =
      residueFrobeniusModPower K l := by
  change ((((unramifiedProjection K) (rec.toMonoidHom (uniformizerUnit K)) :
    ResidueAbsoluteGaloisGroup K) : ResidueTorsionFreeQuotient K) :
      ResidueTorsionFreeModPowerQuotient K l) =
    (((residueFrobenius K : ResidueAbsoluteGaloisGroup K) :
      ResidueTorsionFreeQuotient K) : ResidueTorsionFreeModPowerQuotient K l)
  rw [rec.unramifiedProjection_uniformizer
    (uniformizerUnit K) (uniformizerUnit_isUniformizer K)]

theorem abelianizedUniformizerModPower_ne_one
    {K : PointedMixedCharLocalField.{u}} (rec : LocalReciprocityMap K)
    (l : ℕ) (hl : l.Prime) :
    abelianizedUniformizerModPower rec l ≠ 1 := by
  intro h
  have hm := congrArg (abelianizedModPowerToResidue K l) h
  rw [map_one, abelianizedModPowerToResidue_uniformizer] at hm
  exact residueFrobeniusModPower_ne_one K l hl hm

theorem abelianizedTorsionFreeModPowerQuotient_card_eq_prime
    {K : PointedMixedCharLocalField.{u}} (rec : LocalReciprocityMap K)
    (l : ℕ) (hl : l.Prime) (hne : l ≠ K.residueChar) :
    Nat.card (AbelianizedTorsionFreeModPowerQuotient K l) = l := by
  let source := FieldTorsionFreeModPowerQuotient K l
  let target := AbelianizedTorsionFreeModPowerQuotient K l
  let f : source →* target := reciprocityModPowerMap rec l
  let gs : source := fieldUniformizerModPower K l
  let g : target := f gs
  letI : Fact l.Prime := ⟨hl⟩
  have hsourceCard : Nat.card source = l :=
    fieldTorsionFreeModPowerQuotient_card_eq_prime K l hl hne
  have hsourceTop : Subgroup.zpowers gs = ⊤ :=
    zpowers_eq_top_of_prime_card hsourceCard
      (fieldUniformizerModPower_ne_one K l hl)
  have htargetTop : Subgroup.zpowers g = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := reciprocityModPowerMap_surjective rec l hl y
    have hx : x ∈ Subgroup.zpowers gs := by
      rw [hsourceTop]
      exact Subgroup.mem_top _
    obtain ⟨n, hn⟩ := hx
    refine ⟨n, ?_⟩
    rw [← hn, map_zpow]
  have hgpow : g ^ l = 1 := by
    change f gs ^ l = 1
    rw [← map_pow]
    change f (((uniformizerUnit K : Kˣ) : FieldTorsionFreeQuotient K) ^ l) = 1
    rw [show (((uniformizerUnit K : Kˣ) : FieldTorsionFreeQuotient K) ^ l :
        source) = 1 by
      change (((((uniformizerUnit K : Kˣ) : FieldTorsionFreeQuotient K) ^ l) :
        FieldTorsionFreeQuotient K) : source) = 1
      rw [QuotientGroup.eq_one_iff]
      exact ⟨((uniformizerUnit K : Kˣ) : FieldTorsionFreeQuotient K), rfl⟩,
      map_one]
  have hgne : g ≠ 1 := abelianizedUniformizerModPower_ne_one rec l hl
  have hordNe : orderOf g ≠ 1 := by
    intro h
    exact hgne (orderOf_eq_one_iff.mp h)
  have hord : orderOf g = l :=
    (hl.eq_one_or_self_of_dvd (orderOf g)
      (orderOf_dvd_of_pow_eq_one hgpow)).resolve_left hordNe
  rw [← orderOf_eq_card_of_zpowers_eq_top htargetTop, hord]

end Anabelian.LCFT

