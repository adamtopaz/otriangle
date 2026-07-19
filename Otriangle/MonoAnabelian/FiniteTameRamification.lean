import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Finite tame ramification

For a finite faithful group action on a discrete valuation ring, the tame character sends an
inertia automorphism to its multiplier on a uniformizer, reduced to the residue field.  Its kernel
has no torsion prime to the residue characteristic.  Consequently, when the inertia group has
prime-to-`p` order, the tame character is injective.  The final conjugation theorem identifies the
action of a residue Frobenius on inertia with the corresponding power map.
-/

noncomputable section

namespace Anabelian.OTriangle.FiniteTameRamification

variable (R G : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Group G] [MulSemiringAction G R]

abbrev inertia : Subgroup G := (IsLocalRing.maximalIdeal R).inertia G

def uniformizer : R :=
  (IsDiscreteValuationRing.exists_irreducible R).choose

theorem uniformizer_irreducible : Irreducible (uniformizer R) :=
  (IsDiscreteValuationRing.exists_irreducible R).choose_spec

theorem uniformizer_ne_zero : uniformizer R ≠ 0 :=
  (uniformizer_irreducible R).ne_zero

def transportUnit (g : G) : Rˣ :=
  (IsDiscreteValuationRing.associated_of_irreducible R
    (uniformizer_irreducible R)
    ((uniformizer_irreducible R).map
      (MulSemiringAction.toRingAut G R g))).choose

abbrev tameUnit (g : inertia R G) : Rˣ := transportUnit R G g.1

theorem uniformizer_mul_transportUnit (g : G) :
    uniformizer R * (transportUnit R G g : R) = g • uniformizer R :=
  by
    change uniformizer R * (transportUnit R G g : R) =
      (MulSemiringAction.toRingAut G R g) (uniformizer R)
    exact (IsDiscreteValuationRing.associated_of_irreducible R
      (uniformizer_irreducible R)
      ((uniformizer_irreducible R).map
        (MulSemiringAction.toRingAut G R g))).choose_spec

theorem uniformizer_mul_tameUnit (g : inertia R G) :
    uniformizer R * (tameUnit R G g : R) = g.1 • uniformizer R :=
  uniformizer_mul_transportUnit R G g.1

theorem transportUnit_one : transportUnit R G 1 = 1 := by
  apply Units.ext
  apply mul_left_cancel₀ (uniformizer_ne_zero R)
  simp only [uniformizer_mul_transportUnit, one_smul, Units.val_one, mul_one]

theorem inertia_residue_smul (g : inertia R G) (x : R) :
    IsLocalRing.residue R (g.1 • x) = IsLocalRing.residue R x := by
  have hx := g.2 x
  change g.1 • x - x ∈ IsLocalRing.maximalIdeal R at hx
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at hx
  exact hx

theorem transportUnit_mul (g h : G) :
    transportUnit R G (g * h) =
      transportUnit R G g * Units.map (MulSemiringAction.toRingAut G R g)
        (transportUnit R G h) := by
  apply Units.ext
  apply mul_left_cancel₀ (uniformizer_ne_zero R)
  rw [Units.val_mul, Units.coe_map]
  calc
    uniformizer R * (transportUnit R G (g * h) : R) =
        (g * h) • uniformizer R := uniformizer_mul_transportUnit R G (g * h)
    _ = g • (h • uniformizer R) := mul_smul g h (uniformizer R)
    _ = g • (uniformizer R * (transportUnit R G h : R)) := by
      rw [uniformizer_mul_transportUnit]
    _ = (g • uniformizer R) * (g • (transportUnit R G h : R)) :=
      map_mul (MulSemiringAction.toRingAut G R g) _ _
    _ = (uniformizer R * (transportUnit R G g : R)) *
        (g • (transportUnit R G h : R)) := by rw [uniformizer_mul_transportUnit]
    _ = uniformizer R * ((transportUnit R G g : R) *
        (g • (transportUnit R G h : R))) := mul_assoc _ _ _

theorem tameUnit_mul (g h : inertia R G) :
    tameUnit R G (g * h) =
      tameUnit R G g * Units.map (MulSemiringAction.toRingAut G R g.1)
        (tameUnit R G h) :=
  transportUnit_mul R G g.1 h.1

noncomputable def residueAction : G →* RingAut (IsLocalRing.ResidueField R) :=
  IsLocalRing.ResidueField.mapAut.comp (MulSemiringAction.toRingAut G R)

theorem mem_inertia_iff_residueAction_eq_one (g : G) :
    g ∈ inertia R G ↔ residueAction R G g = 1 := by
  constructor
  · intro hg
    apply RingEquiv.ext
    intro z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    change IsLocalRing.residue R (g • x) = IsLocalRing.residue R x
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hg x
  · intro hg x
    change g • x - x ∈ IsLocalRing.maximalIdeal R
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    have hz := DFunLike.congr_fun hg (IsLocalRing.residue R x)
    exact hz

theorem inertia_smul_residue (g : inertia R G)
    (z : IsLocalRing.ResidueField R) : g.1 • z = z := by
  have hg := (mem_inertia_iff_residueAction_eq_one R G g.1).mp g.2
  exact DFunLike.congr_fun hg z

def conjugate (s : G) (g : inertia R G) : inertia R G :=
  ⟨s * g.1 * s⁻¹, (mem_inertia_iff_residueAction_eq_one R G _).mpr (by
    rw [map_mul, map_mul, map_inv,
      (mem_inertia_iff_residueAction_eq_one R G g.1).mp g.2]
    simp)⟩

def tameCharacter : inertia R G →* (IsLocalRing.ResidueField R)ˣ where
  toFun g := Units.map (IsLocalRing.residue R).toMonoidHom (tameUnit R G g)
  map_one' := by
    apply Units.ext
    change IsLocalRing.residue R (tameUnit R G 1 : R) = 1
    have hu := uniformizer_mul_tameUnit R G 1
    have hu' : uniformizer R * (tameUnit R G 1 : R) = uniformizer R := by
      simpa only [Subgroup.coe_one, one_smul] using hu
    have hu'' : uniformizer R * (tameUnit R G 1 : R) = uniformizer R * 1 := by
      simpa only [mul_one] using hu'
    have := mul_left_cancel₀ (uniformizer_ne_zero R) hu''
    rw [this, map_one]
  map_mul' := fun g h => by
    apply Units.ext
    rw [Units.val_mul]
    change IsLocalRing.residue R (tameUnit R G (g * h) : R) =
      IsLocalRing.residue R (tameUnit R G g : R) *
        IsLocalRing.residue R (tameUnit R G h : R)
    rw [tameUnit_mul]
    rw [Units.val_mul, Units.coe_map, map_mul]
    change IsLocalRing.residue R (tameUnit R G g : R) *
      IsLocalRing.residue R (g.1 • (tameUnit R G h : R)) = _
    rw [inertia_residue_smul]

theorem tameCharacter_conjugate (s : G) (g : inertia R G) :
    tameCharacter R G (conjugate R G s g) =
      Units.map (residueAction R G s) (tameCharacter R G g) := by
  apply Units.ext
  change IsLocalRing.residue R (transportUnit R G (s * g.1 * s⁻¹) : R) =
    residueAction R G s (IsLocalRing.residue R (transportUnit R G g.1 : R))
  have hcancelUnits : transportUnit R G s *
      Units.map (MulSemiringAction.toRingAut G R s) (transportUnit R G s⁻¹) = 1 := by
    rw [← transportUnit_mul, mul_inv_cancel, transportUnit_one]
  have hcancel : IsLocalRing.residue R (transportUnit R G s : R) *
      s • IsLocalRing.residue R (transportUnit R G s⁻¹ : R) = 1 := by
    have hc := congrArg
      (fun u : Rˣ ↦ Units.map (IsLocalRing.residue R).toMonoidHom u) hcancelUnits
    have hcval := congrArg Units.val hc
    simp only [Units.val_mul, Units.coe_map, map_mul, map_one] at hcval
    change IsLocalRing.residue R (transportUnit R G s : R) *
      IsLocalRing.residue R (s • (transportUnit R G s⁻¹ : R)) = 1 at hcval
    rwa [IsLocalRing.ResidueField.residue_smul] at hcval
  rw [transportUnit_mul, transportUnit_mul]
  simp only [Units.val_mul, Units.coe_map, map_mul]
  rw [← map_mul (MulSemiringAction.toRingAut G R) s g.1]
  change IsLocalRing.residue R (transportUnit R G s : R) *
      IsLocalRing.residue R (s • (transportUnit R G g.1 : R)) *
        IsLocalRing.residue R ((s * g.1) • (transportUnit R G s⁻¹ : R)) =
    s • IsLocalRing.residue R (transportUnit R G g.1 : R)
  rw [IsLocalRing.ResidueField.residue_smul,
    IsLocalRing.ResidueField.residue_smul, mul_smul,
    inertia_smul_residue R G]
  change IsLocalRing.residue R (transportUnit R G s : R) *
      (s • IsLocalRing.residue R (transportUnit R G g.1 : R)) *
        (s • IsLocalRing.residue R (transportUnit R G s⁻¹ : R)) = _
  calc
    _ = (s • IsLocalRing.residue R (transportUnit R G g.1 : R)) *
        (IsLocalRing.residue R (transportUnit R G s : R) *
          (s • IsLocalRing.residue R (transportUnit R G s⁻¹ : R))) := by ring
    _ = _ := by rw [hcancel, mul_one]

theorem tameUnit_residue_eq_one_of_mem_ker
    (g : inertia R G) (hg : g ∈ (tameCharacter R G).ker) :
    IsLocalRing.residue R (tameUnit R G g : R) = 1 := by
  have hg' : tameCharacter R G g = 1 := hg
  exact congrArg Units.val hg'

theorem smul_sub_self_mem_pow_succ_of_mem_ker
    (g : inertia R G) (hg : g ∈ (tameCharacter R G).ker)
    (n : ℕ) {x : R} (hx : x ∈ (IsLocalRing.maximalIdeal R) ^ n) :
    g.1 • x - x ∈ (IsLocalRing.maximalIdeal R) ^ (n + 1) := by
  let π := uniformizer R
  let u : R := tameUnit R G g
  have hπ : IsLocalRing.maximalIdeal R = Ideal.span {π} :=
    (uniformizer_irreducible R).maximalIdeal_eq
  rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx ⊢
  obtain ⟨a, rfl⟩ := hx
  have hu : IsLocalRing.residue R u = 1 :=
    tameUnit_residue_eq_one_of_mem_ker R G g hg
  have ha : IsLocalRing.residue R (g.1 • a) = IsLocalRing.residue R a :=
    inertia_residue_smul R G g a
  have hbracket : u ^ n * (g.1 • a) - a ∈ IsLocalRing.maximalIdeal R := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_mul, map_pow, hu, one_pow,
      one_mul, ha, sub_self]
  rw [hπ, Ideal.mem_span_singleton] at hbracket
  obtain ⟨b, hb⟩ := hbracket
  refine ⟨b, ?_⟩
  have hπg : (MulSemiringAction.toRingAut G R g.1) π = π * u := by
    simpa [π, u] using (uniformizer_mul_tameUnit R G g).symm
  change (MulSemiringAction.toRingAut G R g.1) (π ^ n * a) -
      π ^ n * a = π ^ (n + 1) * b
  rw [map_mul, map_pow, hπg]
  change (π * u) ^ n * (g.1 • a) - π ^ n * a = π ^ (n + 1) * b
  rw [mul_pow, mul_assoc, ← mul_sub, hb, pow_add, pow_one]
  ring

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem sum_pow_smul_sub_self (g : G) (r : ℕ) (x : R) :
    ∑ i ∈ Finset.range r, (g ^ i) • (g • x - x) = g ^ r • x - x := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.sum_range_succ, ih, pow_succ, mul_smul]
      simp only [smul_sub]
      abel

theorem eq_one_of_mem_tameCharacter_ker_of_pow_eq_one
    [FaithfulSMul G R] (g : inertia R G) (r : ℕ)
    (hg : g ∈ (tameCharacter R G).ker) (hgr : g ^ r = 1)
    (hr : IsUnit (r : R)) : g = 1 := by
  apply Subtype.ext
  apply eq_of_smul_eq_smul (α := R)
  intro x
  change g.1 • x = (1 : G) • x
  rw [one_smul, ← sub_eq_zero]
  apply (Ideal.mem_bot).mp
  rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing
    (IsLocalRing.maximalIdeal R) Ideal.IsPrime.ne_top']
  rw [Ideal.mem_iInf]
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      let y := g.1 • x - x
      have hterm (i : ℕ) :
          (g ^ i).1 • y - y ∈ (IsLocalRing.maximalIdeal R) ^ (n + 1) := by
        apply smul_sub_self_mem_pow_succ_of_mem_ker R G (g ^ i)
        · change tameCharacter R G (g ^ i) = 1
          rw [map_pow]
          change tameCharacter R G g = 1 at hg
          rw [hg, one_pow]
        · exact ih
      have hsum : ∑ i ∈ Finset.range r, ((g ^ i).1 • y - y) ∈
          (IsLocalRing.maximalIdeal R) ^ (n + 1) := by
        exact Ideal.sum_mem _ fun i _ ↦ hterm i
      have htel : ∑ i ∈ Finset.range r, (g ^ i).1 • y = 0 := by
        have ht := sum_pow_smul_sub_self R G g.1 r x
        have hpow : g.1 ^ r = (1 : G) := congrArg Subtype.val hgr
        rw [hpow, one_smul, sub_self] at ht
        simpa [y] using ht
      have hry : (r : R) * y ∈ (IsLocalRing.maximalIdeal R) ^ (n + 1) := by
        have hsum' :
            (∑ i ∈ Finset.range r, (g ^ i).1 • y) - (r : R) * y ∈
              (IsLocalRing.maximalIdeal R) ^ (n + 1) := by
          simpa [Finset.sum_sub_distrib] using hsum
        rw [htel, zero_sub] at hsum'
        exact (Ideal.neg_mem_iff _).mp hsum'
      exact (Ideal.mul_unit_mem_iff_mem _ hr).mp (by simpa [mul_comm] using hry)

theorem natCast_isUnit_of_coprime_residueChar
    (p r : ℕ) [CharP (IsLocalRing.ResidueField R) p]
    (hp : p.Prime) (hcop : Nat.Coprime r p) : IsUnit (r : R) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit (r : R)).mp
  rw [map_natCast]
  apply (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField R) p r).not.mpr
  exact hp.coprime_iff_not_dvd.mp hcop.symm

theorem tameCharacter_injective_of_coprime_card
    [Finite G] [FaithfulSMul G R]
    (p : ℕ) [CharP (IsLocalRing.ResidueField R) p]
    (hp : p.Prime) (hcop : Nat.Coprime (Nat.card (inertia R G)) p) :
    Function.Injective (tameCharacter R G) := by
  rw [← (tameCharacter R G).ker_eq_bot_iff]
  apply (Subgroup.eq_bot_iff_forall (tameCharacter R G).ker).mpr
  intro g hg
  apply eq_one_of_mem_tameCharacter_ker_of_pow_eq_one R G g (orderOf g) hg
  · exact pow_orderOf_eq_one g
  · apply natCast_isUnit_of_coprime_residueChar R p (orderOf g) hp
    exact Nat.Coprime.of_dvd_left (orderOf_dvd_natCard g) hcop

theorem conjugate_eq_pow_of_residue_frobenius
    (s : G) (q : ℕ)
    (hinj : Function.Injective (tameCharacter R G))
    (hfrob : ∀ z : IsLocalRing.ResidueField R, s • z = z ^ q)
    (g : inertia R G) : conjugate R G s g = g ^ q := by
  apply hinj
  rw [tameCharacter_conjugate, map_pow]
  apply Units.ext
  change s • IsLocalRing.residue R (transportUnit R G g.1 : R) =
    IsLocalRing.residue R (transportUnit R G g.1 : R) ^ q
  exact hfrob _

end Anabelian.OTriangle.FiniteTameRamification
