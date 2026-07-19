import Otriangle.MonoAnabelian.ResidueCharacteristicReciprocityRank
import Otriangle.MonoAnabelian.GroupInvariants

/-!
# Identification of the residue-characteristic candidate

The reciprocity rank calculations identify Hoshi's group-theoretic candidate prime: away from
the residue characteristic the mod-power rank is one, while at the residue characteristic it is
at least two.
-/

noncomputable section

namespace Anabelian.OTriangle.LocalGaloisGroup

universe u

/-- Hoshi's mod-power candidate predicate singles out the residue characteristic of the local
field presentation. -/
theorem isResidueCharacteristicCandidate_iff_reciprocity
    (G : LocalGaloisGroup.{u})
    (rec : LCFT.LocalReciprocityMap G.presentation) (l : ℕ) :
    G.IsResidueCharacteristicCandidate l ↔
      l = G.presentation.residueChar := by
  constructor
  · rintro ⟨hl, hrank⟩
    by_contra hne
    have hcard :=
      LCFT.abelianizedTorsionFreeModPowerQuotient_card_eq_prime
        rec l hl hne
    have hrankEq : G.abelianizationModPowerRank l = 1 := by
      unfold abelianizationModPowerRank
      unfold GroupTheoreticInvariants.modPowerRank
      change Nat.log l
        (Nat.card (LCFT.AbelianizedTorsionFreeModPowerQuotient
          G.presentation l)) = 1
      rw [hcard, Nat.log_of_one_lt_of_le hl.one_lt le_rfl,
        Nat.div_self hl.pos, Nat.log_one_right]
    omega
  · intro hl
    subst l
    refine ⟨Fact.out, ?_⟩
    unfold abelianizationModPowerRank
    unfold GroupTheoreticInvariants.modPowerRank
    change 2 ≤ Nat.log G.presentation.residueChar
      (Nat.card (LCFT.AbelianizedTorsionFreeModPowerQuotient
        G.presentation G.presentation.residueChar))
    exact Nat.le_log_of_pow_le (Fact.out : G.presentation.residueChar.Prime).one_lt
      (LCFT.abelianizedTorsionFreeModPowerQuotient_card_ge_residueChar_sq rec)

end Anabelian.OTriangle.LocalGaloisGroup
