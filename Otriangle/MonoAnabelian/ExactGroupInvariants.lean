import Otriangle.MonoAnabelian.ExactReciprocityRank
import Otriangle.MonoAnabelian.PrimeToTorsionReciprocity
import Otriangle.MonoAnabelian.GroupInvariants

/-!
# Exact group-theoretic numerical invariants

The two local arithmetic calculations now evaluate all three integers in Hoshi's Definition
3.5.  The residue-characteristic mod-power rank recovers `[K : Q_p] = e f`, the prime-to-`p`
torsion quotient recovers `f`, and their quotient recovers `e`.
-/

noncomputable section

namespace Anabelian

open OTriangle

universe u

namespace LCFT

/-- The exact mod-`p` rank of the torsion-free abelianized local Galois group. -/
theorem abelianizedTorsionFree_modPowerRank_eq_residueDegreeProduct_succ
    {K : PointedMixedCharLocalField.{u}} (rec : LocalReciprocityMap K) :
    OTriangle.GroupTheoreticInvariants.modPowerRank
        (OTriangle.GroupTheoreticInvariants.torsionFreeQuotient
          (AbelianizedAbsoluteGaloisGroup K)) K.residueChar =
      absoluteRamificationIndex K * localResidueDegree K + 1 := by
  unfold OTriangle.GroupTheoreticInvariants.modPowerRank
  change Nat.log K.residueChar
      (Nat.card
        (AbelianizedTorsionFreeModPowerQuotient K K.residueChar)) = _
  rw [abelianizedTorsionFreeModPowerQuotient_card_eq_residueDegreeProduct_succ rec,
    Nat.log_pow (Fact.out : K.residueChar.Prime).one_lt]

/-- Hoshi's group-theoretic absolute-degree invariant is the product `e f`. -/
theorem abelianized_groupTheoreticAbsoluteDegree_eq_residueDegreeProduct
    {K : PointedMixedCharLocalField.{u}} (rec : LocalReciprocityMap K) :
    OTriangle.GroupTheoreticInvariants.absoluteDegree
        (AbelianizedAbsoluteGaloisGroup K) K.residueChar =
      absoluteRamificationIndex K * localResidueDegree K := by
  unfold OTriangle.GroupTheoreticInvariants.absoluteDegree
  rw [abelianizedTorsionFree_modPowerRank_eq_residueDegreeProduct_succ rec]
  omega

/-- Hoshi's group-theoretic residue-degree invariant is the usual residue degree. -/
theorem abelianized_groupTheoreticResidueDegree_eq_localResidueDegree
    {K : PointedMixedCharLocalField.{u}} (rec : LocalReciprocityMap K) :
    OTriangle.GroupTheoreticInvariants.residueDegree
        (AbelianizedAbsoluteGaloisGroup K) K.residueChar =
      localResidueDegree K := by
  unfold OTriangle.GroupTheoreticInvariants.residueDegree
  rw [one_add_abelianizedPrimeToTorsionQuotient_card_eq_residueChar_pow_residueDegree rec,
    Nat.log_pow (Fact.out : K.residueChar.Prime).one_lt]

/-- Hoshi's group-theoretic ramification-index invariant is the absolute ramification index. -/
theorem abelianized_groupTheoreticRamificationIndex_eq_absoluteRamificationIndex
    {K : PointedMixedCharLocalField.{u}} (rec : LocalReciprocityMap K) :
    OTriangle.GroupTheoreticInvariants.ramificationIndex
        (AbelianizedAbsoluteGaloisGroup K) K.residueChar =
      absoluteRamificationIndex K := by
  unfold OTriangle.GroupTheoreticInvariants.ramificationIndex
  rw [abelianized_groupTheoreticAbsoluteDegree_eq_residueDegreeProduct rec,
    abelianized_groupTheoreticResidueDegree_eq_localResidueDegree rec]
  rw [Nat.mul_comm]
  exact Nat.mul_div_cancel_left _ (localResidueDegree_pos K)

end LCFT

namespace OTriangle.LocalGaloisGroup

/-- The exact group-theoretic absolute degree of a presented local Galois group. -/
theorem groupTheoreticAbsoluteDegree_eq_residueDegreeProduct
    (G : LocalGaloisGroup.{u})
    (rec : LCFT.LocalReciprocityMap G.presentation) :
    G.groupTheoreticAbsoluteDegree G.presentation.residueChar =
      LCFT.absoluteRamificationIndex G.presentation *
        LCFT.localResidueDegree G.presentation :=
  LCFT.abelianized_groupTheoreticAbsoluteDegree_eq_residueDegreeProduct rec

/-- The exact group-theoretic residue degree of a presented local Galois group. -/
theorem groupTheoreticResidueDegree_eq_localResidueDegree
    (G : LocalGaloisGroup.{u})
    (rec : LCFT.LocalReciprocityMap G.presentation) :
    G.groupTheoreticResidueDegree G.presentation.residueChar =
      LCFT.localResidueDegree G.presentation :=
  LCFT.abelianized_groupTheoreticResidueDegree_eq_localResidueDegree rec

/-- The exact group-theoretic ramification index of a presented local Galois group. -/
theorem groupTheoreticRamificationIndex_eq_absoluteRamificationIndex
    (G : LocalGaloisGroup.{u})
    (rec : LCFT.LocalReciprocityMap G.presentation) :
    G.groupTheoreticRamificationIndex G.presentation.residueChar =
      LCFT.absoluteRamificationIndex G.presentation :=
  LCFT.abelianized_groupTheoreticRamificationIndex_eq_absoluteRamificationIndex rec

end OTriangle.LocalGaloisGroup
end Anabelian
