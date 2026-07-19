import Verso
import VersoManual
import VersoBlueprint
import Otriangle.LCFT
import Otriangle.MonoAnabelian.ResidueProcyclic
import Otriangle.MonoAnabelian.UnramifiedTorsionFree
import Otriangle.MonoAnabelian.DeepUnits
import Otriangle.MonoAnabelian.DeepPowerRoots
import Otriangle.MonoAnabelian.ResidueCharacteristicRank
import Otriangle.MonoAnabelian.ResiduePowerQuotientFinite
import Otriangle.MonoAnabelian.ResidueUnitRank
import Otriangle.MonoAnabelian.ResidueCharacteristicFieldRank
import Otriangle.MonoAnabelian.GroupTransport
import Otriangle.MonoAnabelian.GroupInvariants
import Otriangle.MonoAnabelian.IntrinsicRamification
import Otriangle.MonoAnabelian.ClassicalRamification
import Otriangle.MonoAnabelian.RamificationComparison

set_option linter.hashCommand false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Local reciprocity and group-theoretic invariants" =>

:::group "integral_mono_anabelian"
Reconstruction and rigidity for the multiplicative monoid of nonzero integers
in an algebraic closure of a mixed-characteristic local field.
:::

:::definition "integral_galois_pair" (parent := "integral_mono_anabelian") (lean := "Anabelian.OTriangle.LocalGaloisMonoid")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "29--30"
    text := some { path := "source/hoshi.txt", startLine := 1390, endLine := 1454 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-27.png" }
  }]
}
%%%

For a pointed mixed-characteristic local field $`K` with chosen algebraic
closure $`\overline K`$, write $`G_K` for its absolute Galois group and
$`\mathcal O_{\overline K}^{\triangleright}` for the commutative
multiplicative monoid of nonzero elements of the valuation ring of
$`\overline K`.  Its natural action forms the integral Galois pair
$$`G_K \curvearrowright \mathcal O_{\overline K}^{\triangleright}.`
An isomorphism of pairs consists of a profinite-group isomorphism and an
equivariant monoid isomorphism.
:::

:::theorem "local_reciprocity_input" (parent := "integral_mono_anabelian") (lean := "Anabelian.LCFT.LocalReciprocityFamily, Anabelian.LCFT.localReciprocityFamily_exists, Anabelian.LCFT.localReciprocityFamily_unique")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "15--16"
    text := some { path := "source/hoshi.txt", startLine := 618, endLine := 699 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-13.png" }
  }]
}
%%%

For every finite extension $`L/K`, local reciprocity supplies injections
$`\operatorname{rec}_K : K^\times \hookrightarrow G_K^{\mathrm{ab}}`.
It identifies $`\mathcal O_K^\times` with inertia, takes a uniformizer to
arithmetic Frobenius modulo inertia, intertwines norm with restriction, and
intertwines field inclusion with group-theoretic transfer.  The Lean structure
records these exact compatibility squares; only existence, and optionally
uniqueness, of the family is admitted.
:::

:::theorem "residue_frobenius_procyclic" (parent := "integral_mono_anabelian") (lean := "Anabelian.LCFT.residueFiniteGaloisIntermediateField, Anabelian.LCFT.residueFiniteGaloisIntermediateField_finrank, Anabelian.LCFT.residueFrobenius_restrictNormal, Anabelian.LCFT.residueFrobenius_zpowers_topologicalClosure, Anabelian.OTriangle.TopologicalProcyclic.modPower_finite, Anabelian.OTriangle.TopologicalProcyclic.modPower_card_le, Anabelian.LCFT.residueFrobenius_not_mem_powRange, Anabelian.LCFT.residueModPowerQuotient_card_eq_prime")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "13"
    text := some { path := "source/hoshi.txt", startLine := 491, endLine := 509 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-11.png" }
  }]
}
%%%

The arithmetic Frobenius of the algebraic closure of the finite residue field
restricts on every finite Galois residue extension to the usual power-map
Frobenius.  Its integral powers are dense in the residue absolute Galois group:
$$`\overline{\langle\operatorname{Frob}_k\rangle}=G_k.`
This makes precise the procyclic unramified factor that appears throughout
Hoshi's local calculations.  In particular, its quotient by $`n`th powers
has at most $`n` elements: density descends to the quotient, while the image
of Frobenius has exponent dividing $`n` and hence generates a finite closed
subgroup.  For prime $`n=\ell` the cardinality is exactly $`\ell`.  Indeed,
the standard degree-$`\ell` finite-field extension embeds into the chosen
residue algebraic closure; restriction to it proves that Frobenius is not an
$`\ell`th power.
:::

:::proof "residue_frobenius_procyclic"
Use the fixing subgroups of finite Galois intermediate fields as the Krull
neighborhood basis.  Given $`\sigma` and a neighborhood of it, translate the
neighborhood to one of the identity and choose a finite Galois intermediate
field whose fixing subgroup it contains.  The Galois group of that finite-field
extension is cyclic, generated by Frobenius, so some nonnegative power of
$`\operatorname{Frob}_k` has the same restriction as $`\sigma`.  Their quotient
lies in the fixing subgroup, placing that power in the original neighborhood.
:::

:::theorem "unramified_torsion_free_rank" (parent := "integral_mono_anabelian") (uses := "residue_frobenius_procyclic") (lean := "Anabelian.LCFT.ResidueTorsionFreeQuotient, Anabelian.LCFT.ResidueTorsionFreeModPowerQuotient, Anabelian.LCFT.residueFrobenius_not_pow_mod_torsion, Anabelian.LCFT.residueModPowerToTorsionFreeModPower, Anabelian.LCFT.residueTorsionFreeModPowerQuotient_card_eq_prime")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "19--20"
    text := some { path := "source/hoshi.txt", startLine := 854, endLine := 893 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-17.png" }
  }]
}
%%%

The unramified procyclic direction is not lost on passing to the torsion-free
quotient.  For every prime $`\ell`,
$$`\#\left((G_k^{\mathrm{res}}/\operatorname{tor})/
  \ell(G_k^{\mathrm{res}}/\operatorname{tor})\right)=\ell.`
Thus it contributes exactly one to Hoshi's mod-$`\ell` logarithmic rank.
:::

:::proof "unramified_torsion_free_rank" (uses := "residue_frobenius_procyclic")
The upper bound descends from the size-$`\ell` quotient before removing
torsion.  For the lower bound, suppose Frobenius were an $`\ell`th power
modulo a torsion element $`t` of order dividing $`m`.  Restrict to the explicit
degree-$`\ell m` residue extension.  Raising the alleged factorization to the
$`m`th power makes both the torsion factor and the $`\ell m`th power vanish,
forcing the degree-$`\ell m` Frobenius generator to have order dividing $`m`,
a contradiction.  The surviving Frobenius class has order $`\ell` and
generates the quotient.
:::

:::theorem "principal_unit_prime_to_p_divisibility" (parent := "integral_mono_anabelian") (lean := "Anabelian.LCFT.principalUnit_pow_surjective_of_ne_residueChar, Anabelian.LCFT.residueUnit_has_torsion_lift, Anabelian.LCFT.integerUnit_eq_torsion_mul_pow, Anabelian.LCFT.IntegerUnitTorsionFreeQuotient, Anabelian.LCFT.integerUnitTorsionFree_pow_surjective_of_ne_residueChar")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "11--12"
    text := some { path := "source/hoshi.txt", startLine := 380, endLine := 417 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-09.png" }
  }]
}
%%%

For every prime $`\ell\ne p_K`, the $`\ell`th-power endomorphism of the
principal-unit group $`U_K^1` is surjective.  This supplies the
prime-to-$`p_K` divisibility input in the decomposition of $`K^\times` from
Hoshi's Lemma 1.2.  Hensel lifting also supplies a torsion lift of every
nonzero residue class.  Consequently every local unit is a torsion unit times
an $`\ell`th power, and the torsion-free unit quotient is
$`\ell`-divisible: no prime-to-$`p_K` rank arises from local units.
:::

:::proof "principal_unit_prime_to_p_divisibility"
For $`u\in U_K^1`, apply Hensel's lemma in $`\mathcal O_K` to
$`X^\ell-u` at $`X=1`.  Its value at $`1` lies in the maximal ideal, while
its derivative there is $`\ell`, which is a unit because
$`\ell\ne p_K`.  The lifted root remains congruent to $`1` modulo the
maximal ideal, so it is itself a principal unit and its $`\ell`th power is
$`u`.  Applying the same argument to $`X^{q_K-1}-1` lifts each residue-field
unit to a root of unity.  Divide an arbitrary local unit by that torsion lift;
the quotient is principal and hence an $`\ell`th power by the first step.
:::

:::theorem "deep_principal_unit_torsion_freeness" (parent := "integral_mono_anabelian") (uses := "principal_unit_prime_to_p_divisibility") (lean := "Anabelian.LCFT.valuation_natCast_le_one, Anabelian.LCFT.residueChar_cast_valuation_lt_one, Anabelian.LCFT.residueCharValuation_le_primeCastValuation, Anabelian.LCFT.deepPrincipalUnitGroup, Anabelian.LCFT.deepPrincipalUnit_prime_pow_eq_one, Anabelian.LCFT.deepPrincipalUnit_eq_one_of_isOfFinOrder, Anabelian.LCFT.deepPrincipalUnitGroup_isMulTorsionFree")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "11--12"
    text := some { path := "source/hoshi.txt", startLine := 380, endLine := 417 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-09.png" }
  }]
}
%%%

The sufficiently deep principal units
$$`U_K^{>p}=\{x\in K^\times\mid v(x-1)<v(p_K)\}`
form a torsion-free subgroup.  This isolates a neighborhood of $`1` on which
passing from $`K^\times` to its quotient by torsion loses no information.  It
is the torsion-control input for the residue-characteristic direction of
Hoshi's mod-power rank calculation.
:::

:::proof "deep_principal_unit_torsion_freeness"
Suppose $`x\in U_K^{>p}` has prime order $`\ell`.  In the valuation ring, the
geometric sum $`S=1+x+\cdots+x^{\ell-1}` vanishes, since
$`S(x-1)=x^\ell-1=0` and $`x\ne1`.  Reducing modulo the principal ideal
$`(x-1)` shows that $`\ell\in(x-1)`, hence
$`v(\ell)\le v(x-1)`.  But the residue characteristic has the least valuation
among prime casts, so
$`v(p_K)\le v(\ell)\le v(x-1)`, contradicting the defining strict inequality.
For an arbitrary nontrivial finite-order element, raise it to the quotient of
its order by the least prime divisor; the result has prime order and yields the
same contradiction.
:::

:::theorem "deep_residue_characteristic_power_roots" (parent := "integral_mono_anabelian") (uses := "deep_principal_unit_torsion_freeness") (lean := "Anabelian.LCFT.deepRootCorrection, Anabelian.LCFT.deepRootCorrection_identity, Anabelian.LCFT.deepRootCorrection_sub_norm_le, Anabelian.LCFT.deepRootMap_contracting, Anabelian.LCFT.exists_deepRootSolution, Anabelian.LCFT.one_add_residueChar_cube_is_pow")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "11--12"
    text := some { path := "source/hoshi.txt", startLine := 380, endLine := 417 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-09.png" }
  }]
}
%%%

Writing $`p=p_K`, every element of $`1+p^3\mathcal O_K` is a $`p`th power
in $`\mathcal O_K`.  This explicit uniform depth supplies a finite-index
subgroup of local units contained in the image of the $`p`th-power map.
:::

:::proof "deep_residue_characteristic_power_roots" (uses := "deep_principal_unit_torsion_freeness")
Expand
$$`(1+p^2y)^p=1+p^3(y+H(y))`,
where every monomial of $`H` contains an additional factor of $`p`.  On the
complete valuation ring, powers are nonexpanding and the ultrametric triangle
inequality gives
$$`\lVert H(x)-H(y)\rVert\le \lVert p\rVert\,\lVert x-y\rVert`.
Since $`\lVert p\rVert<1`, the map $`y\mapsto a-H(y)` is a contraction.  Its
fixed point solves $`y+H(y)=a`, and substitution into the expansion gives
$`1+p^3a=(1+p^2y)^p`.
:::

:::theorem "residue_characteristic_unit_direction" (parent := "integral_mono_anabelian") (uses := "deep_principal_unit_torsion_freeness, deep_residue_characteristic_power_roots") (lean := "Anabelian.LCFT.deepIntegerUnitGroup, Anabelian.LCFT.deepIntegerUnitGroup_quotient_finite, Anabelian.LCFT.fieldTorsion_finite, Anabelian.LCFT.principalUnit_pow_residueChar_pow_sub_one_mem, Anabelian.LCFT.isOfFinOrder_of_all_residueChar_power_factorizations, Anabelian.LCFT.fieldTorsionFree_pow_not_surjective_residueChar, Anabelian.LCFT.fieldTorsionFreeModPowerQuotient_residueChar_nontrivial, Anabelian.LCFT.cubeDeepPrincipalUnitGroup, Anabelian.LCFT.cubeDeepIntegerUnitGroup_quotient_finite, Anabelian.LCFT.cubeDeepIntegerUnitGroup_le_powRange, Anabelian.LCFT.integerUnitsModPower_finite, Anabelian.LCFT.fieldModPowerParam_surjective, Anabelian.LCFT.fieldModPowerQuotient_finite, Anabelian.LCFT.fieldTorsionFreeModPowerQuotient_residueChar_finite, Anabelian.LCFT.exists_integerUnit_not_isOfFinOrder, Anabelian.LCFT.integerUnitTorsionFree_pow_not_surjective_residueChar, Anabelian.LCFT.integerUnitTorsionFreeModPowerQuotient_residueChar_nontrivial")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "11--12"
    text := some { path := "source/hoshi.txt", startLine := 380, endLine := 417 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-09.png" }
  }]
}
%%%

The torsion-free quotient of $`K^\times` is not $`p_K`-divisible.  Thus, in
contrast to every prime $`\ell\ne p_K`, the local-unit factor contributes a
nonzero class modulo $`p_K`th powers.  This will be the second direction,
independent of the uniformizer, in the candidate-prime calculation.
:::

:::proof "residue_characteristic_unit_direction" (uses := "deep_principal_unit_torsion_freeness, deep_residue_characteristic_power_roots")
The torsion-free deep principal-unit subgroup is open in the compact unit group.  Since its
intersection with torsion is trivial, all torsion in $`K^\times` injects into
a finite quotient and is therefore finite.  If a principal unit is a
$`p_K^n`th power, repeated use of the geometric-sum identity places its
difference from $`1` in the $`(n+1)`st power of the maximal ideal.  Hence a
class divisible by every $`p_K^n` modulo torsion becomes torsion after raising
to the order of the finite torsion subgroup: Krull intersection forces that
power to equal $`1`.  The explicit deep unit $`1+p_K^2` is nontorsion.
Surjectivity of the $`p_K`th-power map on units modulo torsion would make its
class infinitely divisible, giving the required contradiction.

For finiteness, use the still deeper open subgroup cut out by
$`v(u-1)<v(p_K^3)`.  Division by $`p_K^3` followed by the contraction result
shows that this subgroup lies in $`(\mathcal O_K^\times)^{p_K}`.  Its quotient
in the compact unit group is finite.  Finally, a field element is a
uniformizer power times a unit; reducing the exponent modulo $`p_K` gives a
surjection from
$$`\operatorname{Fin}(p_K)\times
  \mathcal O_K^\times/(\mathcal O_K^\times)^{p_K}`
onto $`K^\times/(K^\times)^{p_K}`, and hence onto the torsion-free quotient.
:::

:::theorem "local_multiplicative_prime_to_p_rank" (parent := "integral_mono_anabelian") (uses := "principal_unit_prime_to_p_divisibility") (lean := "Anabelian.LCFT.fieldUnitDiscreteValuation, Anabelian.LCFT.fieldUnitDiscreteValuation_uniformizer, Anabelian.LCFT.fieldUnitDiscreteValuation_eq_one_of_isOfFinOrder, Anabelian.LCFT.uniformizer_not_pow_mod_torsion, Anabelian.LCFT.fieldUnit_eq_uniformizer_zpow_mul_torsion_mul_pow, Anabelian.LCFT.FieldTorsionFreeQuotient, Anabelian.LCFT.FieldTorsionFreeModPowerQuotient, Anabelian.LCFT.fieldUniformizerModPower, Anabelian.LCFT.fieldTorsionFreeModPowerQuotient_card_eq_prime")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "11--12"
    text := some { path := "source/hoshi.txt", startLine := 380, endLine := 417 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-09.png" }
  }]
}
%%%

For every prime $`\ell\ne p_K`, the torsion-free local multiplicative group
has precisely one mod-$`\ell` direction:
$$`\#\left((K^\times/\operatorname{tor})/
  \ell(K^\times/\operatorname{tor})\right)=\ell.`
It is generated by the class of any uniformizer.
:::

:::proof "local_multiplicative_prime_to_p_rank" (uses := "principal_unit_prime_to_p_divisibility")
The discrete valuation sends a uniformizer to $`-1\in\mathbf Z` and kills
torsion, so the uniformizer is not an $`\ell`th power modulo torsion.  On the
other hand, decompose every element as a uniformizer power times a local unit.
The preceding principal-unit and Teichmüller-lift calculation expresses that
local unit as torsion times an $`\ell`th power.  Hence the mod-power quotient
is cyclic, generated by the uniformizer, and its nontrivial generator has
order exactly the prime $`\ell`.
:::

:::theorem "local_multiplicative_residue_characteristic_rank" (parent := "integral_mono_anabelian") (uses := "residue_characteristic_unit_direction") (lean := "Anabelian.LCFT.IntegerUnitTorsionFreeModPowerQuotient, Anabelian.LCFT.integerUnitTorsionFreeToFieldTorsionFree, Anabelian.LCFT.integerUnitTorsionFreeToFieldTorsionFree_injective, Anabelian.LCFT.integerUnitModPowerToFieldModPowerTorsionFree, Anabelian.LCFT.integerUnitModPowerToFieldModPowerTorsionFree_injective, Anabelian.LCFT.fieldDiscreteValuationModRaw, Anabelian.LCFT.fieldModPowerDiscreteValuationMod, Anabelian.LCFT.fieldModPowerDiscreteValuationMod_surjective, Anabelian.LCFT.fieldModPowerDiscreteValuationMod_integerUnit, Anabelian.LCFT.integerUnitTorsionFreeModPowerQuotient_card_ge_residueChar, Anabelian.LCFT.fieldTorsionFreeModPowerQuotient_card_ge_residueChar_sq")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "11--12"
    text := some { path := "source/hoshi.txt", startLine := 380, endLine := 417 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-09.png" }
  }]
}
%%%

At the residue characteristic, the torsion-free multiplicative quotient is
finite and has at least two independent mod-power directions:
$$`p_K^2\le
  \#\left((K^\times/\operatorname{tor})/
  p_K(K^\times/\operatorname{tor})\right)`.
:::

:::proof "local_multiplicative_residue_characteristic_rank" (uses := "residue_characteristic_unit_direction")
Inclusion of valuation-ring units induces an injection on torsion-free
mod-$`p_K` quotients.  If a unit becomes a $`p_K`th power in the field quotient,
applying the discrete valuation shows that the putative root has valuation
zero, so it was already a unit.  The nonzero unit direction therefore survives.

Discrete valuation modulo $`p_K` gives a surjection from the field quotient to
the multiplicative copy of $`\mathbf Z/p_K\mathbf Z`; units lie in its kernel,
while a uniformizer maps to a generator.  The kernel has at least $`p_K`
elements and the image has exactly $`p_K` elements.  The kernel--image card
formula gives the stated lower bound $`p_K^2`.
:::

:::theorem "abelianization_prime_to_p_rank" (parent := "integral_mono_anabelian") (uses := "local_reciprocity_input, residue_frobenius_procyclic, unramified_torsion_free_rank, local_multiplicative_prime_to_p_rank") (lean := "Anabelian.LCFT.AbelianizedTorsionFreeQuotient, Anabelian.LCFT.AbelianizedTorsionFreeModPowerQuotient, Anabelian.LCFT.reciprocityTorsionFreeMap, Anabelian.LCFT.reciprocityModPowerMap, Anabelian.LCFT.unramifiedProjection_surjective, Anabelian.LCFT.reciprocityModPowerMap_surjective, Anabelian.LCFT.abelianizedTorsionFreeToResidue, Anabelian.LCFT.abelianizedModPowerToResidue, Anabelian.LCFT.residueFrobeniusModPower, Anabelian.LCFT.residueFrobeniusModPower_ne_one, Anabelian.LCFT.abelianizedUniformizerModPower, Anabelian.LCFT.abelianizedUniformizerModPower_ne_one, Anabelian.LCFT.abelianizedTorsionFreeModPowerQuotient_card_eq_prime")
%%%
source := {
  document := "hoshi"
  spans := #[
    {
      page := "15--16"
      text := some { path := "source/hoshi.txt", startLine := 619, endLine := 652 }
      pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-13.png" }
    },
    {
      page := "19--20"
      text := some { path := "source/hoshi.txt", startLine := 853, endLine := 881 }
      pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-17.png" }
    }
  ]
}
%%%

Let $`\operatorname{rec}_K:K^\times\to G_K^{\mathrm{ab}}` be the local
reciprocity map.  For every prime $`\ell\ne p_K`, it induces a surjection on
torsion-free mod-$`\ell` quotients, and
$$`\#\left((G_K^{\mathrm{ab}}/\operatorname{tor})/
  \ell(G_K^{\mathrm{ab}}/\operatorname{tor})\right)=\ell.`
Thus no prime different from $`p_K` satisfies Hoshi's rank-at-least-two
predicate.
:::

:::proof "abelianization_prime_to_p_rank" (uses := "local_reciprocity_input, residue_frobenius_procyclic, unramified_torsion_free_rank, local_multiplicative_prime_to_p_rank")
Local reciprocity maps torsion to torsion and therefore descends through the
two quotients.  To prove surjectivity, first match the unramified image of an
arbitrary abelianized class modulo $`\ell` with an integral power of
Frobenius.  The remaining unramified discrepancy is an $`\ell`th power;
lift its root through the unramified projection.  After dividing by that
power, the discrepancy lies in inertia, where the units--inertia part of
local reciprocity supplies a preimage.

The image of the uniformizer class remains nontrivial: projection to the
torsion-free residue-Galois quotient gives the Frobenius class, which is not
an $`\ell`th power modulo torsion.  The source quotient is cyclic of order
$`\ell` by the local multiplicative calculation, so surjectivity and this
nontrivial image make the target cyclic of the same prime order.
:::

:::theorem "group_theoretic_local_invariants" (parent := "integral_mono_anabelian") (uses := "abelianization_prime_to_p_rank")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "19--21"
    text := some { path := "source/hoshi.txt", startLine := 854, endLine := 949 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-18.png" }
  }]
}
%%%

The abstract profinite group $`G` determines the residue characteristic
$`p(G)`, absolute degree $`d(G)`, residue degree $`f(G)`, ramification index
$`e(G)`, inertia and wild inertia $`P(G)\subseteq I(G)`, and arithmetic
Frobenius $`\operatorname{Frob}(G)\in G/I(G)`.  For $`G=G_K` these agree
with the classical local-field invariants.
:::

:::proof "group_theoretic_local_invariants" (uses := "local_reciprocity_input")
The torsion-free quotient of $`G^{\mathrm{ab}}` detects $`p(G)` as the unique
prime whose mod-$`p` rank is at least two.  Its rank and prime-to-$`p` torsion
recover $`d(G)` and $`f(G)`, hence $`e(G)=d(G)/f(G)`.  Intersections of normal
open subgroups having prescribed ramification index recover inertia and wild
inertia.  Frobenius is then the unique class acting on $`I(G)/P(G)` by the
$`p(G)^{f(G)}`-power map.  Hoshi's Proposition 3.6 and Lemma 3.7 identify
these intrinsic definitions with the classical ones.
:::

:::theorem "topological_abelianized_transport" (parent := "integral_mono_anabelian") (uses := "group_theoretic_local_invariants") (lean := "Anabelian.OTriangle.TopologicalAbelianization.map, Anabelian.OTriangle.TopologicalAbelianization.congr, Anabelian.OTriangle.TopologicalAbelianization.congr_trans, Anabelian.OTriangle.LocalGaloisGroup.fixedFieldGaloisContinuousEquiv, Anabelian.OTriangle.LocalGaloisGroup.abelianizationEquiv, Anabelian.OTriangle.LocalGaloisGroup.fixedFieldAbelianizationEquiv, Anabelian.OTriangle.LocalGaloisGroup.abelianizationEquiv_comp")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "23--25"
    text := some { path := "source/hoshi.txt", startLine := 1088, endLine := 1188 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-21.png" }
  }]
}
%%%

A continuous group isomorphism transports topological abelianizations and the
reverse-inclusion poset of open subgroups.  At each open subgroup, the induced
map agrees with an equivalence between the abelianized absolute Galois groups
of the corresponding fixed fields.  These equivalences respect identity and
composition before restriction to the Frobenius-positive integral cones.
:::

:::proof "topological_abelianized_transport" (uses := "group_theoretic_local_invariants")
A continuous homomorphism maps the commutator subgroup into the commutator
subgroup and, by continuity, maps its topological closure into the target
closure.  It therefore descends to topological abelianizations; applying the
construction to an isomorphism and its inverse yields a multiplicative
equivalence, functorial under composition.

For an open subgroup $`U\leq G_K`, infinite Galois theory identifies $`U`
with the absolute Galois group of its fixed field.  Restriction of
automorphisms is continuous for the Krull topologies.  Its inverse is
continuous because the source is compact and the target Hausdorff.  Composing
this identification with restricted subgroup transport gives the fixed-field
abelianization equivalence used at every node of the reconstruction diagram.
:::

:::theorem "residue_characteristic_predicate" (parent := "integral_mono_anabelian") (uses := "topological_abelianized_transport") (lean := "Anabelian.OTriangle.GroupTheoreticInvariants.torsionFreeQuotient, Anabelian.OTriangle.GroupTheoreticInvariants.torsionFreeQuotientEquiv, Anabelian.OTriangle.GroupTheoreticInvariants.modPowerQuotient, Anabelian.OTriangle.GroupTheoreticInvariants.modPowerQuotientEquiv, Anabelian.OTriangle.GroupTheoreticInvariants.modPowerRank, Anabelian.OTriangle.GroupTheoreticInvariants.isResidueCharacteristicCandidate_congr, Anabelian.OTriangle.GroupTheoreticInvariants.torsionEquiv, Anabelian.OTriangle.GroupTheoreticInvariants.primeToTorsionQuotient, Anabelian.OTriangle.GroupTheoreticInvariants.primeToTorsionQuotientEquiv, Anabelian.OTriangle.GroupTheoreticInvariants.absoluteDegree, Anabelian.OTriangle.GroupTheoreticInvariants.residueDegree, Anabelian.OTriangle.GroupTheoreticInvariants.ramificationIndex, Anabelian.OTriangle.GroupTheoreticInvariants.ramificationIndex_congr, Anabelian.OTriangle.LocalGaloisGroup.torsionFreeAbelianization, Anabelian.OTriangle.LocalGaloisGroup.abelianizationModPowerRank, Anabelian.OTriangle.LocalGaloisGroup.IsResidueCharacteristicCandidate, Anabelian.OTriangle.LocalGaloisGroup.isResidueCharacteristicCandidate_iff, Anabelian.OTriangle.LocalGaloisGroup.groupTheoreticAbsoluteDegree, Anabelian.OTriangle.LocalGaloisGroup.groupTheoreticResidueDegree, Anabelian.OTriangle.LocalGaloisGroup.groupTheoreticRamificationIndex, Anabelian.OTriangle.LocalGaloisGroup.groupTheoreticRamificationIndex_eq")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "19--20"
    text := some { path := "source/hoshi.txt", startLine := 872, endLine := 921 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-17.png" }
  }]
}
%%%

For a prime $`p`, form the torsion-free quotient of $`G^{\mathrm{ab}}`
and then quotient by its subgroup of $`p`th powers.  The predicate that
this finite quotient have base-$`p` logarithmic cardinality at least two is
preserved by every isomorphism of local absolute Galois groups.  Hoshi's
Lemma 3.4 identifies the unique prime satisfying this predicate with the
residue characteristic.  At a candidate prime, the same abelianization also
defines $`d(G)` from the mod-power rank, $`f(G)` from prime-to-$`p` torsion,
and $`e(G)=d(G)/f(G)`; all three expressions are invariant under group
isomorphism.
:::

:::proof "residue_characteristic_predicate" (uses := "topological_abelianized_transport")
An equivalence of commutative groups maps torsion onto torsion and therefore
descends to the torsion-free quotients.  It also maps the range of the
$`p`th-power homomorphism onto the corresponding range in the target.  The
resulting quotient equivalence preserves cardinality, hence the logarithmic
rank and the candidate predicate.  Equivalences likewise preserve the
$`p`-primary component of torsion, so they preserve the prime-to-$`p`
quotient and the formulas for absolute degree, residue degree, and
ramification index.  The remaining local-field calculation of
existence and uniqueness is precisely the arithmetic content of Hoshi's
Lemma 3.4 and Proposition 3.6.
:::

:::theorem "intrinsic_ramification_intersections" (parent := "integral_mono_anabelian") (uses := "residue_characteristic_predicate") (lean := "Anabelian.OTriangle.IntrinsicRamification.ramificationIndex, Anabelian.OTriangle.IntrinsicRamification.ramificationIndex_congr, Anabelian.OTriangle.IntrinsicRamification.IsInertiaNeighborhood, Anabelian.OTriangle.IntrinsicRamification.IsWildInertiaNeighborhood, Anabelian.OTriangle.IntrinsicRamification.inertiaSubgroup, Anabelian.OTriangle.IntrinsicRamification.wildInertiaSubgroup, Anabelian.OTriangle.IntrinsicRamification.inertiaSubgroup_normal, Anabelian.OTriangle.IntrinsicRamification.wildInertiaSubgroup_normal, Anabelian.OTriangle.IntrinsicRamification.wildInertiaSubgroup_le_inertiaSubgroup, Anabelian.OTriangle.IntrinsicRamification.isInertiaNeighborhood_map_iff, Anabelian.OTriangle.IntrinsicRamification.isWildInertiaNeighborhood_map_iff, Anabelian.OTriangle.IntrinsicRamification.map_inertiaSubgroup, Anabelian.OTriangle.IntrinsicRamification.map_wildInertiaSubgroup, Anabelian.OTriangle.LocalGaloisGroup.map_intrinsicInertiaSubgroup, Anabelian.OTriangle.LocalGaloisGroup.map_intrinsicWildInertiaSubgroup")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "20--21"
    text := some { path := "source/hoshi.txt", startLine := 900, endLine := 949 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-18.png" }
  }]
}
%%%

At a prime candidate $`p`, define $`I(G,p)` as the intersection of the
normal open subgroups $`N` with $`e(N,p)=e(G,p)`.  Define $`P(G,p)` as the
intersection of the normal open subgroups for which
$`e(N,p)=e(G,p)q` for a positive integer $`q` prime to $`p`.  Both
intersections are normal, and $`P(G,p)\subseteq I(G,p)`.

Every continuous group equivalence $`G\simeq H` carries these subgroups
exactly onto $`I(H,p)` and $`P(H,p)`.  This is the fully intrinsic,
presentation-independent part of Definition 3.5(iii).  The later arithmetic
identification with classical inertia and wild inertia is kept separate.
:::

:::proof "intrinsic_ramification_intersections" (uses := "residue_characteristic_predicate")
Transport an open subgroup along a continuous equivalence and restrict the
equivalence to that subgroup.  Functoriality of topological abelianization
and invariance of $`e(-,p)` show that the equal-index and prime-to-$`p`
conditions are each preserved and reflected.  Transport therefore gives a
bijection between the respective families being intersected, so membership
in either intersection is preserved in both directions.  Normality follows
because intersections of normal subgroups are normal.  Finally every
equal-index neighborhood is a prime-to-$`p` neighborhood with relative
factor one, proving $`P(G,p)\subseteq I(G,p)`.
:::

:::theorem "intrinsic_frobenius_characterization" (parent := "integral_mono_anabelian") (uses := "intrinsic_ramification_intersections") (lean := "Anabelian.OTriangle.IntrinsicRamification.inertiaQuotient, Anabelian.OTriangle.IntrinsicRamification.IsFrobeniusRepresentative, Anabelian.OTriangle.IntrinsicRamification.IsFrobeniusClass, Anabelian.OTriangle.IntrinsicRamification.HasUniqueFrobeniusClass, Anabelian.OTriangle.IntrinsicRamification.frobeniusClass, Anabelian.OTriangle.IntrinsicRamification.frobeniusClass_spec, Anabelian.OTriangle.IntrinsicRamification.isFrobeniusRepresentative_map_iff, Anabelian.OTriangle.IntrinsicRamification.inertiaQuotientEquiv, Anabelian.OTriangle.IntrinsicRamification.inertiaQuotientEquiv_mk, Anabelian.OTriangle.IntrinsicRamification.isFrobeniusClass_map_iff, Anabelian.OTriangle.IntrinsicRamification.hasUniqueFrobeniusClass_congr, Anabelian.OTriangle.IntrinsicRamification.frobeniusClass_map, Anabelian.OTriangle.LocalGaloisGroup.HasUniqueIntrinsicFrobeniusClass, Anabelian.OTriangle.LocalGaloisGroup.hasUniqueIntrinsicFrobeniusClass_iff")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "21"
    text := some { path := "source/hoshi.txt", startLine := 937, endLine := 976 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-19.png" }
  }]
}
%%%

A representative $`g\in G` satisfies the intrinsic Frobenius condition when
conjugation by $`g` on $`I(G,p)/P(G,p)` is the $`p^f`-power map.  This
condition is expressed directly in the ambient group, and therefore defines
a predicate on classes of $`G/I(G,p)`.  Every continuous group equivalence
preserves and reflects the representative predicate, the class predicate,
and the assertion that there is a unique such class.  Conditional on that
existence-and-uniqueness assertion, the selected Frobenius class is transported
by the canonical quotient equivalence.

This theorem isolates the formal functoriality from the arithmetic content of
Hoshi's Lemma 3.7: proving that a local absolute Galois group actually has the
unique characterized class remains an explicit later obligation.
:::

:::proof "intrinsic_frobenius_characterization" (uses := "intrinsic_ramification_intersections")
The congruence
$$`gxg^{-1}\equiv x^{p^f}\pmod {P(G,p)}`
is preserved by a group equivalence because multiplication, inversion, powers,
inertia membership, and wild-inertia membership are all preserved.  The
equivalence also descends to $`G/I(G,p)`, and maps the class of $`g` to the
class of its image.  Hence it bijects the classes satisfying the Frobenius
predicate.  Existence and uniqueness are invariant under this bijection, and
uniqueness identifies the chosen classes whenever the arithmetic hypothesis
is available on both sides.
:::

:::theorem "classical_inertia_frobenius_bridge" (parent := "integral_mono_anabelian") (uses := "local_reciprocity_input") (lean := "Anabelian.OTriangle.ClassicalRamification.inertiaSubgroup, Anabelian.OTriangle.ClassicalRamification.unramifiedProjection_mk, Anabelian.OTriangle.ClassicalRamification.map_inertiaSubgroup, Anabelian.OTriangle.ClassicalRamification.inertiaQuotient, Anabelian.OTriangle.ClassicalRamification.inertiaQuotientEquivResidue, Anabelian.OTriangle.ClassicalRamification.inertiaQuotientEquivResidue_mk, Anabelian.OTriangle.ClassicalRamification.frobeniusClass, Anabelian.OTriangle.ClassicalRamification.inertiaQuotientEquivResidue_frobeniusClass, Anabelian.OTriangle.ClassicalRamification.inertiaQuotientToAbelianized, Anabelian.OTriangle.ClassicalRamification.unramifiedQuotientEquiv_inertiaQuotientToAbelianized, Anabelian.OTriangle.ClassicalRamification.unramifiedQuotientEquiv_frobeniusClass")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "13--14"
    text := some { path := "source/hoshi.txt", startLine := 489, endLine := 541 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-11.png" }
  }]
}
%%%

For the presented local field $`K`, classical full inertia is the kernel of
the residue action $`G_K\to G_{\kappa_K}`.  Its image in the topological
abelianization is exactly the abelianized inertia subgroup used in local
reciprocity.  The quotient $`G_K/I_K` is canonically the absolute Galois
group of the residue field, and its distinguished class is the inverse image
of arithmetic Frobenius.  Passing this class to the abelianized unramified
quotient still gives arithmetic Frobenius.
:::

:::proof "classical_inertia_frobenius_bridge" (uses := "local_reciprocity_input")
The residue action is surjective, so the first isomorphism theorem identifies
its quotient by the kernel with the residue-field Galois group.  The residue
action factors through the topological abelianization because the target is
abelian.  A class in the abelianization lies in the resulting kernel exactly
when any full-group representative has trivial residue action; this proves
that the image of full inertia is all of abelianized inertia.  Both quotient
identifications are induced by the same residue action, hence commute on
representatives and carry the chosen full Frobenius class to the same
arithmetic Frobenius element.
:::

:::theorem "hoshi_ramification_identification" (parent := "integral_mono_anabelian") (uses := "local_reciprocity_input, residue_characteristic_predicate, intrinsic_ramification_intersections, intrinsic_frobenius_characterization, classical_inertia_frobenius_bridge") (lean := "Anabelian.OTriangle.LocalGaloisGroup.HoshiRamificationComparison, Anabelian.OTriangle.LocalGaloisGroup.HoshiRamificationComparisonFamily")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "19--21"
    text := some { path := "source/hoshi.txt", startLine := 872, endLine := 986 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-19.png" }
  }]
}
%%%

For every presented local absolute Galois group, the unique intrinsic prime is
the residue characteristic, the intrinsic inertia and wild-inertia
intersections are the classical ramification subgroups, and the unique
intrinsic Frobenius class is arithmetic Frobenius.  In Lean the conjunction
needed downstream is named `HoshiRamificationComparison`; its uniform
existence is `HoshiRamificationComparisonFamily`.
:::

:::proof "hoshi_ramification_identification" (uses := "local_reciprocity_input, residue_characteristic_predicate, intrinsic_ramification_intersections, intrinsic_frobenius_characterization, classical_inertia_frobenius_bridge")
Local reciprocity identifies the abstract topological abelianization with the
dense reciprocity image of $`K^\times`.  The structure theorem for the
multiplicative group of a mixed-characteristic local field gives
$$`G_K^{\mathrm{ab}}\cong
\mathbb Z/(q-1)\oplus \mathbb Z/p^a\oplus
\mathbb Z_p^{[K:\mathbb Q_p]}\oplus\widehat{\mathbb Z}.`
Its torsion-free mod-$`\ell` rank is at least two exactly for $`\ell=p`, and
its rank and prime-to-$`p` torsion give the absolute and residue degrees.

For a normal open subgroup $`N=G_L`, multiplicativity of ramification degree
in $`L/K` shows that equality of the reconstructed ramification indices is
equivalent to $`L/K` being unramified.  Intersecting all such $`N` recovers
inertia.  Requiring a positive prime-to-$`p` relative factor similarly
recovers wild inertia.  The tame relation
$`\varphi\tau\varphi^{-1}=\tau^q` then gives existence and uniqueness of the
class acting by the $`p^f`-power map and identifies it with arithmetic
Frobenius.  These are exactly Lemma 3.4, Proposition 3.6, Lemma 3.7, and
Proposition 3.9; formalizing the displayed local-unit structure and tame
relation is the outstanding arithmetic implementation behind the named Lean
proposition.
:::

:::theorem "ramification_comparison_transport" (parent := "integral_mono_anabelian") (uses := "hoshi_ramification_identification") (lean := "Anabelian.OTriangle.LocalGaloisGroup.residueChar_eq_of_hoshiComparison, Anabelian.OTriangle.LocalGaloisGroup.map_classicalInertiaSubgroup_of_hoshiComparison, Anabelian.OTriangle.LocalGaloisGroup.classicalFrobeniusClass_map_of_hoshiComparison, Anabelian.OTriangle.LocalGaloisGroup.map_abelianizedInertiaSubgroup_of_hoshiComparison, Anabelian.OTriangle.LocalGaloisGroup.abelianizedFrobeniusClass_map_of_hoshiComparison, Anabelian.OTriangle.LocalGaloisGroup.mem_intrinsicBaseIntegerMonoid_iff, Anabelian.OTriangle.LocalGaloisGroup.map_intrinsicBaseIntegerMonoid_of_hoshiComparison, Anabelian.OTriangle.LocalGaloisGroup.intrinsicBaseIntegerMonoidEquivOfHoshiComparison, Anabelian.OTriangle.LocalGaloisGroup.fixedFieldGroupHom, Anabelian.OTriangle.LocalGaloisGroup.fixedFieldReconstructedNodeEquiv")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "20--21"
    text := some { path := "source/hoshi.txt", startLine := 916, endLine := 986 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-19.png" }
  }]
}
%%%

From the uniform arithmetic comparison, every
profinite-group isomorphism formally preserves the residue characteristic,
full and abelianized inertia, and arithmetic Frobenius.

Consequently it maps the Frobenius-positive submonoid of one topological
abelianization exactly onto the other.  The construction applies to the
restricted isomorphism at each pair of corresponding fixed fields, giving a
nodewise multiplicative equivalence of the reconstruction diagrams.  The
uniform comparison is passed explicitly to the formal transport theorem, so
the arithmetic dependency remains visible in every downstream declaration.
:::

:::proof "ramification_comparison_transport" (uses := "hoshi_ramification_identification")
The unique-prime predicates on source and target correspond, so their
classical residue characteristics agree.  Intrinsic inertia transport then
becomes classical inertia transport.  Quotienting gives a commutative square
between intrinsic and classical unramified quotients; uniqueness of the
Frobenius characterization forces the classical Frobenius classes to
correspond.  A second commutative square passes this statement through
topological abelianization.

Finally, an abelianized element belongs to the reconstructed one-field monoid
exactly when its unramified quotient class is a nonnegative power of the
abelianized Frobenius class.  This characterization is preserved in both
directions, so restriction of the abelianization equivalence gives the node
equivalence.  Replacing the ambient groups by corresponding open subgroups
and identifying them with fixed-field absolute Galois groups gives the stated
fixed-field node transport.
:::
