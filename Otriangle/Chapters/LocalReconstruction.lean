import Verso
import VersoManual
import VersoBlueprint
import Otriangle.LCFT
import Otriangle.MonoAnabelian.ResidueProcyclic
import Otriangle.MonoAnabelian.ResidueTorsionFree
import Otriangle.MonoAnabelian.UnramifiedTorsionFree
import Otriangle.MonoAnabelian.DeepUnits
import Otriangle.MonoAnabelian.DeepPowerRoots
import Otriangle.MonoAnabelian.LocalArithmeticInvariants
import Otriangle.MonoAnabelian.PrincipalCongruence
import Otriangle.MonoAnabelian.FiniteIndexTorsionFree
import Otriangle.MonoAnabelian.ExactUnitRank
import Otriangle.MonoAnabelian.ExactFieldRank
import Otriangle.MonoAnabelian.ExactReciprocityRank
import Otriangle.MonoAnabelian.PrimeToTorsionUnits
import Otriangle.MonoAnabelian.PrimeToTorsionReciprocity
import Otriangle.MonoAnabelian.ExactGroupInvariants
import Otriangle.MonoAnabelian.LocalExtensionRamification
import Otriangle.MonoAnabelian.FixedFieldRamification
import Otriangle.MonoAnabelian.FiniteGaloisRamification
import Otriangle.MonoAnabelian.UnramifiedFixedFields
import Otriangle.MonoAnabelian.SpectralPointing
import Otriangle.MonoAnabelian.SpectralInertiaComparison
import Otriangle.MonoAnabelian.FiniteInertiaRestriction
import Otriangle.MonoAnabelian.FiniteTameRamification
import Otriangle.MonoAnabelian.FiniteTameFixedField
import Otriangle.MonoAnabelian.FiniteTameRestriction
import Otriangle.MonoAnabelian.TameKummerRamification
import Otriangle.MonoAnabelian.TameFrobeniusUniqueness
import Otriangle.MonoAnabelian.InertiaComparison
import Otriangle.MonoAnabelian.ResidueCharacteristicRank
import Otriangle.MonoAnabelian.ResiduePowerQuotientFinite
import Otriangle.MonoAnabelian.ResidueUnitRank
import Otriangle.MonoAnabelian.ResidueCharacteristicFieldRank
import Otriangle.MonoAnabelian.ResidueCharacteristicReciprocityRank
import Otriangle.MonoAnabelian.ResidueCharacteristicCandidate
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

:::theorem "residue_absolute_galois_torsion_free" (parent := "integral_mono_anabelian") (uses := "residue_frobenius_procyclic") (lean := "Anabelian.LCFT.residueAbsoluteGaloisGroup_isOfFinOrder_eq_one")
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

The absolute Galois group of the finite residue field is torsion-free.  More
precisely, if $`\sigma^n=1`, then $`\sigma` acts trivially on every finite
residue extension and hence on the whole algebraic closure.
:::

:::proof "residue_absolute_galois_torsion_free" (uses := "residue_frobenius_procyclic")
Fix an element of the residue algebraic closure and let $`L` be a finite
Galois field of definition of degree $`d`.  Enlarge $`L` inside the algebraic
closure to a finite Galois field $`M` whose degree is divisible by $`dn`.
On $`M`, write $`\sigma=\operatorname{Frob}^a`.  The relation
$`\sigma^n=1` says that $`[M:k]\mid an`; since $`dn\mid[M:k]`, cancellation
gives $`d\mid a`.  Thus $`\operatorname{Frob}^a` restricts trivially to the
degree-$`d` field $`L`, fixing the chosen element.
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

:::theorem "principal_unit_prime_to_p_divisibility" (parent := "integral_mono_anabelian") (lean := "Anabelian.LCFT.principalUnit_pow_surjective_of_ne_residueChar, Anabelian.LCFT.residueUnit_has_card_sub_one_power_lift, Anabelian.LCFT.residueUnit_has_torsion_lift, Anabelian.LCFT.integerUnit_eq_torsion_mul_pow, Anabelian.LCFT.IntegerUnitTorsionFreeQuotient, Anabelian.LCFT.integerUnitTorsionFree_pow_surjective_of_ne_residueChar")
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

:::theorem "local_arithmetic_invariants" (parent := "integral_mono_anabelian") (lean := "Anabelian.LCFT.LocalIntegerRing, Anabelian.LCFT.residueCharIdeal, Anabelian.LCFT.absoluteRamificationIndex, Anabelian.LCFT.localResidueDegree, Anabelian.LCFT.residueCharIdeal_eq_maximalIdeal_pow, Anabelian.LCFT.absoluteRamificationIndex_pos, Anabelian.LCFT.residueField_card_eq_residueChar_pow_residueDegree, Anabelian.LCFT.residueCharIdeal_quotient_card")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "10--12"
    text := some { path := "source/hoshi.txt", startLine := 330, endLine := 417 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-09.png" }
  }]
}
%%%

For $`A=\mathcal O_K`, write $`p=p_K`, let $`\mathfrak m` be its maximal
ideal, and define the arithmetic integers $`e=e_K` and $`f=f_K` by
$$`pA=\mathfrak m^e,\qquad
f=\dim_{\mathbf F_p}(A/\mathfrak m).`
The DVR ideal filtration then gives the exact finite cardinality
$$`\#(A/pA)=p^{ef}.`
This supplies a ring-theoretic version of the integers in Hoshi's Lemma 1.2
that can be connected directly to the deep principal-unit filtration.
:::

:::proof "local_arithmetic_invariants"
Choose an irreducible uniformizer $`\pi\in A`.  Every nonzero ideal of the
discrete valuation ring $`A` is generated by a unique power of $`\pi`; define
$`e` by $`pA=(\pi^e)=\mathfrak m^e`.  The exponent is positive because
$`v(p)<1`, whereas a zeroth power would make $`p` a unit.  The finite residue
field has cardinality $`p^f` by its dimension over $`\mathbf F_p`.  Successive
quotients in the maximal-ideal filtration all have that cardinality, hence
$$`\#(A/pA)=\#(A/\mathfrak m^e)=(p^f)^e=p^{ef}.`
:::

:::theorem "exact_deep_principal_congruence_quotient" (parent := "integral_mono_anabelian") (uses := "deep_residue_characteristic_power_roots, local_arithmetic_invariants") (lean := "Anabelian.LCFT.residueCharPrincipalCongruenceGroup, Anabelian.LCFT.mem_residueCharPrincipalCongruenceGroup_iff, Anabelian.LCFT.squarePrincipalCoefficientMod, Anabelian.LCFT.squarePrincipalCoefficientMod_surjective, Anabelian.LCFT.squarePrincipalCoefficientMod_eq_one_iff, Anabelian.LCFT.squarePrincipal_pow_range, Anabelian.LCFT.squarePrincipalModPowerQuotient_card")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "11--12"
    text := some { path := "source/hoshi.txt", startLine := 350, endLine := 417 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-09.png" }
  }]
}
%%%

Let $`U[p^n]=\ker(A^\times\to(A/p^nA)^\times)`.  Normalized coefficient
reduction is a surjective homomorphism
$$`c_2:U[p^2]\longrightarrow (A/pA,+),\qquad
c_2(1+p^2a)=a\bmod p,`
with kernel $`U[p^3]`.  Moreover, the image of the $`p`th-power map on
$`U[p^2]` is exactly $`U[p^3]`.  Consequently
$$`\#\bigl(U[p^2]/U[p^2]^p\bigr)=\#(A/pA)=p^{ef}.`
This is the exact local-unit contribution to the rank $`d_K=ef` in Hoshi's
Lemma 1.2 and Definition 3.5.
:::

:::proof "exact_deep_principal_congruence_quotient" (uses := "deep_residue_characteristic_power_roots, local_arithmetic_invariants")
Writing $`u=1+p^2a` and $`v=1+p^2b`, multiplication gives normalized
coefficient $`a+b+p^2ab`, so reduction modulo $`p` makes $`c_2` a
homomorphism.  Every residue class is represented by $`1+p^2a`, proving
surjectivity, and $`c_2(u)=0` exactly when $`u\equiv1\pmod {p^3}`.

The binomial correction formula shows directly that a $`p`th power from
$`U[p^2]` lies in $`U[p^3]`.  Conversely the contraction argument constructs,
for every $`1+p^3a`, a root of the sharper form $`1+p^2y`; thus the image is
precisely $`U[p^3]`.  The first isomorphism theorem identifies the resulting
power quotient with the additive group of $`A/pA`, whose exact cardinality
was computed in the preceding node.
:::

:::theorem "finite_index_torsion_cancellation" (parent := "integral_mono_anabelian") (uses := "deep_principal_unit_torsion_freeness, exact_deep_principal_congruence_quotient") (lean := "Anabelian.LCFT.subgroupPowerRange, Anabelian.LCFT.torsionTimesSubgroupModPowerToPowerKernel, Anabelian.LCFT.torsionTimesSubgroupModPowerToPowerKernel_bijective, Anabelian.LCFT.ambientModPower_card_eq_powerTorsion_mul_subgroupModPower, Anabelian.LCFT.ambientPowerRange_inf_torsion_subgroupOf, Anabelian.LCFT.torsionFreeModPower_card_eq_subgroupModPower, Anabelian.LCFT.squarePrincipalCongruence_isMulTorsionFree, Anabelian.LCFT.subgroupPowerRange_squarePrincipal, Anabelian.LCFT.integerUnitTorsionFreeModPowerQuotient_card_eq_residueDegreeProduct")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "11, 19--20"
    text := some { path := "source/hoshi.txt", startLine := 350, endLine := 417 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-09.png" }
  }]
}
%%%

Let $`D\le U` be a finite-index torsion-free subgroup of a commutative group,
and suppose $`U/D^n` is finite.  Then
$$`\#\bigl((U/\operatorname{tor}U)/n(U/\operatorname{tor}U)\bigr)
=\#(D/D^n).`
Applied to $`U=\mathcal O_K^\times`, $`D=U[p^2]`, and $`n=p`, this yields
the exact local-unit cardinality $`p^{ef}`.
:::

:::proof "finite_index_torsion_cancellation" (uses := "deep_principal_unit_torsion_freeness, exact_deep_principal_congruence_quotient")
First quotient $`U` by $`D^n`.  The kernel of the induced $`n`th-power
endomorphism consists uniquely of a product of an element of $`U[n]` and a
class in $`D/D^n`: if $`x^n=d^n`, then $`xd^{-1}\in U[n]`; uniqueness uses
torsion-freeness of $`D`.  Since the ambient quotient is finite, the kernel
and cokernel of its power endomorphism have equal cardinality.  Thus
$$`\#(U/U^n)=\#U[n]\,\#(D/D^n).`

The intersection of $`U^n` with the torsion subgroup is exactly
$`(\operatorname{tor}U)^n`: an $`n`th root of a torsion element is torsion.
The finite torsion group's power endomorphism has cokernel and kernel of the
same size $`\#U[n]`.  Passing from $`U/U^n` to the quotient by all torsion
therefore cancels precisely that factor.  For local units, $`U[p^2]` is
torsion-free, its $`p`th powers are $`U[p^3]`, and the finite residue-ring
quotient proves the required finite-index hypotheses.
:::

:::theorem "residue_characteristic_unit_direction" (parent := "integral_mono_anabelian") (uses := "deep_principal_unit_torsion_freeness, deep_residue_characteristic_power_roots, exact_deep_principal_congruence_quotient") (lean := "Anabelian.LCFT.deepIntegerUnitGroup, Anabelian.LCFT.deepIntegerUnitGroup_quotient_finite, Anabelian.LCFT.fieldTorsion_finite, Anabelian.LCFT.principalUnit_pow_residueChar_pow_sub_one_mem, Anabelian.LCFT.isOfFinOrder_of_all_residueChar_power_factorizations, Anabelian.LCFT.fieldTorsionFree_pow_not_surjective_residueChar, Anabelian.LCFT.fieldTorsionFreeModPowerQuotient_residueChar_nontrivial, Anabelian.LCFT.cubeDeepPrincipalUnitGroup, Anabelian.LCFT.cubeDeepIntegerUnitGroup_quotient_finite, Anabelian.LCFT.cubeDeepIntegerUnitGroup_le_powRange, Anabelian.LCFT.integerUnitsModPower_finite, Anabelian.LCFT.fieldModPowerParam_surjective, Anabelian.LCFT.fieldModPowerQuotient_finite, Anabelian.LCFT.fieldTorsionFreeModPowerQuotient_residueChar_finite, Anabelian.LCFT.exists_integerUnit_not_isOfFinOrder, Anabelian.LCFT.integerUnitTorsionFree_pow_not_surjective_residueChar, Anabelian.LCFT.integerUnitTorsionFreeModPowerQuotient_residueChar_nontrivial")
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

:::theorem "abelianization_residue_characteristic_rank" (parent := "integral_mono_anabelian") (uses := "local_reciprocity_input, residue_absolute_galois_torsion_free, local_multiplicative_residue_characteristic_rank, abelianization_prime_to_p_rank") (lean := "Anabelian.LCFT.integerUnitModPowerToAbelianizedModPower, Anabelian.LCFT.integerUnitModPowerToAbelianizedModPower_injective, Anabelian.LCFT.abelianizedModPowerToResidue_residueChar_surjective, Anabelian.LCFT.abelianizedModPowerToResidue_integerUnit, Anabelian.LCFT.abelianizedTorsionFreeModPowerQuotient_card_ge_residueChar_sq")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "19--20"
    text := some { path := "source/hoshi.txt", startLine := 853, endLine := 893 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-17.png" }
  }]
}
%%%

At $`p=p_K`, local reciprocity preserves both the local-unit and unramified
directions.  Consequently
$$`p_K^2\le
  \#\left((G_K^{\mathrm{ab}}/\operatorname{tor})/
  p_K(G_K^{\mathrm{ab}}/\operatorname{tor})\right).`
Together with the prime-to-$`p_K` calculation, this proves the existence and
uniqueness portion of Hoshi's residue-characteristic predicate.
:::

:::proof "abelianization_residue_characteristic_rank" (uses := "local_reciprocity_input, residue_absolute_galois_torsion_free, local_multiplicative_residue_characteristic_rank, abelianization_prime_to_p_rank")
Suppose a local-unit class becomes a $`p_K`th power after applying reciprocity
and quotienting by torsion.  Lift a putative root to $`G_K^{\mathrm{ab}}`.
Its unramified projection has a power of finite order.  Torsion-freeness of
the residue absolute Galois group makes that projection trivial, so the root
lies in inertia.  The units--inertia equivalence supplies a local-unit
preimage, and injectivity of reciprocity reflects the remaining torsion
relation back to the unit group.  Thus the unit mod-power quotient injects
into the abelianized one.

The unramified projection is surjective on mod-$`p_K` quotients because the
uniformizer maps to Frobenius, which generates the residue quotient of order
$`p_K`.  Local units lie in its kernel.  That kernel has at least $`p_K`
elements, while the image has exactly $`p_K`; the kernel--image cardinality
formula gives the claimed $`p_K^2` lower bound.
:::

:::theorem "exact_residue_characteristic_degree" (parent := "integral_mono_anabelian") (uses := "local_reciprocity_input, residue_absolute_galois_torsion_free, finite_index_torsion_cancellation, abelianization_residue_characteristic_rank") (lean := "Anabelian.LCFT.fieldModPowerDiscreteValuationMod_ker_eq_integerUnit_range, Anabelian.LCFT.fieldTorsionFreeModPowerQuotient_card_eq_residueDegreeProduct_succ, Anabelian.LCFT.abelianizedModPowerToResidue_ker_eq_integerUnit_range, Anabelian.LCFT.abelianizedTorsionFreeModPowerQuotient_card_eq_residueDegreeProduct_succ")
%%%
source := {
  document := "hoshi"
  spans := #[
    {
      page := "11--12"
      text := some { path := "source/hoshi.txt", startLine := 350, endLine := 417 }
      pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-09.png" }
    },
    {
      page := "19--21"
      text := some { path := "source/hoshi.txt", startLine := 853, endLine := 933 }
      pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-17.png" }
    }
  ]
}
%%%

The lower-bound calculation sharpens to Hoshi's exact absolute-degree formula:
$$`\#\left((G_K^{\mathrm{ab}}/\operatorname{tor})/
p_K(G_K^{\mathrm{ab}}/\operatorname{tor})\right)
=p_K^{e_Kf_K+1}.`
The identical formula holds for $`K^\times`.  Hence the base-$`p_K`
logarithm, minus the single unramified direction, is exactly
$`d_K=e_Kf_K`.
:::

:::proof "exact_residue_characteristic_degree" (uses := "local_reciprocity_input, residue_absolute_galois_torsion_free, finite_index_torsion_cancellation")
Discrete valuation modulo $`p_K` on the field quotient is surjective, and its
kernel is exactly the image of the local-unit quotient.  For a class in the
kernel, adjust a representative by a uniformizer power; the vanishing of its
valuation modulo $`p_K` makes that adjustment a $`p_K`th power.  Multiplying
the kernel cardinal $`p_K^{e_Kf_K}` by the unramified image cardinal $`p_K`
gives the field formula.

The reciprocity-side argument has the same shape.  If an abelianized class
maps to a $`p_K`th power in the residue Galois group, lift the root through the
unramified projection and divide by its $`p_K`th power.  The remainder lies
in inertia and therefore comes from a local unit.  Torsion-freeness of the
residue absolute Galois group removes the only possible discrepancy.  Thus
the reciprocity-side kernel is precisely the unit image, and the same
kernel--image product gives $`p_K^{e_Kf_K+1}`.
:::

:::theorem "prime_to_torsion_residue_degree" (parent := "integral_mono_anabelian") (uses := "local_reciprocity_input, principal_unit_prime_to_p_divisibility, residue_absolute_galois_torsion_free, local_arithmetic_invariants") (lean := "Anabelian.LCFT.principalUnitGroup_torsion_finite, Anabelian.LCFT.principalUnitTorsion_pow_injective_of_ne_residueChar, Anabelian.LCFT.principalUnitTorsion_orderOf_eq_residueChar_pow, Anabelian.LCFT.integerUnitTorsionReduction, Anabelian.LCFT.integerUnitTorsionReduction_ker, Anabelian.LCFT.integerUnitPrimeToTorsionQuotientEquivResidueUnits, Anabelian.LCFT.one_add_integerUnitPrimeToTorsionQuotient_card, Anabelian.LCFT.integerUnitTorsionEquivAbelianizedTorsion, Anabelian.LCFT.integerUnitPrimeToTorsionQuotientEquivAbelianized, Anabelian.LCFT.one_add_abelianizedPrimeToTorsionQuotient_card_eq_residueChar_pow_residueDegree")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "19--21"
    text := some { path := "source/hoshi.txt", startLine := 853, endLine := 933 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-17.png" }
  }]
}
%%%

Reduction on finite-order valuation-ring units induces the exact equivalence
$$`\operatorname{tor}(\mathcal O_K^\times)/
  \operatorname{tor}(\mathcal O_K^\times)[p^\infty]
  \simeq k_K^\times.`
Consequently its cardinality is $`p_K^{f_K}-1`.  Local reciprocity identifies
all torsion in $`G_K^{\mathrm{ab}}` with torsion local units, and hence
$$`1+\#\left(
  \operatorname{tor}(G_K^{\mathrm{ab}})/
  \operatorname{tor}(G_K^{\mathrm{ab}})[p_K^\infty]
  \right)=p_K^{f_K}.`
This is the exact prime-to-$`p_K` torsion formula used to recover Hoshi's
residue-degree integer.
:::

:::proof "prime_to_torsion_residue_degree" (uses := "local_reciprocity_input, principal_unit_prime_to_p_divisibility, residue_absolute_galois_torsion_free")
Torsion in the principal-unit group is finite.  For every prime
$`\ell\ne p_K`, Hensel divisibility makes its $`\ell`th-power endomorphism
surjective and hence injective.  If $`\ell` divided the order of a torsion
principal unit, raising that unit to the order divided by $`\ell` would
produce a nontrivial element killed by this injective map.  Thus every
torsion principal unit has $`p_K`-power order.

Reduction from torsion units onto $`k_K^\times` is surjective by the
root-of-unity lifting theorem.  Its kernel consists of torsion principal
units and is therefore $`p_K`-primary.  Conversely a $`p_K`-primary unit
reduces to one because Frobenius is injective on the finite residue field.
The first isomorphism theorem gives the displayed equivalence.

Finally, a torsion class in $`G_K^{\mathrm{ab}}` has torsion unramified
projection.  The residue absolute Galois group is torsion-free, so that class
lies in inertia.  The units--inertia equivalence supplies a unique local-unit
preimage, and injectivity of reciprocity reflects its finite-order relation.
This transports the prime-to-primary quotient and its exact cardinality.
:::

:::theorem "exact_group_theoretic_numerical_invariants" (parent := "integral_mono_anabelian") (uses := "exact_residue_characteristic_degree, prime_to_torsion_residue_degree") (lean := "Anabelian.LCFT.abelianizedTorsionFree_modPowerRank_eq_residueDegreeProduct_succ, Anabelian.LCFT.abelianized_groupTheoreticAbsoluteDegree_eq_residueDegreeProduct, Anabelian.LCFT.abelianized_groupTheoreticResidueDegree_eq_localResidueDegree, Anabelian.LCFT.abelianized_groupTheoreticRamificationIndex_eq_absoluteRamificationIndex, Anabelian.OTriangle.LocalGaloisGroup.groupTheoreticAbsoluteDegree_eq_residueDegreeProduct, Anabelian.OTriangle.LocalGaloisGroup.groupTheoreticResidueDegree_eq_localResidueDegree, Anabelian.OTriangle.LocalGaloisGroup.groupTheoreticRamificationIndex_eq_absoluteRamificationIndex")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "19--21"
    text := some { path := "source/hoshi.txt", startLine := 872, endLine := 949 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-18.png" }
  }]
}
%%%

At the detected residue characteristic, all three numerical expressions in
Hoshi's Definition 3.5 have now been evaluated:
$$`d(G_K)=e_Kf_K,\qquad f(G_K)=f_K,\qquad e(G_K)=e_K.`
Thus the numerical ramification index used in the intrinsic intersection
definitions agrees with the classical absolute ramification index.
:::

:::proof "exact_group_theoretic_numerical_invariants" (uses := "exact_residue_characteristic_degree, prime_to_torsion_residue_degree")
The exact mod-$`p_K` cardinality is $`p_K^{e_Kf_K+1}`; taking its base-$`p_K`
logarithm and subtracting the single unramified direction gives
$`d(G_K)=e_Kf_K`.  The exact prime-to-primary torsion formula has logarithm
$`f_K`, giving $`f(G_K)=f_K`.  Since $`f_K>0`, natural-number cancellation in
$`e_Kf_K/f_K` gives $`e(G_K)=e_K`.
:::

:::theorem "group_theoretic_local_invariants" (parent := "integral_mono_anabelian") (uses := "abelianization_prime_to_p_rank, abelianization_residue_characteristic_rank, exact_group_theoretic_numerical_invariants")
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

:::proof "group_theoretic_local_invariants" (uses := "local_reciprocity_input, exact_group_theoretic_numerical_invariants")
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

:::theorem "residue_characteristic_predicate" (parent := "integral_mono_anabelian") (uses := "topological_abelianized_transport, abelianization_residue_characteristic_rank") (lean := "Anabelian.OTriangle.GroupTheoreticInvariants.torsionFreeQuotient, Anabelian.OTriangle.GroupTheoreticInvariants.torsionFreeQuotientEquiv, Anabelian.OTriangle.GroupTheoreticInvariants.modPowerQuotient, Anabelian.OTriangle.GroupTheoreticInvariants.modPowerQuotientEquiv, Anabelian.OTriangle.GroupTheoreticInvariants.modPowerRank, Anabelian.OTriangle.GroupTheoreticInvariants.isResidueCharacteristicCandidate_congr, Anabelian.OTriangle.GroupTheoreticInvariants.torsionEquiv, Anabelian.OTriangle.GroupTheoreticInvariants.primeToTorsionQuotient, Anabelian.OTriangle.GroupTheoreticInvariants.primeToTorsionQuotientEquiv, Anabelian.OTriangle.GroupTheoreticInvariants.absoluteDegree, Anabelian.OTriangle.GroupTheoreticInvariants.residueDegree, Anabelian.OTriangle.GroupTheoreticInvariants.ramificationIndex, Anabelian.OTriangle.GroupTheoreticInvariants.ramificationIndex_congr, Anabelian.OTriangle.LocalGaloisGroup.torsionFreeAbelianization, Anabelian.OTriangle.LocalGaloisGroup.abelianizationModPowerRank, Anabelian.OTriangle.LocalGaloisGroup.IsResidueCharacteristicCandidate, Anabelian.OTriangle.LocalGaloisGroup.isResidueCharacteristicCandidate_iff, Anabelian.OTriangle.LocalGaloisGroup.isResidueCharacteristicCandidate_iff_reciprocity, Anabelian.OTriangle.LocalGaloisGroup.groupTheoreticAbsoluteDegree, Anabelian.OTriangle.LocalGaloisGroup.groupTheoreticResidueDegree, Anabelian.OTriangle.LocalGaloisGroup.groupTheoreticRamificationIndex, Anabelian.OTriangle.LocalGaloisGroup.groupTheoreticRamificationIndex_eq")
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
ramification index.  The exact local-field calculations above identify these
three expressions with $`e_Kf_K`, $`f_K`, and $`e_K`, respectively.  The
remaining comparison is the subgroup-theoretic ramification and Frobenius
content of Hoshi's Proposition 3.6 and Lemma 3.7.
:::

:::theorem "fixed_field_ramification_indices" (parent := "integral_mono_anabelian") (uses := "local_reciprocity_input, exact_group_theoretic_numerical_invariants, topological_abelianized_transport") (lean := "Anabelian.LCFT.FiniteExtension.relativeRamificationIndex, Anabelian.LCFT.FiniteExtension.map_localMaximalIdeal_eq_pow, Anabelian.LCFT.FiniteExtension.relativeRamificationIndex_pos, Anabelian.LCFT.FiniteExtension.relativeRamificationIndex_eq_ramificationIdx, Anabelian.LCFT.FiniteExtension.residueChar_eq, Anabelian.LCFT.FiniteExtension.map_residueCharIdeal, Anabelian.LCFT.FiniteExtension.absoluteRamificationIndex_eq_mul, Anabelian.OTriangle.LocalGaloisGroup.fixedFieldBaseExtension, Anabelian.OTriangle.LocalGaloisGroup.intrinsicRamificationIndex_eq_absoluteRamificationIndex, Anabelian.OTriangle.LocalGaloisGroup.openSubgroupIntrinsicRamificationIndex_eq_fixedField, Anabelian.OTriangle.LocalGaloisGroup.isInertiaNeighborhood_iff_relativeRamificationIndex_eq_one, Anabelian.OTriangle.LocalGaloisGroup.isWildInertiaNeighborhood_iff_relativeRamificationIndex_coprime")
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

For a finite valued extension $`L/K`, define $`e(L/K)` by
$$`\mathfrak m_K\mathcal O_L=\mathfrak m_L^{e(L/K)}.`
The DVR ideal factorization gives the exact tower law
$$`e_L=e_K e(L/K).`
At an open subgroup $`U\leq G_K`, topological abelianization identifies
Hoshi's numerical index with $`e_{\overline K^U}`.  Therefore an intrinsic
inertia neighborhood is exactly a normal $`U` with
$`e(\overline K^U/K)=1`, while a wild-inertia neighborhood is exactly a
normal $`U` whose relative index is prime to $`p_K`.
:::

:::proof "fixed_field_ramification_indices" (uses := "local_reciprocity_input, exact_group_theoretic_numerical_invariants, topological_abelianized_transport")
The image of the base maximal ideal is a nonzero proper ideal in the upstairs
DVR, hence a unique power of its maximal ideal; this defines $`e(L/K)`.
The residue characteristics agree because the induced embedding of residue
fields preserves characteristic.  Mapping the identity
$`p_K\mathcal O_K=\mathfrak m_K^{e_K}` into $`\mathcal O_L`, then substituting
the relative maximal-ideal factorization, gives
$`p_K\mathcal O_L=\mathfrak m_L^{e_Ke(L/K)}`.  Uniqueness of powers in a DVR
proves the tower law.

For an open subgroup, the continuous fixed-field Galois equivalence descends
to topological abelianizations.  The exact reciprocity calculation evaluates
the transported group-theoretic index as the fixed field's absolute index.
Substitution of the tower law and cancellation by the positive integer $`e_K`
give the two neighborhood characterizations.
:::

:::theorem "finite_fixed_field_inertia_order" (parent := "integral_mono_anabelian") (uses := "fixed_field_ramification_indices") (lean := "Anabelian.OTriangle.LocalGaloisGroup.fixedFieldFiniteInertia_card, Anabelian.OTriangle.PointedMixedCharLocalField.spectralPointing, Anabelian.OTriangle.LocalGaloisGroup.spectralInertiaSubgroup, Anabelian.OTriangle.LocalGaloisGroup.map_spectralInertiaSubgroup_restrictNormalHom, Anabelian.OTriangle.LocalGaloisGroup.spectralInertiaSubgroup_le_iff_relativeRamificationIndex_eq_one")
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

Let $`U\triangleleft G_K` be open and put $`L=\overline K^U`.  For the
canonical spectral valuation on $`L`, the finite Galois inertia group has
order
$$`\# I(L/K)=e(L/K).`
In particular $`L/K` is unramified exactly when this finite inertia group is
trivial.  This is the finite-level bridge needed to turn the relative-index
criterion into containment of the full inertia subgroup in $`U`.
:::

:::proof "finite_fixed_field_inertia_order" (uses := "fixed_field_ramification_indices")
Normality of $`U` makes the fixed extension $`L/K` Galois.  The spectral
valuation is invariant under every $`K`-automorphism, so the action restricts
to $`\mathcal O_L` and descends to its residue field.  The integral closure
of $`\mathcal O_K` in $`L` is $`\mathcal O_L`; finite Galois ramification
theory therefore identifies the cardinality of the kernel of the residue
action with Mathlib's ramification index of $`\mathfrak m_L` over
$`\mathcal O_K`.  The maximal-ideal factorization theorem identifies that
index with the previously constructed integer $`e(L/K)`.

To compare the finite kernel with full inertia, equip the common algebraic
closure with its spectral valuation while retaining the given valuation on
$`K`.  Restriction sends full spectral inertia into finite inertia.  Conversely,
lift a finite-inertia automorphism to the algebraic closure.  Its residue
action fixes $`\kappa_L`; surjectivity of the residue action over $`L`
supplies a correcting automorphism with the same action.  Dividing by that
correction gives an inertial lift with the prescribed restriction.  Hence
restriction maps full inertia onto finite inertia, while infinite Galois
theory identifies its kernel with $`U`.  The cardinality formula therefore
gives $`I_K\subseteq U\iff e(L/K)=1`.
:::

:::theorem "canonical_unramified_fixed_fields" (parent := "integral_mono_anabelian") (uses := "finite_fixed_field_inertia_order") (lean := "Anabelian.OTriangle.LocalGaloisGroup.fixedFieldIntegerIsGaloisGroup, Anabelian.OTriangle.LocalGaloisGroup.fixedFieldFiniteInertia_card_mul_residueField_finrank, Anabelian.OTriangle.LocalGaloisGroup.residueUnramifiedOpenSubgroup, Anabelian.OTriangle.LocalGaloisGroup.residueUnramifiedOpenSubgroup_normal, Anabelian.OTriangle.LocalGaloisGroup.spectralInertiaSubgroup_le_residueUnramifiedOpenSubgroup, Anabelian.OTriangle.LocalGaloisGroup.residueUnramified_relativeRamificationIndex_eq_one, Anabelian.OTriangle.LocalGaloisGroup.residueUnramified_fixedField_finrank, Anabelian.OTriangle.LocalGaloisGroup.residueUnramified_residueField_finrank, Anabelian.OTriangle.LocalGaloisGroup.residueUnramifiedResidueEmbedding, Anabelian.OTriangle.LocalGaloisGroup.residueUnramifiedResidueEmbedding_fieldRange, Anabelian.OTriangle.LocalGaloisGroup.ResidueFiniteGaloisIntermediateField, Anabelian.OTriangle.LocalGaloisGroup.residueUnramifiedOpenSubgroupOf, Anabelian.OTriangle.LocalGaloisGroup.residueUnramifiedOpenSubgroupOf_normal, Anabelian.OTriangle.LocalGaloisGroup.residueUnramifiedOf_relativeRamificationIndex_eq_one, Anabelian.OTriangle.LocalGaloisGroup.residueUnramifiedOf_fixedField_finrank, Anabelian.OTriangle.LocalGaloisGroup.residueUnramifiedOf_residueField_finrank, Anabelian.OTriangle.LocalGaloisGroup.residueUnramifiedOfResidueEmbedding, Anabelian.OTriangle.LocalGaloisGroup.residueUnramifiedOfResidueEmbedding_fieldRange")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "20--21"
    text := some { path := "source/hoshi.txt", startLine := 900, endLine := 976 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-19.png" }
  }]
}
%%%

For every $`n>0`, let $`k_n` be the unique degree-$`n` subfield of the
chosen algebraic closure $`\overline{k_K}` of the residue field.  The inverse
image of $`\operatorname{Gal}(\overline{k_K}/k_n)` under the spectral residue
action is an open normal subgroup $`U_n\triangleleft G_K`.  Its fixed field
$`K_n=\overline K^{U_n}` is unramified of degree $`n`, and reduction identifies
its residue field with the selected subfield:
$$`
 [K_n:K]=[k_{K_n}:k_K]=n,
 \qquad \operatorname{im}(k_{K_n}\hookrightarrow\overline{k_K})=k_n.
`
:::

:::proof "canonical_unramified_fixed_fields" (uses := "finite_fixed_field_inertia_order")
Finite-field theory embeds the standard degree-$`n` extension into
$`\overline{k_K}`; its field range is finite Galois and has degree $`n`.
Continuity and surjectivity of the spectral residue action show that the
inverse image of its fixing subgroup is open and has index $`n`; normality is
preserved by inverse image.  Since the kernel of the residue action is
spectral inertia, that inertia lies in $`U_n`, and the finite fixed-field
criterion gives $`e(K_n/K)=1`.

For later use, the integral Galois action on every normal fixed field is
packaged independently: its invariant subring is $`\mathcal O_K` and it is
faithful on $`\mathcal O_L`.  The finite inertia--residue identity then gives
$$`
  [L:K]=\#I(L/K)[k_L:k_K].
`
Applying it to $`K_n`, where inertia has order one, proves that the residue
degree is $`n`.

Finally, reduction along $`K_n\hookrightarrow\overline K` gives an embedding
$`k_{K_n}\hookrightarrow\overline{k_K}`.  Every element in its range is fixed
by $`\operatorname{Gal}(\overline{k_K}/k_n)`: lift such a residue automorphism
to $`G_K`, observe that the lift lies in $`U_n`, and reduce the fact that it
fixes $`K_n`.  Thus the range is contained in $`k_n`; both fields have degree
$`n`, so finite-dimensionality upgrades containment to equality.

The same construction is also formalized with an arbitrary finite Galois
intermediate field $`E\subset\overline{k_K}` in place of the standard
degree-$`n` field.  Its inverse-image subgroup cuts out an unramified field
$`K_E`, and reduction has field range literally equal to $`E`.  Taking
$`E` to be the finite Galois closure generated by a chosen residue element
will let the tame-conjugation argument lift that element without replacing
the ambient spectral residue action by an abstractly isomorphic copy.
:::

:::theorem "intrinsic_ramification_intersections" (parent := "integral_mono_anabelian") (uses := "residue_characteristic_predicate, finite_fixed_field_inertia_order") (lean := "Anabelian.OTriangle.IntrinsicRamification.ramificationIndex, Anabelian.OTriangle.IntrinsicRamification.ramificationIndex_congr, Anabelian.OTriangle.IntrinsicRamification.IsInertiaNeighborhood, Anabelian.OTriangle.IntrinsicRamification.IsWildInertiaNeighborhood, Anabelian.OTriangle.IntrinsicRamification.inertiaSubgroup, Anabelian.OTriangle.IntrinsicRamification.wildInertiaSubgroup, Anabelian.OTriangle.IntrinsicRamification.inertiaSubgroup_normal, Anabelian.OTriangle.IntrinsicRamification.wildInertiaSubgroup_normal, Anabelian.OTriangle.IntrinsicRamification.wildInertiaSubgroup_le_inertiaSubgroup, Anabelian.OTriangle.IntrinsicRamification.isInertiaNeighborhood_map_iff, Anabelian.OTriangle.IntrinsicRamification.isWildInertiaNeighborhood_map_iff, Anabelian.OTriangle.IntrinsicRamification.map_inertiaSubgroup, Anabelian.OTriangle.IntrinsicRamification.map_wildInertiaSubgroup, Anabelian.OTriangle.LocalGaloisGroup.map_intrinsicInertiaSubgroup, Anabelian.OTriangle.LocalGaloisGroup.map_intrinsicWildInertiaSubgroup, Anabelian.OTriangle.ClassicalRamification.inertiaSubgroup_eq_spectralPointing, Anabelian.OTriangle.LocalGaloisGroup.classicalInertiaSubgroup_le_iff_isInertiaNeighborhood, Anabelian.OTriangle.LocalGaloisGroup.intrinsicInertiaSubgroup_eq_classicalInertiaSubgroup")
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

For the presented local group, reciprocity applied to the identity extension
between the recorded pointing and the canonical spectral pointing identifies
their abelianized inertia groups.  Full inertia is the inverse image of
abelianized inertia, so the full kernels agree.  The finite restriction
criterion above now says that intrinsic inertia neighborhoods are exactly the
normal open subgroups containing classical inertia.  One inclusion of the
intersections is immediate.  For the other, profinite separation supplies,
for any element outside the closed classical inertia subgroup, an open normal
supergroup of inertia that still excludes the element.  Thus intrinsic inertia
is exactly classical inertia.
:::

:::theorem "finite_tame_character" (parent := "integral_mono_anabelian") (uses := "fixed_field_ramification_indices, finite_fixed_field_inertia") (lean := "Anabelian.OTriangle.FiniteTameRamification.tameCharacter, Anabelian.OTriangle.FiniteTameRamification.tameCharacter_injective_of_coprime_card, Anabelian.OTriangle.FiniteTameRamification.tameCharacter_conjugate, Anabelian.OTriangle.FiniteTameRamification.conjugate_eq_pow_of_residue_frobenius, Anabelian.OTriangle.SpectralLocalField.integerMulSemiringAction_faithful, Anabelian.OTriangle.LocalGaloisGroup.fixedFieldFiniteTameCharacter_injective, Anabelian.OTriangle.LocalGaloisGroup.fixedFieldRestrictNormalHom, Anabelian.OTriangle.LocalGaloisGroup.fixedFieldRestrictNormalHom_ker, Anabelian.OTriangle.LocalGaloisGroup.restrict_conjugation_eq_pow_of_fixedField_residue_frobenius, Anabelian.OTriangle.LocalGaloisGroup.fixedField_residue_smul_eq_pow_of_spectralResidueFrobenius, Anabelian.OTriangle.LocalGaloisGroup.spectralFrobenius_isFrobeniusRepresentative")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "13--14"
    text := some { path := "source/hoshi.txt", startLine := 527, endLine := 559 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-12.png" }
  }]
}
%%%

Let a finite group act faithfully on a discrete valuation ring $`R`, and let
$`I` be the subgroup acting trivially on its residue field.  Choosing a
uniformizer $`\pi`, reduction of the multiplier
$`\tau(\pi)/\pi` defines the tame character
$$`
  \theta_\pi:I\longrightarrow \kappa_R^\times.
`
If the order of $`I` is prime to the residue characteristic $`p`, then
$`\theta_\pi` is injective.  It is equivariant for conjugation and the
residue action.  Hence an element acting on the residue field by the
$`q`-power Frobenius conjugates every $`\tau\in I` to $`\tau^q`.

For a normal finite fixed field $`L/K` in the spectral algebraic closure,
restriction to $`\mathcal O_L` is faithful and the order of finite inertia is
$`e(L/K)`.  Therefore Hoshi's prime-to-$`p` relative-index condition makes
the finite fixed-field tame character injective and yields the finite tame
conjugation relation required by Lemma 1.5.
:::

:::proof "finite_tame_character" (uses := "fixed_field_ramification_indices, finite_fixed_field_inertia")
Write $`\tau(\pi)=\pi u_\tau`.  Multiplication of automorphisms gives
$`u_{\tau\upsilon}=u_\tau\tau(u_\upsilon)`, and inertia acts trivially after
reduction, so $`\tau\mapsto\overline{u_\tau}` is a homomorphism.  If
$`\overline{u_\tau}=1`, then
$`\tau(x)-x\in\mathfrak m^{n+1}` whenever
$`x\in\mathfrak m^n`.  For $`r=\operatorname{ord}(\tau)` the telescoping sum
$$`
  \sum_{i=0}^{r-1}\tau^i(\tau(x)-x)=\tau^r(x)-x=0
`
and invertibility of $`r` in $`R` improve
$`\tau(x)-x\in\mathfrak m^n` to membership in
$`\mathfrak m^{n+1}`.  Krull intersection then gives $`\tau(x)=x` for every
$`x`, and faithfulness gives $`\tau=1`.

For arbitrary $`\sigma`, comparison of the uniformizer multipliers for
$`\sigma\tau\sigma^{-1}` shows
$`\theta(\sigma\tau\sigma^{-1})=\overline\sigma(\theta(\tau))`.
If $`\overline\sigma(z)=z^q`, injectivity identifies the conjugate with
$`\tau^q`.  At a finite fixed field the finite inertia cardinality theorem
replaces $`|I|` by $`e(L/K)`, exactly matching the prime-to-$`p` hypothesis.
Restriction has kernel the original open subgroup.  Consequently, after
testing the relation at every prime-to-$`p` neighborhood, the Frobenius
commutator lies in their intersection $`P(G,p)`.  The residue-field cardinality
formula and exact reciprocity identity
$`f(G)=f_K` replace the finite exponent by $`p^{f(G)}`.  Thus every lift of
arithmetic Frobenius for the spectral pointing is now proved to satisfy
Hoshi's intrinsic representative predicate.
:::

:::theorem "explicit_tame_kummer_extensions" (parent := "integral_mono_anabelian") (uses := "fixed_field_ramification_indices, finite_fixed_field_inertia_order, finite_tame_character") (lean := "Anabelian.LCFT.localUniformizer_X_pow_sub_C_irreducible, Anabelian.LCFT.tameKummerIntermediateField, Anabelian.LCFT.tameKummerFiniteGaloisIntermediateField, Anabelian.LCFT.tameKummerIntermediateField_finrank, Anabelian.LCFT.tameKummerRoot, Anabelian.LCFT.tameKummerRoot_pow, Anabelian.LCFT.tameKummerRoot_isIntegral, Anabelian.LCFT.tameKummerGeneratorAutomorphism, Anabelian.LCFT.tameKummerGeneratorAutomorphism_apply_root, Anabelian.LCFT.tameKummerOpenSubgroup, Anabelian.LCFT.tameKummer_fixedField_eq, Anabelian.LCFT.tameKummerFixedFieldEquiv, Anabelian.LCFT.tameKummerFixedRoot, Anabelian.LCFT.tameKummerFixedRoot_pow, Anabelian.LCFT.tameKummerFixedRoot_isIntegral, Anabelian.LCFT.tameKummerFixedIntegerRoot, Anabelian.LCFT.tameKummerFixedGeneratorAutomorphism, Anabelian.LCFT.tameKummerFixedGeneratorAutomorphism_apply_root, Anabelian.LCFT.tameKummer_relativeRamificationIndex_eq, Anabelian.LCFT.tameKummerFixedIntegerRoot_irreducible, Anabelian.LCFT.unit_eq_one_of_pow_eq_one_of_residue_eq_one_of_coprime, Anabelian.LCFT.orderOf_unitsMap_residue_eq_of_coprime, Anabelian.LCFT.exists_tameKummerInertiaGenerator_tameCharacter, Anabelian.LCFT.exists_tameKummerInertiaGenerator_tameCharacter_isPrimitiveRoot, Anabelian.LCFT.uniformizer_X_pow_sub_C_irreducible, Anabelian.LCFT.uniformizerKummerIntermediateField, Anabelian.LCFT.uniformizerKummerFiniteGaloisIntermediateField, Anabelian.LCFT.uniformizerKummerIntermediateField_finrank, Anabelian.LCFT.uniformizerKummerRoot, Anabelian.LCFT.uniformizerKummerRoot_pow, Anabelian.LCFT.uniformizerKummerGeneratorAutomorphism, Anabelian.LCFT.uniformizerKummerGeneratorAutomorphism_apply_root, Anabelian.LCFT.uniformizerKummerOpenSubgroup, Anabelian.LCFT.uniformizerKummer_relativeRamificationIndex_eq, Anabelian.LCFT.uniformizerKummerFixedIntegerRoot_irreducible, Anabelian.LCFT.exists_uniformizerKummerInertiaGenerator_tameCharacter")
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

Let $`K` be a mixed-characteristic local field, let $`n>0`, and assume that
$`K` contains a primitive $`n`th root of unity $`\zeta`.  For a uniformizer
$`\pi_K`, the splitting field
$$`L_n=K\bigl((\pi_K)^{1/n}\bigr)`
of $`X^n-\pi_K` in the chosen algebraic closure is a finite Galois extension
with
$$`[L_n:K]=e(L_n/K)=n.`
Writing $`\alpha^n=\pi_K`, its cyclic Galois group has a distinguished
generator $`\tau_n` satisfying $`\tau_n(\alpha)=\zeta\alpha`.
:::

:::proof "explicit_tame_kummer_extensions" (uses := "fixed_field_ramification_indices, finite_fixed_field_inertia_order, finite_tame_character")
The polynomial $`X^n-\pi_K` is Eisenstein: all non-leading coefficients lie
in the maximal ideal, while its constant coefficient lies outside the square
of that ideal.  Gauss's lemma therefore makes it irreducible over $`K`.
The standard Kummer description of its splitting field, using the primitive
root already in $`K`, computes its degree as $`n` and supplies the generator
$`\alpha\mapsto\zeta\alpha`.

Embed this splitting field into the fixed algebraic closure and take its
fixing subgroup $`U_n`.  Infinite Galois theory identifies the corresponding
spectral fixed field with $`L_n`.  The distinguished root is integral over
$`\mathcal O_K`; in the spectral valuation ring its equation implies
$$`\mathfrak m_K\mathcal O_{L_n}\subseteq\mathfrak m_{L_n}^{n}.`
Comparing DVR coheights with the defining identity
$`\mathfrak m_K\mathcal O_{L_n}=\mathfrak m_{L_n}^{e(L_n/K)}` gives
$`n\le e(L_n/K)`.  On the other hand, finite Galois ramification identifies
$`e(L_n/K)` with the order of a subgroup of $`\operatorname{Gal}(L_n/K)`,
whose order is the degree $`n`.  Thus $`e(L_n/K)=n`.

Transporting the splitting-field presentation across the fixed-field
equality gives a literal element $`\alpha\in\overline K^{U_n}` and a literal
automorphism $`\tau_n` of that fixed field.  Equality of the two ideal powers
then shows that $`\alpha` generates the maximal ideal, so it is a
uniformizer.  The arbitrary-uniformizer formula for the finite tame character
therefore computes
$$`
  \theta(\tau_n)=\overline\zeta.
`
This is the finite faithful Kummer character that will detect the action of
unramified classes on tame inertia.  If $`(n,p_K)=1`, reduction preserves the
exact order of $`\zeta`: a prime-to-$`p_K` root of unity congruent to one is
trivial by the geometric-sum factorization of $`X^n-1`.  Hence
$`\theta(\tau_n)` is itself a primitive $`n`th root.

For the conjugation calculation, the same development is parameterized by an
arbitrary $`\pi\in\mathcal O_K` satisfying
$`(\pi)=\mathfrak m_K`.  The corresponding polynomial is Eisenstein, its
embedded splitting field is finite Galois, its distinguished root is a
uniformizer, and the cyclic generator again has tame character
$`\overline\zeta`.  This parameterized form permits $`\pi_K` to be carried
unchanged into an unramified extension, where
$`\mathfrak m_K\mathcal O_L=\mathfrak m_L`, instead of relying on unrelated
noncomputable choices of a uniformizer in $`K` and $`L`.
:::

:::theorem "intrinsic_frobenius_characterization" (parent := "integral_mono_anabelian") (uses := "intrinsic_ramification_intersections, finite_tame_character, canonical_unramified_fixed_fields, explicit_tame_kummer_extensions") (lean := "Anabelian.OTriangle.IntrinsicRamification.inertiaQuotient, Anabelian.OTriangle.IntrinsicRamification.IsFrobeniusRepresentative, Anabelian.OTriangle.IntrinsicRamification.IsFrobeniusClass, Anabelian.OTriangle.IntrinsicRamification.HasUniqueFrobeniusClass, Anabelian.OTriangle.IntrinsicRamification.frobeniusClass, Anabelian.OTriangle.IntrinsicRamification.frobeniusClass_spec, Anabelian.OTriangle.IntrinsicRamification.isFrobeniusRepresentative_map_iff, Anabelian.OTriangle.IntrinsicRamification.inertiaQuotientEquiv, Anabelian.OTriangle.IntrinsicRamification.inertiaQuotientEquiv_mk, Anabelian.OTriangle.IntrinsicRamification.isFrobeniusClass_map_iff, Anabelian.OTriangle.IntrinsicRamification.hasUniqueFrobeniusClass_congr, Anabelian.OTriangle.IntrinsicRamification.frobeniusClass_map, Anabelian.OTriangle.LocalGaloisGroup.HasUniqueIntrinsicFrobeniusClass, Anabelian.OTriangle.LocalGaloisGroup.hasUniqueIntrinsicFrobeniusClass_iff, Anabelian.LCFT.LocalReciprocityFamily.map_spectralPointing, Anabelian.OTriangle.LocalGaloisGroup.exists_commonFrobeniusLift, Anabelian.OTriangle.LocalGaloisGroup.TameConjugationFaithful, Anabelian.OTriangle.LocalGaloisGroup.inverse_mul_tameConjugation_trivial_of_frobeniusRepresentatives, Anabelian.OTriangle.LocalGaloisGroup.hasUniqueIntrinsicFrobeniusClass_of_tameConjugationFaithful, Anabelian.OTriangle.LocalGaloisGroup.intrinsicFrobeniusClass_classicalImage_of_tameConjugationFaithful, Anabelian.OTriangle.LocalGaloisGroup.hoshiRamificationComparison_of_tameConjugationFaithful")
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

:::proof "intrinsic_frobenius_characterization" (uses := "intrinsic_ramification_intersections, finite_tame_character, explicit_tame_kummer_extensions")
The congruence
$$`gxg^{-1}\equiv x^{p^f}\pmod {P(G,p)}`
is preserved by a group equivalence because multiplication, inversion, powers,
inertia membership, and wild-inertia membership are all preserved.  The
equivalence also descends to $`G/I(G,p)`, and maps the class of $`g` to the
class of its image.  Hence it bijects the classes satisfying the Frobenius
predicate.  Existence and uniqueness are invariant under this bijection, and
uniqueness identifies the chosen classes whenever the arithmetic hypothesis
is available on both sides.

For the presented local group, reciprocity applied to a uniformizer gives a
full Galois lift which is simultaneously arithmetic Frobenius for the
recorded and spectral residue pointings.  The finite tame-character theorem
proves that this lift has the required power action.  If conjugation on the
tame quotient is faithful, any second representative with the same power
action differs from it by inertia: after quotienting by wild inertia, the
two power relations show directly that their quotient centralizes tame
inertia.  Thus the entire existence, uniqueness, and classical-identification
step is reduced to `TameConjugationFaithful`; the Kummer characters above
provide its finite prime-to-$`p` detectors.
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
equivalent to $`L/K` being unramified.  The finite-restriction and
profinite-separation arguments now prove formally that intersecting all such
$`N` recovers inertia.  Requiring a positive prime-to-$`p` relative factor
similarly recovers wild inertia.  The tame relation
$`\varphi\tau\varphi^{-1}=\tau^q` then gives existence and uniqueness of the
class acting by the $`p^f`-power map and identifies it with arithmetic
Frobenius.  These are exactly Lemma 3.4, Proposition 3.6, Lemma 3.7, and
Proposition 3.9.  The finite tame relation is formalized at every
prime-to-$`p` normal fixed field.  The outstanding arithmetic implementation
behind the named Lean proposition is now confined to passing those finite
characters to the full tame quotient, identifying the wild-inertia
intersection, and proving that the resulting conjugation action distinguishes
a unique unramified class.
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
