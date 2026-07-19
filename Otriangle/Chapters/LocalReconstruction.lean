import Verso
import VersoManual
import VersoBlueprint
import Otriangle.LCFT
import Otriangle.MonoAnabelian.GroupTransport
import Otriangle.MonoAnabelian.GroupInvariants
import Otriangle.MonoAnabelian.IntrinsicRamification
import Otriangle.MonoAnabelian.ClassicalRamification

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

:::theorem "group_theoretic_local_invariants" (parent := "integral_mono_anabelian")
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
