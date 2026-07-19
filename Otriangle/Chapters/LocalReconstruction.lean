import Verso
import VersoManual
import VersoBlueprint
import Otriangle.LCFT
import Otriangle.MonoAnabelian.GroupTransport

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
