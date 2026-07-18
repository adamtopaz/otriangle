import Verso
import VersoManual
import VersoBlueprint
import Otriangle.MonoAnabelian.Package

set_option linter.hashCommand false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Cyclotomic synchronization and Kummer comparison" =>

:::theorem "cyclotomic_synchronization" (parent := "integral_mono_anabelian")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "31--37"
    text := some { path := "source/hoshi.txt", startLine := 1519, endLine := 1857 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-33.png" }
  }]
}
%%%

The Frobenius-like cyclotome $`\Lambda(M)` extracted from an integral pair and
the étale-like cyclotome $`\Lambda(G)` extracted from its group admit a
functorial equivariant synchronization.  In the integral case the index group
$`\operatorname{Ind}^{\triangleright}` is trivial, so this is a unique natural
isomorphism rather than a nontrivial poly-isomorphism.
:::

:::proof "cyclotomic_synchronization" (uses := "group_theoretic_local_invariants, integral_mono_reconstruction")
Both cyclotomes are inverse limits of torsion in multiplicative monoids.  For
model pairs, local reciprocity identifies them with the Tate module of roots
of unity.  Hoshi's degree-two invariant recognizes the synchronizations
compatible with valuation.  Lemma 6.5 makes these an
$`\operatorname{Ind}^{\triangleright}`-torsor and Proposition 6.7 makes the
torsor functorial.  Definition 5.5 says the integral index group is trivial,
so exactly one natural synchronization remains.
:::

:::theorem "kummer_restriction" (parent := "integral_mono_anabelian")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "37--38"
    text := some { path := "source/hoshi.txt", startLine := 1859, endLine := 1905 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-35.png" }
  }]
}
%%%

The Kummer embeddings of $`M` and
$`\mathcal O^{\triangleright}(G)` into direct-limit cohomology are injective.
The synchronized cohomology isomorphism maps one Kummer image onto the other
and therefore restricts to an equivariant monoid isomorphism.
:::

:::proof "kummer_restriction" (uses := "cyclotomic_synchronization, integral_mono_reconstruction")
For every open $`H\leq G`, the Kummer kernel is the divisible subgroup of the
corresponding multiplicative group, which is trivial.  The injective limit
therefore gives Hoshi's map $`{}^\infty\!\operatorname{Kmm}`.  Proposition 6.7
makes synchronization compatible with model comparison, and Lemma 7.3
restricts the induced cohomology isomorphism to the two monoids.  Equivariance
and naturality descend from Kummer cohomology.
:::

:::theorem "integral_kummer_comparison" (parent := "integral_mono_anabelian") (lean := "Anabelian.LCFT.IntegralKummerComparison")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "38"
    text := some { path := "source/hoshi.txt", startLine := 1885, endLine := 1932 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-35.png" }
  }]
}
%%%

For an integral Galois pair $`G\curvearrowright M`, Kummer theory yields a
canonical equivariant isomorphism
$$`\kappa_{G,M}:M\simeq\mathcal O^{\triangleright}(G).`
Because the integral ambiguity group is trivial, this comparison is unique and
natural in isomorphisms of pairs.
:::

:::proof "integral_kummer_comparison" (uses := "kummer_restriction, cyclotomic_synchronization")
Kummer theory injects $`M` into cohomology formed from its Tate module.
Cyclotomic synchronization compares this with the module reconstructed from
$`G`; restriction gives $`\kappa_{G,M}`.  Naturality of Kummer theory and of
synchronization makes the comparison square commute.  Triviality of the
integral index group turns the poly-isomorphism into one canonical comparison.
:::

:::theorem "reconstruction_package" (parent := "integral_mono_anabelian") (uses := "integral_mono_reconstruction, integral_kummer_comparison") (lean := "Anabelian.LCFT.monoAnabelianReconstructionPackage_of_reciprocity") (priority := "high")
The algorithm of Summary 4.3 and the natural integral Kummer comparison of
Definition 7.4 together form a `MonoAnabelianReconstructionPackage`.  Thus a
fixed `LocalReciprocityFamily` determines a nonempty type of such packages.
:::
