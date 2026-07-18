import Verso
import VersoManual
import VersoBlueprint
import Otriangle.OTriangle

set_option linter.hashCommand false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Integral Mono-anabelian Reconstruction" =>

This chapter explains the argument behind the full faithfulness of the
forgetful functor from mixed-characteristic local Galois groups equipped with
their multiplicative monoids of nonzero algebraic integers.  It follows
Hoshi's Summary 4.3, Definition 7.4, and Theorem 7.6(iv).

:::group "integral_mono_anabelian"
Reconstruction and rigidity for the multiplicative monoid of nonzero integers
in an algebraic closure of a mixed-characteristic local field.
:::

:::definition "integral_galois_pair" (parent := "integral_mono_anabelian") (lean := "Anabelian.OTriangle.LocalGaloisMonoid")
%%%
source := {
  document := "hoshi"
  spans := #[
    {
      page := "29--30"
      text := some {
        path := "source/hoshi.txt"
        startLine := 1390
        endLine := 1454
      }
      pdf := some {
        path := "source/hoshi.pdf"
        image := "source/hoshi-page-27.png"
      }
    }
  ]
}
%%%

For a pointed mixed-characteristic local field $`K` with chosen algebraic
closure $`\overline K`$, write $`G_K` for its absolute Galois group and
$`\mathcal O_{\overline K}^{\triangleright}` for the commutative
multiplicative monoid of nonzero elements of the valuation ring of
$`\overline K`.  The natural action gives a group--monoid pair
$$`G_K \curvearrowright \mathcal O_{\overline K}^{\triangleright}.`

In Hoshi's terminology this is a model $`\mathrm{MLF}^{\triangleright}`-pair.
An isomorphism of such pairs consists of an isomorphism of the Galois groups
and an equivariant isomorphism of the monoids.
:::

:::theorem "local_reciprocity_input" (parent := "integral_mono_anabelian") (lean := "Anabelian.LCFT.localReciprocityFamily_exists, Anabelian.LCFT.localReciprocityFamily_unique")
%%%
source := {
  document := "hoshi"
  spans := #[
    {
      page := "15--16"
      text := some {
        path := "source/hoshi.txt"
        startLine := 618
        endLine := 699
      }
      pdf := some {
        path := "source/hoshi.pdf"
        image := "source/hoshi-page-13.png"
      }
    }
  ]
}
%%%

Local reciprocity embeds $`K^\times` into $`G_K^{\mathrm{ab}}`, identifies
$`\mathcal O_K^\times` with inertia, sends a uniformizer to arithmetic
Frobenius modulo inertia, and is compatible with norm and transfer along
finite extensions.  We use existence and uniqueness of this compatible family
as the admitted local-class-field-theory input.
:::

:::theorem "integral_mono_reconstruction" (parent := "integral_mono_anabelian") (lean := "Anabelian.LCFT.monoAnabelianReconstructionPackage_exists")
%%%
source := {
  document := "hoshi"
  spans := #[
    {
      page := "26"
      text := some {
        path := "source/hoshi.txt"
        startLine := 1233
        endLine := 1261
      }
      pdf := some {
        path := "source/hoshi.pdf"
        image := "source/hoshi-page-23.png"
      }
    }
  ]
}
%%%

From an abstract group $`G` of mixed-characteristic-local-field type, there is
a functorial group-theoretic construction of a $`G`-monoid
$`\mathcal O^{\triangleright}(G)`.  For $`G = G_K`, this reconstructed monoid
corresponds to $`\mathcal O_{\overline K}^{\triangleright}`.
:::

:::proof "integral_mono_reconstruction" (uses := "local_reciprocity_input")
Apply local reciprocity to every open subgroup $`H \leq G`.  It identifies the
multiplicative group of the corresponding finite extension with a
group-theoretically specified submonoid of $`H^{\mathrm{ab}}`.  Transfer maps
give the transition maps as $`H` varies.  Passing to the filtered colimit
reconstructs the multiplicative monoid in the algebraic closure, including its
$`G`-action.  Because all ingredients use only the group, its open subgroups,
abelianization, Frobenius, and transfer, a group isomorphism $`\alpha : G_0
\simeq G_1` induces an equivariant monoid isomorphism
$$`\mathcal O^{\triangleright}(\alpha) :
\mathcal O^{\triangleright}(G_0) \simeq
\mathcal O^{\triangleright}(G_1).`
:::

:::theorem "integral_kummer_comparison" (parent := "integral_mono_anabelian") (lean := "Anabelian.LCFT.IntegralReconstruction.comparison_natural")
%%%
source := {
  document := "hoshi"
  spans := #[
    {
      page := "38"
      text := some {
        path := "source/hoshi.txt"
        startLine := 1885
        endLine := 1932
      }
      pdf := some {
        path := "source/hoshi.pdf"
        image := "source/hoshi-page-35.png"
      }
    }
  ]
}
%%%

For an integral Galois pair $`G \curvearrowright M`, the Kummer comparison is
a $`G`-equivariant isomorphism
$$`\kappa_{G,M} : M \simeq \mathcal O^{\triangleright}(G).`
For the integral monoid the ambiguity group $`\mathrm{Ind}^{\triangleright}` is
trivial, so this comparison is unique and natural in isomorphisms of pairs.
:::

:::proof "integral_kummer_comparison" (uses := "integral_mono_reconstruction, local_reciprocity_input")
Kummer theory injects $`M` into a cohomological object formed from its Tate
module.  Cyclotomic synchronization compares this Tate module with the one
reconstructed from $`G`; restricting the induced cohomological comparison gives
$`\kappa_{G,M}`.  Naturality of Kummer theory and synchronization makes the
comparison square commute for every isomorphism of pairs.  In the integral
case the index group has one element, so the poly-isomorphism consists of a
single canonical comparison.
:::

:::theorem "integral_forget_full" (parent := "integral_mono_anabelian") (lean := "Anabelian.OTriangle.LocalGaloisMonoid.forgetGaloisGroup_full") (priority := "high") (effort := "medium")
%%%
source := {
  document := "hoshi"
  spans := #[
    {
      page := "39"
      text := some {
        path := "source/hoshi.txt"
        startLine := 1936
        endLine := 1973
      }
      pdf := some {
        path := "source/hoshi.pdf"
        image := "source/hoshi-page-36.png"
      }
    }
  ]
}
%%%

Every isomorphism $`\alpha : G_0 \simeq G_1` of the étale-like portions of two
integral Galois pairs lifts to an isomorphism of the pairs.  Categorically, the
forgetful functor from integral Galois pairs to their Galois groups is full.
:::

:::proof "integral_forget_full" (uses := "integral_mono_reconstruction, integral_kummer_comparison")
Let $`\iota_i : M_i \simeq \mathcal O^{\triangleright}(G_i)` be the canonical
Kummer comparisons.  Functorial reconstruction supplies
$`\mathcal O^{\triangleright}(\alpha)`.  The required Frobenius-like component
is the composite
$$`M_0 \xrightarrow{\iota_0}
\mathcal O^{\triangleright}(G_0)
\xrightarrow{\mathcal O^{\triangleright}(\alpha)}
\mathcal O^{\triangleright}(G_1)
\xrightarrow{\iota_1^{-1}} M_1.`
Each arrow is equivariant, so this composite together with $`\alpha` is an
isomorphism of pairs whose image under the forgetful functor is $`\alpha`.
:::

:::theorem "integral_forget_faithful" (parent := "integral_mono_anabelian") (lean := "Anabelian.OTriangle.LocalGaloisMonoid.forgetGaloisGroup_faithful") (priority := "high") (effort := "small")
%%%
source := {
  document := "hoshi"
  spans := #[
    {
      page := "39--40"
      text := some {
        path := "source/hoshi.txt"
        startLine := 1974
        endLine := 2007
      }
      pdf := some {
        path := "source/hoshi.pdf"
        image := "source/hoshi-page-37.png"
      }
    }
  ]
}
%%%

Two isomorphisms of integral Galois pairs with the same Galois-group component
are equal.  Categorically, the forgetful functor is faithful.
:::

:::proof "integral_forget_faithful" (uses := "integral_kummer_comparison")
Naturality of the unique Kummer comparisons says that the Frobenius-like
component of a pair isomorphism becomes the functorially reconstructed map
after conjugating by $`\iota_0` and $`\iota_1`.  Hence two pair isomorphisms
with the same group component become the same map between reconstructed
monoids.  Canceling the comparison isomorphisms shows that their monoid
components coincide, and therefore the pair isomorphisms coincide.  This is
the singleton-fiber assertion in Hoshi's Theorem 7.6(iv).
:::

:::theorem "integral_forget_ess_surjective" (parent := "integral_mono_anabelian") (lean := "Anabelian.OTriangle.LocalGaloisMonoid.forgetGaloisGroup_essSurj")
The forgetful functor is essentially surjective because both categories are
presented by pointed mixed-characteristic local fields: a group presented by
$`K` is the image of the integral pair presented by the same $`K`.
:::

:::corollary "integral_forget_equivalence" (parent := "integral_mono_anabelian") (uses := "integral_forget_full, integral_forget_faithful, integral_forget_ess_surjective") (lean := "Anabelian.OTriangle.LocalGaloisMonoid.forgetGaloisGroupEquivalence")
Fullness, faithfulness, and essential surjectivity exhibit the forgetful
functor as an equivalence of the corresponding groupoids.
:::
