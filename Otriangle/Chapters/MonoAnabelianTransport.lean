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

#doc (Manual) "Mono-anabelian transport" =>

:::theorem "integral_forget_full" (parent := "integral_mono_anabelian") (lean := "Anabelian.OTriangle.LocalGaloisMonoid.forgetGaloisGroup_full") (priority := "high")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "39"
    text := some { path := "source/hoshi.txt", startLine := 1936, endLine := 1973 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-36.png" }
  }]
}
%%%

Every isomorphism $`\alpha:G_0\simeq G_1` of the étale-like portions of two
integral Galois pairs lifts to an isomorphism of the pairs.  Categorically, the
forgetful functor is full.
:::

:::proof "integral_forget_full" (uses := "reconstruction_package")
Let $`\iota_i:M_i\simeq\mathcal O^{\triangleright}(G_i)` be the canonical
comparisons.  The monoid component of the lift is
$$`M_0\xrightarrow{\iota_0}\mathcal O^{\triangleright}(G_0)
\xrightarrow{\mathcal O^{\triangleright}(\alpha)}
\mathcal O^{\triangleright}(G_1)\xrightarrow{\iota_1^{-1}}M_1.`
All three arrows are equivariant, so the composite with $`\alpha` is an
isomorphism of pairs.  This composite is implemented by
`Anabelian.LCFT.IntegralReconstruction.lift`.
:::

:::theorem "integral_forget_faithful" (parent := "integral_mono_anabelian") (lean := "Anabelian.OTriangle.LocalGaloisMonoid.forgetGaloisGroup_faithful") (priority := "high")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "39--40"
    text := some { path := "source/hoshi.txt", startLine := 1974, endLine := 2007 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-37.png" }
  }]
}
%%%

Two isomorphisms of integral Galois pairs with the same Galois-group component
are equal.  Categorically, the forgetful functor is faithful.
:::

:::proof "integral_forget_faithful" (uses := "integral_kummer_comparison")
Naturality says that conjugating either monoid component by the canonical
comparisons yields the functorially reconstructed map of its group component.
Equal group components therefore give equal conjugates.  Canceling the two
comparison isomorphisms gives equal monoid components and hence equal pair
isomorphisms.  Lean implements the cancellation in
`Anabelian.LCFT.IntegralReconstruction.hom_ext`.
:::

:::theorem "integral_forget_ess_surjective" (parent := "integral_mono_anabelian") (lean := "Anabelian.OTriangle.LocalGaloisMonoid.forgetGaloisGroup_essSurj")
The forgetful functor is essentially surjective because both categories are
presented by pointed mixed-characteristic local fields: the group presented
by $`K` is the image of the integral pair presented by that same $`K`.
:::

:::corollary "integral_forget_equivalence" (parent := "integral_mono_anabelian") (uses := "integral_forget_full, integral_forget_faithful, integral_forget_ess_surjective") (lean := "Anabelian.OTriangle.LocalGaloisMonoid.forgetGaloisGroupEquivalence")
Fullness, faithfulness, and essential surjectivity exhibit the forgetful
functor as an equivalence of groupoids.
:::
