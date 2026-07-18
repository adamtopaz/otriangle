import Verso
import VersoManual
import VersoBlueprint
import Otriangle.MonoAnabelian.Interface
import Otriangle.MonoAnabelian.OneField
import Otriangle.MonoAnabelian.TransferSystem
import Otriangle.MonoAnabelian.DirectLimit
import Otriangle.MonoAnabelian.FiniteExtensionSystem
import Otriangle.MonoAnabelian.OpenSubgroups
import Otriangle.MonoAnabelian.FixedFields
import Otriangle.MonoAnabelian.FieldColimit
import Otriangle.MonoAnabelian.SpectralLocalField
import Otriangle.MonoAnabelian.FixedFieldLocal

set_option linter.hashCommand false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "One-field and direct-limit reconstruction" =>

:::theorem "one_field_multiplicative_reconstruction" (parent := "integral_mono_anabelian") (lean := "Anabelian.LCFT.LocalReciprocityMap.injective, Anabelian.LCFT.LocalReciprocityFamily.baseIntegerMonoidEquiv")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "21--22"
    text := some { path := "source/hoshi.txt", startLine := 950, endLine := 1043 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-19.png" }
  }]
}
%%%

For a group $`G` of local-field type, the image of inertia in
$`G^{\mathrm{ab}}` reconstructs the unit group.  The inverse images of
$`\operatorname{Frob}(G)^{\mathbb Z}` and
$`\operatorname{Frob}(G)^{\mathbb N}` reconstruct the multiplicative group
and the monoid of nonzero integers.  Local reciprocity identifies these with
$`\mathcal O_K^\times`, $`K^\times`, and
$`\mathcal O_K^{\triangleright}` for $`G=G_K`.
:::

:::proof "one_field_multiplicative_reconstruction" (uses := "local_reciprocity_input, group_theoretic_local_invariants")
The units and Frobenius conditions identify the valuation exact sequence
$$`1\to\mathcal O_K^\times\to K^\times\to\mathbb Z\to0`
with the corresponding sequence in $`G_K^{\mathrm{ab}}`.  Injectivity follows
because reciprocity is injective on units and nonzero Frobenius powers have
infinite order in the unramified quotient.  Nonnegative valuation is precisely
the inverse image of the Frobenius submonoid.  Thus restriction of reciprocity
gives the asserted monoid equivalence, and the intrinsic definitions make it
functorial under group isomorphisms.
:::

:::theorem "transfer_direct_system" (parent := "integral_mono_anabelian") (lean := "Anabelian.LCFT.LocalReciprocityFamily.reconstructedBaseIntegerMonoidMap, Anabelian.LCFT.LocalReciprocityFamily.baseIntegerMonoidEquiv_natural, Anabelian.LCFT.FiniteExtensionSystem.reconstructedDirectedSystem, Anabelian.OTriangle.LocalGaloisGroup.openSubgroupIndexEquiv, Anabelian.OTriangle.LocalGaloisGroup.fixedField_finiteDimensional, Anabelian.OTriangle.LocalGaloisGroup.fixedFieldGaloisEquiv, Anabelian.OTriangle.SpectralLocalField.isNonarchimedeanLocalField, Anabelian.OTriangle.LocalGaloisGroup.fixedFieldIsNonarchimedeanLocalField, Anabelian.OTriangle.LocalGaloisGroup.fixedFieldValuativeExtension, Anabelian.OTriangle.LocalGaloisGroup.fixedFieldIsAlgClosure")
%%%
source := {
  document := "hoshi"
  spans := #[
    {
      page := "16"
      text := some { path := "source/hoshi.txt", startLine := 664, endLine := 699 }
      pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-13.png" }
    },
    {
      page := "25"
      text := some { path := "source/hoshi.txt", startLine := 1151, endLine := 1188 }
      pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-22.png" }
    }
  ]
}
%%%

As $`H` ranges over open subgroups of $`G`, transfer carries the one-field
reconstructed monoids covariantly from smaller finite extensions to larger
ones.  The open subgroup's fixed field is finite over the base field, and its
absolute Galois group in the chosen algebraic closure is identified with that
open subgroup.  These injective transition maps form a directed system,
functorial in isomorphisms of $`G`.
:::

:::proof "transfer_direct_system" (uses := "local_reciprocity_input, one_field_multiplicative_reconstruction")
For $`H'\subseteq H`, Hoshi's transfer square identifies
$`H^{\mathrm{ab}}\to H'^{\mathrm{ab}}` with inclusion of the corresponding
finite extensions' multiplicative groups.  It therefore preserves their
nonnegative-valuation submonoids.  The identity and composition laws for field
inclusions transport through the nodewise reciprocity equivalences to give the
direct-system laws; naturality under group isomorphisms supplies functoriality.

Formally, a finite fixed field is equipped with the spectral norm over the
presented local field.  The spectral norm is nonarchimedean, its norm topology
is its valuative topology, and finite-dimensionality makes it locally compact.
The tower identity for spectral norms proves compatibility with the spectral
valuation on the common algebraic closure.  Thus the fixed field is genuinely
a finite valued local extension with that common algebraic closure, rather than
this arithmetic fact being added as an assumption on the diagram.
:::

:::theorem "filtered_colimit_comparison" (parent := "integral_mono_anabelian") (lean := "Anabelian.LCFT.FilteredColimit.mapMonoidHom, Anabelian.LCFT.FilteredColimit.mapMonoidHomAlong, Anabelian.LCFT.FilteredColimit.mulEquiv, Anabelian.LCFT.FilteredColimit.mulEquivAlongOrderIso, Anabelian.LCFT.FiniteExtensionSystem.directLimitEquiv, Anabelian.OTriangle.LocalGaloisGroup.exists_mem_fixedField, Anabelian.OTriangle.LocalGaloisGroup.fixedFieldDirectLimitEquiv")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "25--26"
    text := some { path := "source/hoshi.txt", startLine := 1151, endLine := 1235 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-22.png" }
  }]
}
%%%

A natural family of homomorphisms between two filtered systems of monoids,
possibly over different monotonically related index types, induces a
homomorphism between their direct limits.  If the indices are order-isomorphic
and every component is a multiplicative equivalence, then the induced map of
direct limits is a multiplicative equivalence.  On the field side, the fixed
fields of open subgroups cover the algebraic closure.  Consequently, the
direct limit of their nonzero integral monoids is multiplicatively equivalent
to $`\mathcal O_{\overline K}^{\triangleright}`.
:::

:::proof "filtered_colimit_comparison" (uses := "transfer_direct_system")
Mathlib's `DirectLimit.map` descends the component maps through the quotient
relation by their naturality squares.  Preservation of the unit and product is
proved on representatives.  Applying the same construction to the inverse
component equivalences gives an inverse map; the two inverse laws again reduce
to the corresponding laws on representatives.  For the field-side system,
every integral element lies in some finite fixed field, which proves
surjectivity of the canonical colimit map; injectivity follows from the
injectivity of fixed-field inclusions after moving two representatives to a
common index.
:::

:::theorem "integral_mono_reconstruction" (parent := "integral_mono_anabelian") (lean := "Anabelian.LCFT.IntegralMonoAnabelianAlgorithm")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "26"
    text := some { path := "source/hoshi.txt", startLine := 1233, endLine := 1261 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-23.png" }
  }]
}
%%%

From an abstract group $`G` of mixed-characteristic-local-field type, one
constructs functorially a $`G`-monoid
$`\mathcal O^{\triangleright}(G)` corresponding, for $`G=G_K`, to
$`\mathcal O_{\overline K}^{\triangleright}`.
:::

:::proof "integral_mono_reconstruction" (uses := "one_field_multiplicative_reconstruction, transfer_direct_system, filtered_colimit_comparison")
Apply one-field reconstruction to every open subgroup $`H\leq G`.  Transfer
gives the transition maps.  Their filtered colimit reconstructs the integral
multiplicative monoid in the algebraic closure, and conjugation of open
subgroups supplies its $`G`-action.  An isomorphism $`\alpha:G_0\simeq G_1`
maps the entire indexed diagram to the corresponding diagram for $`G_1`, so
it induces an equivariant monoid equivalence.  Identity and composition laws
hold because this construction is induced functorially on the diagrams.

The Lean structure `Anabelian.LCFT.IntegralMonoAnabelianAlgorithm` records
exactly these outputs and laws; the implementation is split into one-field,
transfer, and filtered-colimit modules.
:::
