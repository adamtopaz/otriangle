import Verso
import VersoManual
import VersoBlueprint
import Otriangle.MonoAnabelian.Package
import Otriangle.MonoAnabelian.KummerComparison

set_option linter.hashCommand false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Cyclotomic synchronization and Kummer comparison" =>

:::theorem "canonical_fixed_field_comparison" (parent := "integral_mono_anabelian") (uses := "integral_mono_reconstruction") (lean := "Anabelian.OTriangle.LocalGaloisGroup.reconstructedIntegralMonoidComparison, Anabelian.OTriangle.LocalGaloisGroup.reconstructedIntegralMonoidComparison_action")
For every presented group $`G_K`, the field-side fixed-field colimit is
canonically equivalent to $`\mathcal O_{\overline K}^{\triangleright}`.
Composing its inverse with the nodewise reciprocity equivalences gives an
equivariant comparison
$$`\mathcal O_{\overline K}^{\triangleright}\simeq
\mathcal O^{\triangleright}(G_K).`
This constructs the objectwise comparison required by Kummer theory; the
remaining issue is its naturality for arbitrary isomorphisms of integral
Galois pairs.
:::

:::proof "canonical_fixed_field_comparison" (uses := "integral_mono_reconstruction")
Every algebraic integer lies in the fixed field of an open subgroup.  The
field-side colimit comparison is therefore bijective.  At each node local
reciprocity identifies the nonzero integer monoid with the reconstructed
Frobenius-positive cone, and transfer naturality makes these node maps descend
to the colimit.  Conjugation of fixed fields commutes with both colimit maps,
which proves equivariance of the resulting comparison.
:::

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

:::theorem "integral_valuation_rigidity" (parent := "integral_mono_anabelian") (uses := "kummer_restriction") (lean := "Anabelian.LCFT.isUnit_baseIntegerMonoid_iff, Anabelian.LCFT.baseIntegerMonoidEquiv_fieldUnitDiscreteValuation")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "37--38"
    text := some { path := "source/hoshi.txt", startLine := 1859, endLine := 1932 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-35.png" }
  }]
}
%%%

Every multiplicative automorphism of the nonzero integral monoid
$`\mathcal O_K^{\triangleright}` preserves the normalized discrete
valuation.  Thus the possible integral ambiguity has no component in the
free valuation direction.
:::

:::proof "integral_valuation_rigidity" (uses := "kummer_restriction")
The invertible elements of $`\mathcal O_K^{\triangleright}` are exactly
$`\mathcal O_K^\times`; this characterization uses only the monoid.  After
quotienting by these units, every element has a unique expression represented
by a nonnegative power of a uniformizer, so the quotient is the free
commutative monoid on one generator.

For a direct formal proof, write the image of a uniformizer as $`\pi^n u`
and the image under the inverse automorphism as $`\pi^m v`, with $`u,v`
units.  Applying the two automorphisms successively and taking discrete
valuations gives $`nm=1`; hence $`n=m=1`.  Decomposing an arbitrary
$`x=\pi^r w` then proves $`v(\alpha(x))=v(x)`.
:::

:::theorem "integral_cyclotomic_rigidity" (parent := "integral_mono_anabelian") (uses := "integral_valuation_rigidity, cyclotomic_synchronization") (lean := "Anabelian.OTriangle.LocalGaloisGroup.restrictCentralIntegerMonoidEquiv, Anabelian.OTriangle.LocalGaloisGroup.restrictCentralIntegerMonoid_fix_primitiveRoot, Anabelian.OTriangle.LocalGaloisGroup.restrictCentralIntegerMonoid_fix_of_pow_eq_one")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "31--38"
    text := some { path := "source/hoshi.txt", startLine := 1519, endLine := 1932 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-35.png" }
  }]
}
%%%

An automorphism of $`\mathcal O_{\overline K}^{\triangleright}` commuting
with $`G_K` fixes every root of unity.  This is the concrete integral form of
the cyclotomic synchronization that removes Hoshi's index ambiguity.
:::

:::proof "integral_cyclotomic_rigidity" (uses := "integral_valuation_rigidity, cyclotomic_synchronization")
Put a primitive $`n`th root $`\zeta` in a finite fixed field $`L`.  Choose a
uniformizer $`\pi_L` and a Kummer root $`\beta^n=\pi_L` in the algebraic
closure.  If the central automorphism sends $`\zeta` to $`\zeta^a`, then
equivariance shows that
$$`
  c=\frac{\alpha(\beta)}{\beta^a}
`
is fixed by $`G_L`, hence belongs to $`L^\times`.  Raising to the $`n`th
power gives
$$`
  \alpha(\pi_L)=c^n\pi_L^a.
`
The valuation-rigidity theorem makes the two sides have the same normalized
valuation, so $`a\equiv1\pmod n`.  Since $`0\le a<n`, one has $`a=1`.
Every torsion element is primitive of its exact order, so all roots of unity
are fixed.
:::

:::theorem "integral_centralizer_rigidity" (parent := "integral_mono_anabelian") (uses := "integral_cyclotomic_rigidity, kummer_restriction") (lean := "Anabelian.LCFT.eq_one_of_forall_exists_pow_eq, Anabelian.OTriangle.LocalGaloisGroup.centralIntegerMonoidEquiv_eq_refl")
%%%
source := {
  document := "hoshi"
  spans := #[{
    page := "37--38"
    text := some { path := "source/hoshi.txt", startLine := 1859, endLine := 1932 }
    pdf := some { path := "source/hoshi.pdf", image := "source/hoshi-page-35.png" }
  }]
}
%%%

The centralizer of the $`G_K`-action in
$`\operatorname{Aut}(\mathcal O_{\overline K}^{\triangleright})` is
trivial.  Equivalently, the integral Kummer comparison has no residual
automorphism after cyclotomic synchronization.
:::

:::proof "integral_centralizer_rigidity" (uses := "integral_cyclotomic_rigidity, kummer_restriction")
Let $`\alpha` commute with $`G_K`, and put an arbitrary nonzero algebraic
integer $`x` in a finite fixed field $`L`.  For each $`q>0`, choose
$`y\in\overline K` with $`y^q=x`.  Integrality of $`x` implies integrality
of $`y`.  For $`\sigma\in G_L`, the ratio
$`r_\sigma=\sigma(y)/y` is a $`q`th root of unity, so cyclotomic rigidity
fixes it.  Equivariance therefore gives
$$`
  \sigma\!\left(\frac{\alpha(y)}y\right)
  =\frac{\alpha(y)}y,
`
and the ratio belongs to $`L^\times`.  Its $`q`th power is
$`\alpha(x)/x`.  Hence $`\alpha(x)/x` is divisible by every positive
integer in $`L^\times`.

There are no nontrivial infinitely divisible elements in a local
multiplicative group.  Arbitrarily deep residue-characteristic power
factorizations first force such an element into the finite torsion subgroup;
taking a root whose exponent is the cardinality of that subgroup then forces
the element to be one.  Thus $`\alpha(x)=x` for every $`x`, and
$`\alpha=1`.
:::

:::theorem "integral_kummer_naturality" (parent := "integral_mono_anabelian") (uses := "canonical_fixed_field_comparison, kummer_restriction, cyclotomic_synchronization, integral_centralizer_rigidity") (lean := "Anabelian.OTriangle.IntegralKummerNaturality, Anabelian.OTriangle.integralKummerNaturality_of_reciprocity")
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

For a morphism $`f:(G_0\curvearrowright M_0)\simeq
(G_1\curvearrowright M_1)`, the canonical objectwise comparisons satisfy
$$`\kappa_0\,\mathcal O^{\triangleright}(f)=f_M\,\kappa_1.`
The Lean proposition `IntegralKummerNaturality` states this square directly
for the fixed-field reconstruction, and
`integralKummerNaturality_of_reciprocity` proves it.
:::

:::proof "integral_kummer_naturality" (uses := "canonical_fixed_field_comparison, kummer_restriction, cyclotomic_synchronization, integral_centralizer_rigidity")
Kummer theory injects $`M` into cohomology formed from its Tate module.
Cyclotomic synchronization compares this with the module reconstructed from
$`G`; restriction gives $`\kappa_{G,M}`.  Naturality of Kummer theory and of
synchronization makes the comparison square commute.  Triviality of the
integral index group turns the poly-isomorphism into one canonical comparison.

Formally, conjugate reconstructed transport by the two canonical fixed-field
comparisons.  This produces an equivariant monoid isomorphism
$`c_f:M_0\simeq M_1`.  The discrepancy
$`\delta=c_f\circ f_M^{-1}` is an automorphism of $`M_0` commuting with its
Galois action.  Integral centralizer rigidity gives $`\delta=1`, hence
$`c_f=f_M`; expanding this equality is precisely the displayed naturality
square.
:::

:::theorem "integral_kummer_comparison" (parent := "integral_mono_anabelian") (uses := "integral_kummer_naturality") (lean := "Anabelian.LCFT.IntegralKummerComparison, Anabelian.OTriangle.integralKummerComparisonOfHoshiComparison, Anabelian.OTriangle.integralReconstructionOfHoshiComparison")
The canonical fixed-field comparisons and their naturality assemble with the
functorial reconstruction algorithm into an `IntegralKummerComparison` and
hence an `IntegralReconstruction`.
:::

:::proof "integral_kummer_comparison" (uses := "integral_kummer_naturality")
Use the canonical fixed-field comparison at every object.  Its established
equivariance supplies `comparison_action`, and the Kummer square supplies
`comparison_natural`.  The Lean constructors perform exactly this assembly;
they retain the ramification-comparison and Kummer-naturality hypotheses
explicitly.
:::

:::theorem "reconstruction_package" (parent := "integral_mono_anabelian") (uses := "integral_mono_reconstruction, integral_kummer_comparison") (lean := "Anabelian.LCFT.monoAnabelianReconstructionPackage_of_reciprocity") (priority := "high")
The algorithm of Summary 4.3 and the natural integral Kummer comparison of
Definition 7.4 together form a `MonoAnabelianReconstructionPackage`.  Thus a
fixed `LocalReciprocityFamily` determines a nonempty type of such packages.
:::

:::proof "reconstruction_package" (uses := "integral_mono_reconstruction, integral_kummer_comparison")
First apply the uniform ramification identification to the fixed-field
transport construction, obtaining the functorial algorithm.  Then apply
integral Kummer naturality to the canonical objectwise comparisons, obtaining
the complete `IntegralReconstruction`.  The formal constructor
`Anabelian.LCFT.monoAnabelianReconstructionPackageOfComparisons` implements
this last assembly.  The theorem
`monoAnabelianReconstructionPackage_of_reciprocity` supplies its two inputs
from local reciprocity: the uniform Hoshi ramification comparison and the
integral Kummer naturality theorem proved above.
:::
