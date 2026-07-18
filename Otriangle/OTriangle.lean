import Otriangle.OTriangle.Core
import Otriangle.LCFT

/-!
# Full faithfulness for the O-triangle forgetful functor

The shared categorical definitions live in `Otriangle.OTriangle.Core`.  This module is kept after
`Otriangle.LCFT` in the import graph so that the full and faithful instances below may use local
class field theory, including the stipulated existence and uniqueness of local reciprocity.
-/

noncomputable section

open CategoryTheory

namespace Anabelian
namespace OTriangle

universe u

namespace LocalGaloisMonoid

open LCFT

/-- Every open embedding of local absolute Galois groups lifts to an equivariant isomorphism of
their integral monoids. -/
noncomputable instance forgetGaloisGroup_full : forgetGaloisGroup.Full := by
  sorry

/-- An equivariant integral-monoid isomorphism is uniquely determined by its underlying open
embedding of local absolute Galois groups. -/
instance forgetGaloisGroup_faithful : forgetGaloisGroup.Faithful := by
  sorry

end LocalGaloisMonoid
end OTriangle
end Anabelian
