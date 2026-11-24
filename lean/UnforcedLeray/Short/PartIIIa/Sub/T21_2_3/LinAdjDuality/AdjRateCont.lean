import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjRateCont.Loc
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjRateCont.Glob

/-!
# Part III-a: continuity of the adjoint pairing in the age (`adjWRateCont`)

Source of record: `the November 2 reference manuscript` lines 3052-3058, 2854-2865.
The band part is continuous by joint continuity on a compact strip (`adjLocContinuous`), the global
part `∫ φ(r) uψ·∇E(r)` by `X_{-m}`-continuity of `φ` and dominated convergence (`adjGlobContinuous`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- **Leaf 1** (SP 3052-3058, 2854-2865): `r ↦ ∫_cell adjIntegrand tr (φ r) r ψ uψ` is continuous
on `(t, s)`. -/
theorem adjWRateCont (m : ℝ) : UnforcedLeray.Short.IIIa.AdjWRateCont m :=
  adjWRateCont_of_glob m (adjGlobContinuous m)

end UnforcedLeray.Short.IIIa
