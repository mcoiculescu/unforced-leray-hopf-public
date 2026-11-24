import UnforcedLeray.Short.PartIIb.Defs

/-!
# Scalar-test version of `IsPlanarSolTest` (leaf `PartII-b:T13/1/2`)

The proof of the causal Duhamel equation (`Sub/T12_7.lean` and `Tasks/FlatCausal/DuhamelEquation/**`)
uses only the smoothness field of `IsPlanarSolTest`, never `div_free`. The renamed copies in this
folder (prefix `dfe_`) are stated for `IsPlanarTestDfe`, which keeps only that field.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- Planar test fields in `s > 0`, with no divergence condition (SP 1923-1927). -/
structure IsPlanarTestDfe (Ψ : Coord → Fin 2 → ℝ) : Prop where
  smooth : ∀ i, IsCoordTest (fun x => Ψ x i)

end UnforcedLeray.Short.IIb

end
