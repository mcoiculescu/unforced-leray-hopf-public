import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c1_b_4

/-!
# Part III-a, task `PartIII-a:T21/c1/b/4`: the uniform dual bound `PerLam0Bound`

Source of record: `the November 2 reference manuscript`, lines 2894-2897.

`PerLam0Bound κ` (in `Sub/PartIII-a_T21_c1_b.lean`) carries the measurability hypothesis
`AEStronglyMeasurable W (volume.restrict (B0579.cell d))`. Its body is definitionally the same as
`Lam0B.PerLam0BoundM κ` (in `Sub/PartIII-a_T21_c1_b_4.lean`), which is proved there as
`Lam0B.perLam0BoundM`. Hence the leaf is discharged by that proof.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- Leaf 4 (SP 2894-2897): the uniform dual bound of the periodized rows, for a.e.-strongly
measurable inputs. -/
theorem perLam0Bound (κ : PlanarFrameKernels) : PerLam0Bound κ := by
  unfold PerLam0Bound
  exact Lam0B.perLam0BoundM κ

end UnforcedLeray.Short.IIIa
