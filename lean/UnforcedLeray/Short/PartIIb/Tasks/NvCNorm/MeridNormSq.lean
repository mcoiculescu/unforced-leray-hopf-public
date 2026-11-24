import UnforcedLeray.Short.PartIIb.Sub.T07

/-!
# Part II-b, task `PartII-b:NvCNorm/MeridNormSq`: the meridional norm identity

Source of record: `the November 2 reference manuscript`, lines 1902-1906
(step 2 of the complex lift norm identity). For `v ∈ ℂ²` (`CMerid`),
`‖v‖² = ‖Re v‖² + ‖Im v‖²`, where `reM v` and `imM v` are the coordinatewise real and imaginary
parts (`Short/PartII-b/Defs.lean`).

Proof: expand the three Euclidean norms with `EuclideanSpace.norm_sq_eq` and sum over `Fin 2`,
then per coordinate use `Complex.sq_norm`, `Complex.normSq_apply` and `Real.norm_eq_abs`,
`sq_abs`, and close by `ring`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- SP 1902-1906, step 2: `‖v‖² = ‖Re v‖² + ‖Im v‖²` for `v ∈ ℂ²`. -/
theorem cMeridNormSq : UnforcedLeray.Short.IIb.CMeridNormSq := by
  intro v
  simp only [EuclideanSpace.norm_sq_eq, reM, imM, Fin.sum_univ_two,
    Complex.sq_norm, Complex.normSq_apply, Real.norm_eq_abs, sq_abs]
  ring

end UnforcedLeray.Short.IIb
