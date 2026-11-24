import UnforcedLeray.Short.PartIIIa.Targets
import UnforcedLeray.Lib.Kernels.GaussDeriv

/-!
# Part III-a: derivative bounds of the heat kernel (SP 3604-3606)

Proves `heatGBound : HeatGBound` (`Targets.lean`, task PartIII-a:T14). For each `m : ℕ` there is
`C ≥ 0` with `‖D^m G_a(x)‖ ≤ C a^{-(3+m)/2} e^{-‖x‖²/(8a)}` for all `a > 0` and `x`, where
`G_a = heatG a` is the three-dimensional heat kernel of `SeparatedKernels.lean`.

1. `heatG a` is the audited heat kernel `UnforcedLeray.Heat.kernel a`
   (`Analysis/Heat/KernelNorm.lean`, `kernel_formula`): both equal
   `(4πa)^{-3/2} exp(-‖x‖²/(4a))`.
2. The audited Gaussian majorant `UnforcedLeray.Kernels.norm_iteratedFDeriv_heatKernel_le`
   (`Lib/Kernels/GaussDeriv.lean`) gives the bound with constant `heatDerivConst m ≥ 0` and
   exponent `-((3+m)/2)`. The target writes the exponent as `-(3+m)/2`, a ring identity.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- The heat kernel `heatG a` agrees with the audited kernel `UnforcedLeray.Heat.kernel a`
for `a > 0` (both are `(4πa)^{-3/2} exp(-‖x‖²/(4a))`). -/
theorem heatG_eq_heatKernel {a : ℝ} : heatG a = UnforcedLeray.Heat.kernel a := by
  funext x
  rw [UnforcedLeray.Heat.kernel_formula]
  unfold heatG
  have e : -‖x‖ ^ 2 / (4 * a) = -(4 * a)⁻¹ * ‖x‖ ^ 2 := by ring
  rw [e]

theorem heatGBound : HeatGBound := by
  unfold HeatGBound
  intro m
  refine ⟨UnforcedLeray.Kernels.heatDerivConst m,
    (UnforcedLeray.Kernels.heatDerivConst_pos m).le, ?_⟩
  intro a ha x
  rw [heatG_eq_heatKernel, show (-(3 + (m : ℝ)) / 2) = -((3 + (m : ℝ)) / 2) by ring]
  exact UnforcedLeray.Kernels.norm_iteratedFDeriv_heatKernel_le m ha x

end UnforcedLeray.Short.IIIa
