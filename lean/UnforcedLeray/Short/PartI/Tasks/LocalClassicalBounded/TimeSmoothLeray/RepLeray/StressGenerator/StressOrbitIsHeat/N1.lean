import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.StressGenerator.StressOrbitIsHeat.Needed
import UnforcedLeray.Lib.TrainB.P0GaussianTensorIBP

/-!
# N1: smooth Gaussian integration by parts for one scalar pair

Proof of `NeedSmoothRowIBP` from `Needed.lean`. The library theorem
`UnforcedLeray.TrainB.integral_gradKernel_row_eq_integral_kernel_rowDiv`
(`Lib/TrainB/P0GaussianTensorIBP.lean`) already takes `ContDiff ℝ ∞` fields with bounded values
and bounded first derivatives, which is exactly the hypothesis set of `NeedSmoothRowIBP`, so this
is a direct application. (The probe note in `Needed.lean` that the library requires `ContDiff ℝ ⊤`
is out of date: the library file uses `ContDiff ℝ ∞`.)
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartI

theorem needSmoothRowIBP : NeedSmoothRowIBP := by
  intro θ hθ f g hf hg hfB hgB hfD hgD z
  exact UnforcedLeray.TrainB.integral_gradKernel_row_eq_integral_kernel_rowDiv hθ hf hg
    hfB hgB hfD hgD z

end UnforcedLeray.Short.PartI
