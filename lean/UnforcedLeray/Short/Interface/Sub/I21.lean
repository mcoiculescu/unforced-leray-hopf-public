import UnforcedLeray.Short.Interface.WindowSteps

/-!
# Interface leaf 4b (`WindowsToGlobalLaplacian`): conditional assembly

Source of record: `the November 2 reference manuscript` (the shorter proof does not
state the window argument; the old manuscript lines 7519-7536 are used, only existence of the
Laplacian in `𝒴₂` is needed). The passage from the fixed-window Laplacian estimate
(`FreeWindowRegularity`) to the global `𝒴₂` Laplacian (`FreeLaplacianRegularity`) is two steps:

* `WindowGlueLocal` (task `Interface:I19`, `Leaf4b_Glue.lean`): window Laplacians on the windows
  `(n-1, n+1) × ℝ³`, `n ∈ ℤ`, glue to one locally `L²` weak Laplacian `L` of `w`;
* `PeriodicSelection` (task `Interface:I20`, `Leaf4b_Periodic.lean`): a locally `L²` weak
  Laplacian of a `𝒯`-periodic `𝒴₂` field is re-chosen `𝒯`-periodic, hence in `𝒴₂`.

`windowsToGlobalLaplacian_of` assembles `WindowsToGlobalLaplacian` from them. The unconditional
`windowsToGlobalLaplacian` is the task `Interface:I21` (`Short/Interface/Leaf4b.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Cons.C08

/-- `WindowsToGlobalLaplacian` from the gluing step `WindowGlueLocal` and the periodic selection
`PeriodicSelection`. -/
theorem windowsToGlobalLaplacian_of (hglue : WindowGlueLocal) (hper : PeriodicSelection) :
    WindowsToGlobalLaplacian := by
  intro hwin h P μ w g hh hP _hμ hw hg hsol
  have hwY : B0005.IsY2 P w := ⟨hw.value.periodic, hw.value.measurable, hw.value.memL2⟩
  choose Λ hΛ using fun n : ℤ => hwin h μ P w g hh hP hwY hg hsol (n : ℝ)
  obtain ⟨L, hLm, hLL2, hLweak⟩ := hglue w Λ hΛ
  exact hper P w L hP hwY hLm hLL2 hLweak

end UnforcedLeray.Short.Interface
