import UnforcedLeray.Short.PartIIa.Calc.BlockA2Calc

/-!
# Part II-a, block `A₂`, task `PartII-a:R02/12/1`: `∂_s` is smooth and local

Source: `the November 2 reference manuscript`, lines 397-404 and 437-446.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet.A2

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190

/-- **`∂_s` is smooth and local** (task `PartII-a:R02/12/1`). -/
theorem ageSmoothLocal : UnforcedLeray.Short.PartIIa.Jet.A2.AgeSmoothLocal := by
  refine ⟨fun F hF => ?_, fun F G h => ?_⟩
  · intro ν c hν hc tr htr
    exact UnforcedLeray.Short.PartIIa.contDiffOn_fderiv_apply (hF ν c hν hc tr htr) esDir
  · intro ν c hν hc tr htr x hx
    have hev : F ν c tr =ᶠ[𝓝 x] G ν c tr :=
      Filter.eventuallyEq_of_mem (UnforcedLeray.Short.PartIIa.isOpen_late.mem_nhds hx)
        (fun y hy => h ν c hν hc tr htr hy)
    show partialAge (F ν c tr) x = partialAge (G ν c tr) x
    unfold partialAge
    rw [hev.fderiv_eq]

end UnforcedLeray.Short.PartIIa.Jet.A2
