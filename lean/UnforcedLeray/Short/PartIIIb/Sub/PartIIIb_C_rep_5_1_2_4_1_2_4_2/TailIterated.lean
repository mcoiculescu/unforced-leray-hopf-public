import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_2_4_2
import UnforcedLeray.Short.PartIIIa.T14_HeatGBound
import UnforcedLeray.Lib.Kernels.HeatTimePotential

/-!
# `PartIII-b:C/rep/5/1/2/4/1/2/4/2/1`: `TailIterated` for `t > 0`

Proves `tailIterated : TailIterated` (source 3600-3610). For `t > 0` the tail `heatTail t` is the
library time potential `Kernels.heatTimePotential t` (`heatG a = Heat.kernel a`, T14), which is
smooth on all of `Space` when `t > 0` and whose iterated derivatives are the integrals of the
iterated derivatives of the heat kernel (library `Kernels.iteratedFDeriv_heatTimePotential`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.KPH

open UnforcedLeray.Short.IIIa

theorem heatTail_eq_potential_KPH (t : ℝ) : heatTail t = Kernels.heatTimePotential t := by
  funext x
  unfold heatTail Kernels.heatTimePotential
  simp only [heatG_eq_heatKernel]

theorem tailIterated : UnforcedLeray.Short.PartIIIb.Concrete.KPH.TailIterated := by
  unfold TailIterated
  intro t ht
  refine ⟨?_, ?_⟩
  · rw [heatTail_eq_potential_KPH, contDiff_iff_contDiffAt]
    intro x
    exact Kernels.contDiffAt_heatTimePotential ht.le (Or.inr ht)
  · intro n x
    rw [heatTail_eq_potential_KPH, Kernels.iteratedFDeriv_heatTimePotential n ht.le (Or.inr ht)]
    simp only [heatG_eq_heatKernel]

end UnforcedLeray.Short.PartIIIb.Concrete.KPH
