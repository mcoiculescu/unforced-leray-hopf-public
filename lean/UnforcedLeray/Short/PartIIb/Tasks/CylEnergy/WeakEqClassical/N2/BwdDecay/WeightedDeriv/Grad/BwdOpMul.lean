import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2_1
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.LapPMul

/-!


Source: `the November 2 reference manuscript` lines 2100-2105.
The time derivative satisfies the ordinary product rule (`HasDerivAt.mul`); the spatial part is
the product rule for `pd` (`lapPMul_pd_mul`) together with the Laplacian of a product (`lapPMul`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb

theorem bwdOpMul : UnforcedLeray.Short.IIb.BwdOpMul := by
  intro ν b0 b1 U W r x FU FW hU hW hUa hWa
  obtain ⟨DU, hDU, eU⟩ := hUa
  obtain ⟨DW, hDW, eW⟩ := hWa
  have hUd : Differentiable ℝ (U r) := hU.differentiable (by norm_num)
  have hWd : Differentiable ℝ (W r) := hW.differentiable (by norm_num)
  refine ⟨U r x * DW + W r x * DU, ?_, ?_⟩
  · exact (hDU.mul hDW).congr_deriv (by ring)
  · show (U r x * DW + W r x * DU) + ν * lapP (fun y => U r y * W r y) x +
        (b0 r x * B0579.pd 0 (fun y => U r y * W r y) x +
          b1 r x * B0579.pd 1 (fun y => U r y * W r y) x) =
      U r x * FW + W r x * FU +
        2 * ν * (B0579.pd 0 (U r) x * B0579.pd 0 (W r) x +
          B0579.pd 1 (U r) x * B0579.pd 1 (W r) x)
    rw [lapPMul (U r) (W r) x hU hW, lapPMul_pd_mul 0 (U r) (W r) x (hUd x) (hWd x),
      lapPMul_pd_mul 1 (U r) (W r) x (hUd x) (hWd x)]
    linear_combination (U r x) * eW + (W r x) * eU

end UnforcedLeray.Short.IIb
