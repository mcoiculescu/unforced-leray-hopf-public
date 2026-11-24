import UnforcedLeray.Short.PartIIa.Sub.F14_1_org.Defs
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.HeatGaussInitial
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.HeatGaussEquation
import UnforcedLeray.Lib.HeatR3.ConvOp
import UnforcedLeray.Lib.HeatR3.Space

/-!
# Part II-a, task `PartII-a:F14/1/1/4`: the heat factor is an `L²` contraction

Target: `HeatGaussL2` (defined in `Sub/F14_1_org/Defs.lean`).

Source of record: `the November 2 reference manuscript`, lines 1375-1376.

Proof. For `w = 0`, `heatGauss f 0 = f` (`HeatGaussInitial`), so the two norms agree.
For `w ≠ 0`, `heatGauss f w (τ, ·)` is the heat average `Heat.average (w^2)` of the slice
(`heatGauss_eq_average`), which is `heatConv id (w^2)` (`heatConv_space_eq_average`), and the
heat convolution is an `L^2` contraction (`Heat.eLpNorm_heatConv_le`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

namespace UnforcedLeray.Short.PartIIa

theorem heatGaussL2 : HeatGaussL2 := by
  intro P hP f hf w τ
  by_cases hw : w = 0
  · subst hw
    have hfun : (fun z : Space => heatGauss f 0 (τ, z)) = fun z : Space => f (τ, z) :=
      funext fun z => (heatGaussInitial_proof P hP f hf).1 (τ, z)
    rw [hfun]
  · have hθ : (0 : ℝ) < w ^ 2 := by positivity
    have hmeas : AEStronglyMeasurable (fun y : Space => f (τ, y)) volume :=
      (hf.smooth.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    have havg := UnforcedLeray.Heat.heatConv_space_eq_average (w ^ 2) (fun y : Space => f (τ, y))
    have hfun : (fun z : Space => heatGauss f w (τ, z))
        = UnforcedLeray.Heat.heatConv (AddMonoidHom.id Space) (w ^ 2) (fun y : Space => f (τ, y)) := by
      rw [havg]
      funext z
      exact HeatGaussEquationAux.heatGauss_eq_average f hw τ z
    rw [hfun]
    exact UnforcedLeray.Heat.eLpNorm_heatConv_le (AddMonoidHom.id Space) measurable_id hθ hmeas
      (by norm_num)

end UnforcedLeray.Short.PartIIa
