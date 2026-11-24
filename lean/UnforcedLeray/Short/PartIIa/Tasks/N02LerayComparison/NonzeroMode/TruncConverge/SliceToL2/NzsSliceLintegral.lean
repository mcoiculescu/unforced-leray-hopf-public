import UnforcedLeray.Short.PartIIa.Sub.N02_4_11_2

/-!
# Part II-a, `Sub4` of `PartII-a:N02/4/11/2`: `q`-slice lintegral of a continuous profile

Target: `nzsSliceLintegral : NzsSliceLintegral` (`Sub/N02_4_11_2.lean`). Source of record:
`the November 2 reference manuscript`, lines 1744-1749.

For a continuous `g`, the squared norm `q ↦ ‖g (s, q, η)‖²` is continuous, hence integrable on
`(0, c]`. Its lintegral is the `ofReal` of the interval integral, and the extended-real power
`‖x‖ₑ ^ (2 : ℝ)` is `ofReal (‖x‖ ^ 2)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

theorem nzsSliceLintegral : NzsSliceLintegral := by
  intro c hc g hg s η
  have hcont : Continuous (fun q : ℝ => ‖g (s, q, η)‖ ^ 2) := by
    have hline : Continuous (fun q : ℝ => (s, q, η)) := by fun_prop
    exact ((hg.comp hline).norm).pow 2
  have hint : IntegrableOn (fun q : ℝ => ‖g (s, q, η)‖ ^ 2) (Ioc (0 : ℝ) c) :=
    hcont.integrableOn_Ioc
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) c)] (fun q : ℝ => ‖g (s, q, η)‖ ^ 2) :=
    ae_of_all _ (fun q => by positivity)
  rw [intervalIntegral.integral_of_le hc.le, ofReal_integral_eq_lintegral_ofReal hint hnn]
  refine lintegral_congr (fun q => ?_)
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]

end UnforcedLeray.Short.PartIIa
