import UnforcedLeray.Short.PartI.Sub.T02_3_8

/-!
# Part I, task `PartI:T02/3/8/HmeanLap`: the horizontal average of the Laplacian

Source of record: `the November 2 reference manuscript`, lines 276-288 (bounded
periodic pressure) and line 447 (the Poisson equation for the pressure).

Target: `CylPoisHmeanLap` (`Short/PartI/Sub/T02_3_8.lean`): for `c > 0` and a `C²`, `c`-periodic
`f`, the horizontal average of `Δf = ∂_q² f + ∂_η² f` equals the horizontal average of `∂_η² f`.

Proof idea.  Split `Δf` into its two second partials.  Both are continuous, so the integral splits.
The `∂_q²` part integrates to zero over one period: `G = ∂_q f` is `C¹` and `c`-periodic, and the
fundamental theorem of calculus on `[-c/2, c/2]` gives `∫ ∂_q G = G(c/2, η) - G(-c/2, η) = 0`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

open MeasureTheory Set

/-- The `q`-average over one period of `∂_q G` vanishes for a `c`-periodic `C¹` function `G`
(the `C¹` version of `mm_integral_partialQ_zero`; fundamental theorem of calculus). -/
theorem cpHL_integral_partialQ_zero {c : ℝ} (hc : 0 < c) {G : UnforcedLeray.Cyl.Plane → ℝ}
    (hG : Differentiable ℝ G) (hGc : Continuous (UnforcedLeray.Cyl.partialQ G))
    (hper : UnforcedLeray.Cyl.IsPeriodic c G) (η : ℝ) :
    ∫ q in Ioc (-c / 2) (c / 2), UnforcedLeray.Cyl.partialQ G (q, η) = 0 := by
  have hcq : Continuous (fun q : ℝ => ((q, η) : UnforcedLeray.Cyl.Plane)) :=
    continuous_id.prodMk continuous_const
  have hftc : ∫ q in (-c / 2)..(c / 2), UnforcedLeray.Cyl.partialQ G (q, η)
      = G (c / 2, η) - G (-c / 2, η) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun q => G (q, η))
    · intro x _
      exact UnforcedLeray.Cyl.hasDerivAt_sliceQ hG x η
    · exact (hGc.comp hcq).intervalIntegrable _ _
  rw [intervalIntegral.integral_of_le (by linarith : -c / 2 ≤ c / 2)] at hftc
  rw [hftc, hper.neg_half η, sub_self]

theorem cylPoisHmeanLap : CylPoisHmeanLap := by
  unfold CylPoisHmeanLap
  intro c f hc hf hper η
  have hC := UnforcedLeray.Cyl.C2.of_contDiff hf
  have hcq : Continuous (fun q : ℝ => ((q, η) : UnforcedLeray.Cyl.Plane)) :=
    continuous_id.prodMk continuous_const
  have hint1 : IntegrableOn
      (fun q : ℝ => UnforcedLeray.Cyl.partialQ (UnforcedLeray.Cyl.partialQ f) (q, η))
      (Ioc (-c / 2) (c / 2)) :=
    (hC.contQQ.comp hcq).integrableOn_Ioc
  have hint2 : IntegrableOn
      (fun q : ℝ => UnforcedLeray.Cyl.partialEta (UnforcedLeray.Cyl.partialEta f) (q, η))
      (Ioc (-c / 2) (c / 2)) :=
    (hC.contEtaEta.comp hcq).integrableOn_Ioc
  have h0 : ∫ q in Ioc (-c / 2) (c / 2),
      UnforcedLeray.Cyl.partialQ (UnforcedLeray.Cyl.partialQ f) (q, η) = 0 :=
    cpHL_integral_partialQ_zero hc hC.diffQ hC.contQQ hper.partialQ η
  unfold hmean
  rw [show (fun q : ℝ => UnforcedLeray.Train.lapS f (q, η)) =
      fun q : ℝ => UnforcedLeray.Cyl.partialQ (UnforcedLeray.Cyl.partialQ f) (q, η)
        + UnforcedLeray.Cyl.partialEta (UnforcedLeray.Cyl.partialEta f) (q, η) from rfl]
  rw [MeasureTheory.integral_add hint1 hint2, h0, zero_add]

end UnforcedLeray.Short.PartI
