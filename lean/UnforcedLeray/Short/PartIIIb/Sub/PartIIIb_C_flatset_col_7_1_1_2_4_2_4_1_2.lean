import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_1_of

/-!
# `SFCCausalHeatPer`: `q`-periodicity of the Duhamel integral for `s > 0`
(task `PartIII-b:C/flatset/col/7/1/1/2/4/2/4/1/2`)

Source `the November 2 reference manuscript`
lines 1650-1656, 1684-1689, 3426-3430.  The datum is periodized in `q` (`B0220.periodize`), so for
each `σ` the integrand `planeHeat θ (periodize c g (σ, ·))` is `c`-periodic in `q`
(`B0224.isPeriodic_planeHeat`, `B0224.isPeriodic_periodize_slice`).  No almost-everywhere
argument is needed: the periodicity holds pointwise in `σ`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem sfcCausalHeatPer : SFCCausalHeatPer := by
  intro c ν μ hc R0 g _hctx f' _hlift s q η _hs i
  have key : UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (sfcGp hc f') (s, (q + c, η)) =
      UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (sfcGp hc f') (s, (q, η)) := by
    unfold UnforcedLeray.B0225.causalHeat
    refine intervalIntegral.integral_congr (fun σ _ => ?_)
    simp only
    have hu := UnforcedLeray.B0224.isPeriodic_periodize_slice hc (sfcGp hc f') σ
    have h : UnforcedLeray.B0224.planeHeat (ν * (s - σ))
        (fun z : ℝ × ℝ => UnforcedLeray.B0220.periodize c (sfcGp hc f') (σ, z)) (q + c, η) =
        UnforcedLeray.B0224.planeHeat (ν * (s - σ))
        (fun z : ℝ × ℝ => UnforcedLeray.B0220.periodize c (sfcGp hc f') (σ, z)) (q, η) :=
      UnforcedLeray.B0224.isPeriodic_planeHeat hu (q, η)
    rw [h]
  rw [key]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
