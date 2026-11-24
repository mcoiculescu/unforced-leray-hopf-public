import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.Defs
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.OdHeatTaylor

/-!
# `odHeatDeriv` (task `PartIII-b:C/near/pins/3/4/2/3/2/4/14`)

Right derivative at `0` of `r ↦ e^{θ(r)Δ} Ψ` with `θ(r) = h(e^r - 1)`, from the second-order
heat Taylor bound `odHeatTaylor` (`‖e^{θΔ}Ψ - Ψ - θΨΔ‖ ≤ C θ²` for `0 ≤ θ ≤ 1`) and
`|e^r - 1 - r| ≤ r²` for `|r| ≤ 1` (`Real.abs_exp_sub_one_sub_id_le`).
Source `the November 2 reference manuscript`
lines 3346-3352 and 1339-1362.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Asymptotics

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem odHeatDeriv : OD_HeatDeriv := by
  unfold OD_HeatDeriv
  intro p ψ hψ Ψ ΨΔ hΨ hΔ h hh
  obtain ⟨C, hC0, hC⟩ := odHeatTaylor p ψ hψ Ψ ΨΔ hΨ hΔ
  -- the heat factor at `θ = 0` is the identity
  have h0 : UnforcedLeray.B0223.heatC (E := UnforcedLeray.B0223.SpaceC) 0 Ψ = Ψ := by
    have hb := hC 0 le_rfl zero_le_one
    simpa [sub_eq_zero] using hb
  have hA : ∀ᶠ r in 𝓝 (0:ℝ), |r| ≤ 1 := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) one_pos] with r hr
    have := Metric.mem_ball.mp hr
    rw [Real.dist_eq, sub_zero] at this
    exact this.le
  have hE3 : ∀ᶠ r in 𝓝 (0:ℝ), h * (Real.exp r - 1) < 1 := by
    have hc : Tendsto (fun r : ℝ => h * (Real.exp r - 1)) (𝓝 0)
        (𝓝 (h * (Real.exp 0 - 1))) :=
      (continuous_const.mul (Real.continuous_exp.sub continuous_const)).tendsto 0
    have hlt : h * (Real.exp 0 - 1) < 1 := by simp
    exact hc.eventually (Iio_mem_nhds hlt)
  have hE : ∀ᶠ r in 𝓝[Ici 0] (0:ℝ), 0 ≤ r ∧ |r| ≤ 1 ∧ h * (Real.exp r - 1) ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hA,
      eventually_nhdsWithin_of_eventually_nhds hE3] with r hr1 hr2 hr3
    exact ⟨Set.mem_Ici.mp hr1, hr2, hr3.le⟩
  have hbound : ∀ᶠ r in 𝓝[Ici 0] (0:ℝ),
      ‖UnforcedLeray.B0223.heatC (E := UnforcedLeray.B0223.SpaceC) (h * (Real.exp r - 1)) Ψ
        - UnforcedLeray.B0223.heatC (E := UnforcedLeray.B0223.SpaceC)
            (h * (Real.exp 0 - 1)) Ψ
        - (r - 0) • ((h : ℂ) • ΨΔ)‖ ≤ (4 * C * h ^ 2 + h * ‖ΨΔ‖) * ‖r ^ 2‖ := by
    filter_upwards [hE] with r hr
    obtain ⟨hr0, hr1, hr3⟩ := hr
    have hr1' : r ≤ 1 := (abs_le.mp hr1).2
    have hexp1 : |Real.exp r - 1 - r| ≤ r ^ 2 := Real.abs_exp_sub_one_sub_id_le hr1
    have hexp2 : 0 ≤ Real.exp r - 1 := by linarith [Real.one_le_exp hr0]
    have hrle : r ^ 2 ≤ r := by nlinarith
    have hexp3 : Real.exp r - 1 ≤ 2 * r := by
      have := (abs_le.mp hexp1).2
      linarith
    have e0 : h * (Real.exp 0 - 1) = 0 := by simp
    have hn : ‖r ^ 2‖ = r ^ 2 := by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r)]
    rw [e0, h0, sub_zero, hn, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
    set θ : ℝ := h * (Real.exp r - 1) with hθdef
    have hθ0 : 0 ≤ θ := mul_nonneg hh hexp2
    have hθ1 : θ ≤ 2 * h * r := by
      have := mul_le_mul_of_nonneg_left hexp3 hh
      rw [hθdef]
      linarith
    have hT : ‖UnforcedLeray.B0223.heatC (E := UnforcedLeray.B0223.SpaceC) θ Ψ - Ψ
        - (θ : ℂ) • ΨΔ‖ ≤ C * θ ^ 2 := hC θ hθ0 hr3
    have hθdiff : θ - h * r = h * (Real.exp r - 1 - r) := by rw [hθdef]; ring
    have hdec : UnforcedLeray.B0223.heatC (E := UnforcedLeray.B0223.SpaceC) θ Ψ - Ψ
        - ((r : ℂ) * (h : ℂ)) • ΨΔ
        = (UnforcedLeray.B0223.heatC (E := UnforcedLeray.B0223.SpaceC) θ Ψ - Ψ
            - (θ : ℂ) • ΨΔ) + (((θ - h * r : ℝ)) : ℂ) • ΨΔ := by
      push_cast
      module
    have hB : ‖(((θ - h * r : ℝ)) : ℂ) • ΨΔ‖ ≤ h * r ^ 2 * ‖ΨΔ‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, hθdiff, abs_mul,
        abs_of_nonneg hh]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp1 hh) (norm_nonneg _)
    have hθsq : θ ^ 2 ≤ (2 * h * r) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hθ1) (add_nonneg hθ0 (le_trans hθ0 hθ1))]
    have hfin : C * θ ^ 2 + h * r ^ 2 * ‖ΨΔ‖ ≤ (4 * C * h ^ 2 + h * ‖ΨΔ‖) * r ^ 2 := by
      have := mul_le_mul_of_nonneg_left hθsq hC0
      nlinarith [this]
    refine (congrArg (fun z => ‖z‖) hdec).trans_le ?_
    refine (norm_add_le _ _).trans ?_
    exact (add_le_add hT hB).trans hfin
  have hsmall : (fun r : ℝ => r ^ 2) =o[𝓝[Ici 0] (0:ℝ)] (fun r : ℝ => r - 0) := by
    simp only [sub_zero]
    exact (isLittleO_pow_id (by norm_num : 1 < 2)).mono nhdsWithin_le_nhds
  refine (hasDerivWithinAt_iff_isLittleO).2 ?_
  exact IsBigO.trans_isLittleO (IsBigO.of_bound _ hbound) hsmall

end UnforcedLeray.Short.PartIIIb.NearInst
