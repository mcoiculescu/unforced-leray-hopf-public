import UnforcedLeray.Short.PartIIb.Sub.B1

/-!
# Part II-b, task `PartII-b:B1/7`: the cutoff tail vanishes

Proves `UnforcedLeray.Short.IIb.CutoffTailSmall` (`Sub/B1.lean`): for `F ∈ L^{q₀'}`,
`‖F - χ_R F‖_{L^{q₀'}} → 0` as `R → ∞`, where `q₀' = conjExp q0E = 11/7`.
Source of record: `the November 2 reference manuscript`.

Proof: with `r = (conjExp q0E).toReal > 0`, the `L^{q₀'}` norm is `(∫⁻ ‖F - χ_R F‖ₑ ^ r)^(1/r)`.
The integrand tends to `0` pointwise (it vanishes once `R ≥ ‖y‖`) and is dominated by
`‖F y‖ₑ ^ r`, which is integrable. Dominated convergence gives the integral tends to `0`, and
continuity of `x ↦ x ^ (1/r)` at `0` concludes.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0412

theorem cutoffTailSmall : UnforcedLeray.Short.IIb.CutoffTailSmall := by
  unfold UnforcedLeray.Short.IIb.CutoffTailSmall
  intro F hF
  have hp1 : (1 : ℝ≥0∞) ≤ conjExp q0E := fact_one_le_conjExp_q0E_B1.out
  have hp_ne_top : conjExp q0E ≠ ⊤ := conjExp_ne_top one_lt_q0E
  have hp_ne_zero : conjExp q0E ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hr_pos : 0 < (conjExp q0E).toReal := ENNReal.toReal_pos hp_ne_zero hp_ne_top
  have hr_nonneg : 0 ≤ (conjExp q0E).toReal := hr_pos.le
  -- pointwise domination: `0 ≤ 1 - χ ≤ 1`, so `‖F y - χ F y‖ₑ ≤ ‖F y‖ₑ`
  have hb : ∀ (R : ℝ) (y), ‖F y - NavierStokesR3.ComparisonCutoffs.cutoff R y • F y‖ₑ ≤ ‖F y‖ₑ := by
    intro R y
    have h0 := NavierStokesR3.ComparisonCutoffs.cutoff_nonneg R y
    have h1 := NavierStokesR3.ComparisonCutoffs.cutoff_le_one R y
    have hsub : F y - NavierStokesR3.ComparisonCutoffs.cutoff R y • F y
        = (1 - NavierStokesR3.ComparisonCutoffs.cutoff R y) • F y := by
      rw [sub_smul, one_smul]
    have hc : ‖1 - NavierStokesR3.ComparisonCutoffs.cutoff R y‖ₑ ≤ 1 := by
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_one.2 (abs_le.2 ⟨by linarith, by linarith⟩)
    rw [hsub, enorm_smul]
    exact mul_le_of_le_one_left zero_le hc
  -- measurability of the integrand for each fixed `R`
  have hmeas : ∀ R : ℝ, AEMeasurable
      (fun y => ‖F y - NavierStokesR3.ComparisonCutoffs.cutoff R y • F y‖ₑ ^ (conjExp q0E).toReal)
      volume := by
    intro R
    have hFm : AEMeasurable F volume := hF.aestronglyMeasurable.aemeasurable
    have hχm : AEMeasurable (fun y => NavierStokesR3.ComparisonCutoffs.cutoff R y) volume :=
      (NavierStokesR3.ComparisonCutoffs.cutoff_smooth R).continuous.measurable.aemeasurable
    have hsm : AEMeasurable (fun y => NavierStokesR3.ComparisonCutoffs.cutoff R y • F y) volume :=
      hχm.smul hFm
    have hdif : AEMeasurable
        (fun y => F y - NavierStokesR3.ComparisonCutoffs.cutoff R y • F y) volume :=
      hFm.sub hsm
    exact hdif.enorm.pow_const _
  -- the dominating function is integrable
  have hfin : ∫⁻ y, ‖F y‖ₑ ^ (conjExp q0E).toReal ∂volume ≠ ⊤ :=
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp_ne_zero hp_ne_top hF.eLpNorm_lt_top).ne
  -- pointwise convergence to zero: the integrand vanishes once `R ≥ ‖y‖`
  have hlim : ∀ y, Tendsto
      (fun R : ℝ => ‖F y - NavierStokesR3.ComparisonCutoffs.cutoff R y • F y‖ₑ ^ (conjExp q0E).toReal)
      atTop (𝓝 0) := by
    intro y
    have hev : (fun _ : ℝ => (0 : ℝ≥0∞)) =ᶠ[atTop]
        (fun R : ℝ => ‖F y - NavierStokesR3.ComparisonCutoffs.cutoff R y • F y‖ₑ ^ (conjExp q0E).toReal) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop ‖y‖] with R hR0 hRy
      rw [NavierStokesR3.ComparisonCutoffs.cutoff_eq_one hR0 hRy, one_smul, sub_self]
      simp [ENNReal.zero_rpow_of_pos hr_pos]
    exact tendsto_const_nhds.congr' hev
  -- dominated convergence on the integrals
  have hD : Tendsto
      (fun R : ℝ => ∫⁻ y, ‖F y - NavierStokesR3.ComparisonCutoffs.cutoff R y • F y‖ₑ ^ (conjExp q0E).toReal ∂volume)
      atTop (𝓝 0) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence' (μ := volume) (l := atTop)
      (F := fun (R : ℝ) y =>
        ‖F y - NavierStokesR3.ComparisonCutoffs.cutoff R y • F y‖ₑ ^ (conjExp q0E).toReal)
      (f := fun _ => (0 : ℝ≥0∞)) (fun y => ‖F y‖ₑ ^ (conjExp q0E).toReal)
      (Filter.Eventually.of_forall hmeas)
      (Filter.Eventually.of_forall fun R =>
        ae_of_all _ fun y => ENNReal.rpow_le_rpow (hb R y) hr_nonneg)
      hfin (ae_of_all _ hlim)
    simpa only [lintegral_zero] using h
  -- the `L^{q₀'}` norm is the `1/r` power of the integral
  have hEq : ∀ R : ℝ, eLpNorm (fun y => F y - NavierStokesR3.ComparisonCutoffs.cutoff R y • F y)
      (conjExp q0E) volume
      = (∫⁻ y, ‖F y - NavierStokesR3.ComparisonCutoffs.cutoff R y • F y‖ₑ ^ (conjExp q0E).toReal ∂volume)
          ^ (1 / (conjExp q0E).toReal) :=
    fun R => eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top
  simp only [hEq]
  have hpow := hD.ennrpow_const (1 / (conjExp q0E).toReal)
  rw [ENNReal.zero_rpow_of_pos (one_div_pos.2 hr_pos)] at hpow
  exact hpow

end UnforcedLeray.Short.IIb
