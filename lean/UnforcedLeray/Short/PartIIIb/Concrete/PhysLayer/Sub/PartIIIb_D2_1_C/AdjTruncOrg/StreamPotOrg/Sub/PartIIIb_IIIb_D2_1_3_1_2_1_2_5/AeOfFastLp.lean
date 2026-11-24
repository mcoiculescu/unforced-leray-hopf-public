import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_5.Defs

/-!
# `AeOfFastLp`: fast `L⁶` convergence gives a.e. convergence

Source `the November 2 reference manuscript` lines 1351-1362, 1470-1480.
Borel–Cantelli through `∑ ∫ ‖fₙ - u‖⁶ ≤ ∑ 2^{-6n} < ∞`.  Measurability of `u` is part of the
statement (without it `eLpNorm` is a lower integral and the claim fails).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem aeOfFastLp_holds : AeOfFastLp := by
  intro f u hf hu hb
  set g : ℕ → Space → ℝ≥0∞ := fun n y => ‖f n y - u y‖ₑ ^ (6 : ℝ) with hg
  have hm : ∀ n, AEMeasurable (g n) volume := fun n =>
    (((hf n).sub hu).enorm).pow_const _
  have hint : ∀ n, ∫⁻ y, g n y ≤ (((1 / 2 : ℝ≥0∞)) ^ n) ^ (6 : ℝ) := by
    intro n
    have h := hb n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at h
    have h6 : (6 : ℝ≥0∞).toReal = 6 := by norm_num
    rw [h6] at h
    have h2 := ENNReal.rpow_le_rpow h (z := 6) (by norm_num)
    rw [← ENNReal.rpow_mul] at h2
    have : (1 / (6 : ℝ)) * 6 = 1 := by norm_num
    rw [this, ENNReal.rpow_one] at h2
    exact h2
  have hsum : ∫⁻ y, ∑' n, g n y ≠ ∞ := by
    rw [lintegral_tsum hm]
    refine ne_top_of_le_ne_top (b := ∑' n : ℕ, ((1 / 2 : ℝ≥0∞) ^ 6) ^ n) ?_ (ENNReal.tsum_le_tsum ?_)
    · rw [ENNReal.tsum_geometric]
      refine ENNReal.inv_ne_top.2 ?_
      have : (1 / 2 : ℝ≥0∞) ^ 6 < 1 := pow_lt_one₀ (by simp) (by norm_num) (by norm_num)
      exact (tsub_pos_of_lt this).ne'
    · intro n
      refine (hint n).trans (le_of_eq ?_)
      rw [show ((6 : ℝ)) = ((6 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast, ← pow_mul, ← pow_mul,
        mul_comm]
  have hae : ∀ᵐ y ∂volume, ∑' n, g n y ≠ ∞ := by
    have := ae_lt_top' (AEMeasurable.tsum hm) hsum
    filter_upwards [this] with y hy using hy.ne
  filter_upwards [hae] with y hy
  have h0 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hy
  have h1 : Tendsto (fun n => ‖f n y - u y‖ₑ) atTop (𝓝 0) := by
    have := ((ENNReal.continuous_rpow_const (y := 1 / 6)).tendsto 0).comp h0
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at this
    refine this.congr (fun n => ?_)
    simp only [Function.comp, hg]
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [tendsto_iff_dist_tendsto_zero]
  have h2 : Tendsto (fun n => (‖f n y - u y‖ₑ).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [Function.comp_def] using this
  refine h2.congr (fun n => ?_)
  rw [dist_eq_norm, toReal_enorm]

end UnforcedLeray.Short.PartIIIb.Concrete
