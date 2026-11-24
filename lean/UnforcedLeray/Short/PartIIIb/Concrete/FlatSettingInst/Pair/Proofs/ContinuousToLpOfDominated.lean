import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Defs
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Continuity into `L²` by dominated convergence (source 4352-4356)

If `F s` is dominated in `L²` by a fixed `g`, and `s ↦ F s x` is continuous for a.e. `x`, then
`s ↦ F s` is continuous as a map into `L²(μ)`.  Route: `dist = (eLpNorm (F s - F t) 2 μ).toReal`,
then the `L²` norm is the `1/2` power of `∫⁻ ‖F s - F t‖ₑ^2`, which tends to `0` by
dominated convergence for the filter `𝓝 t`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair

/-- **Continuity into `L²` by dominated convergence**, in the form `ContinuousToLpOfDominated`. -/
theorem continuousToLpOfDominated : ContinuousToLpOfDominated := by
  intro μ F hF g hg hdom hcont
  rw [continuous_iff_continuousAt]
  intro t
  unfold ContinuousAt
  rw [tendsto_iff_dist_tendsto_zero]
  have hdist : ∀ s, dist ((hF s).toLp (F s)) ((hF t).toLp (F t)) =
      (eLpNorm (F s - F t) 2 μ).toReal := by
    intro s
    rw [Lp.dist_def]
    congr 1
    exact eLpNorm_congr_ae ((hF s).coeFn_toLp.sub (hF t).coeFn_toLp)
  simp only [hdist]
  -- the integrability of the dominating function
  have hgI : ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ ≠ ∞ := by
    have h := hg.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at h
    simp only [ENNReal.toReal_ofNat] at h
    intro hT
    rw [hT, ENNReal.top_rpow_of_pos (by norm_num)] at h
    exact lt_irrefl _ h
  have hfin : ∫⁻ x, (2 * ‖g x‖ₑ) ^ (2 : ℝ) ∂μ ≠ ∞ := by
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by norm_num))]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by norm_num)) hgI
  -- pointwise domination of the squared differences
  have hbound : ∀ s, ∀ᵐ x ∂μ, ‖F s x - F t x‖ₑ ^ (2 : ℝ) ≤ (2 * ‖g x‖ₑ) ^ (2 : ℝ) := by
    intro s
    filter_upwards [hdom s, hdom t] with x h1 h2
    have e1 : ‖F s x‖ₑ ≤ ‖g x‖ₑ := by
      rw [← ofReal_norm, Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (h1.trans (le_abs_self _))
    have e2 : ‖F t x‖ₑ ≤ ‖g x‖ₑ := by
      rw [← ofReal_norm, Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (h2.trans (le_abs_self _))
    have hle : ‖F s x - F t x‖ₑ ≤ 2 * ‖g x‖ₑ := by
      calc ‖F s x - F t x‖ₑ ≤ ‖F s x‖ₑ + ‖F t x‖ₑ := enorm_sub_le
        _ ≤ ‖g x‖ₑ + ‖g x‖ₑ := add_le_add e1 e2
        _ = 2 * ‖g x‖ₑ := (two_mul _).symm
    exact ENNReal.rpow_le_rpow hle (by norm_num)
  -- the dominated convergence of the squared differences
  have hI : Tendsto (fun s => ∫⁻ x, ‖F s x - F t x‖ₑ ^ (2 : ℝ) ∂μ) (𝓝 t) (𝓝 0) := by
    have hmeas : ∀ᶠ s in 𝓝 t, AEMeasurable (fun x => ‖F s x - F t x‖ₑ ^ (2 : ℝ)) μ :=
      Filter.Eventually.of_forall fun s =>
        ((((hF s).aestronglyMeasurable.sub (hF t).aestronglyMeasurable).enorm).pow_const
          (2 : ℝ))
    have hbd : ∀ᶠ s in 𝓝 t, ∀ᵐ x ∂μ, ‖F s x - F t x‖ₑ ^ (2 : ℝ) ≤ (2 * ‖g x‖ₑ) ^ (2 : ℝ) :=
      Filter.Eventually.of_forall hbound
    have hlim : ∀ᵐ x ∂μ, Tendsto (fun s => ‖F s x - F t x‖ₑ ^ (2 : ℝ)) (𝓝 t)
        (𝓝 ((fun _ => (0 : ℝ≥0∞)) x)) := by
      filter_upwards [hcont] with x hx
      have h1 : Tendsto (fun s => F s x - F t x) (𝓝 t) (𝓝 0) := by
        simpa using (hx.tendsto t).sub_const (F t x)
      have h2 : Tendsto (fun s => ‖F s x - F t x‖ₑ) (𝓝 t) (𝓝 0) := by
        have h := (continuous_enorm.tendsto (0 : ℂ)).comp h1
        rw [enorm_zero] at h
        exact h
      have h3 : Tendsto (fun s => ‖F s x - F t x‖ₑ ^ (2 : ℝ)) (𝓝 t) (𝓝 ((0 : ℝ≥0∞) ^ (2 : ℝ))) :=
        ((ENNReal.continuous_rpow_const (y := 2)).tendsto (0 : ℝ≥0∞)).comp h2
      rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
      exact h3
    have := tendsto_lintegral_filter_of_dominated_convergence' (μ := μ) (l := 𝓝 t)
      (F := fun s x => ‖F s x - F t x‖ₑ ^ (2 : ℝ)) (f := fun _ => (0 : ℝ≥0∞))
      (fun x => (2 * ‖g x‖ₑ) ^ (2 : ℝ)) hmeas hbd hfin hlim
    simpa using this
  -- the `L²` norm is the `1/2` power of the integral
  have hEq : ∀ s, eLpNorm (F s - F t) 2 μ =
      (∫⁻ x, ‖F s x - F t x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    intro s
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, Pi.sub_apply]
  have hE : Tendsto (fun s => eLpNorm (F s - F t) 2 μ) (𝓝 t) (𝓝 0) := by
    simp only [hEq]
    have h := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto (0 : ℝ≥0∞)).comp hI
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
    exact h
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hE
  rw [ENNReal.toReal_zero] at h
  exact h

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair
