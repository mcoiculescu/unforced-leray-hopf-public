import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_2_1
import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_2_1.Riemann
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# `L2SqMeas`: the slices near `s` are a.e. strongly measurable (source 341-348)

`F r z - F s z` is the limit, for every `z`, of the left Riemann sums of `t ↦ ∂ₜF t z` over
`[s, r]`. Each Riemann sum is a finite sum of the a.e. measurable slices at the sample times
(which lie within `ε` of `s`), so `F r - F s` is a.e. strongly measurable, and so is `F r`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace UnforcedLeray.Short.PartI.L2SqDeriv

theorem riemann_sample_dist {s r ε : ℝ} (hr : |r - s| < ε) {n k : ℕ} (hk : k < n) :
    |s + (k : ℝ) * ((r - s) / n) - s| < ε := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le k) hk)
  have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk.le
  have h1 : (k : ℝ) / n ≤ 1 := (div_le_one hn).2 hk'
  have h0 : (0 : ℝ) ≤ (k : ℝ) / n := by positivity
  have e : s + (k : ℝ) * ((r - s) / n) - s = ((k : ℝ) / n) * (r - s) := by ring
  rw [e, abs_mul, abs_of_nonneg h0]
  calc (k : ℝ) / n * |r - s| ≤ 1 * |r - s| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = |r - s| := one_mul _
    _ < ε := hr

end UnforcedLeray.Short.PartI.L2SqDeriv

open UnforcedLeray.Short.PartI.L2SqDeriv in
theorem l2SqMeas : UnforcedLeray.Short.PartI.L2SqDeriv.L2SqMeas := by
  intro μ F s ε K H r hr
  obtain ⟨hε, hC, hF, hD⟩ := H
  have hcont : ∀ z, Continuous (fun t => deriv (fun t' => F t' z) t) :=
    fun z => (hC z).continuous_deriv (by norm_num)
  -- the Riemann sums are a.e. strongly measurable
  have hRm : ∀ n : ℕ, AEStronglyMeasurable (fun z => ∑ k ∈ Finset.range n,
      (r - s) / n * deriv (fun t => F t z) (s + (k : ℝ) * ((r - s) / n))) μ := by
    intro n
    refine Finset.aestronglyMeasurable_fun_sum (Finset.range n) fun k hk => ?_
    have hkn : k < n := Finset.mem_range.1 hk
    have hmem := (hD _ (riemann_sample_dist hr hkn)).1.aestronglyMeasurable
    exact hmem.const_mul _
  -- the Riemann sums converge pointwise to the interval integral
  have hlim : ∀ z, Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
      (r - s) / n * deriv (fun t => F t z) (s + (k : ℝ) * ((r - s) / n))) atTop
      (𝓝 (∫ t in s..r, deriv (fun t' => F t' z) t)) :=
    fun z => tendsto_riemannSum (fun t => deriv (fun t' => F t' z) t) (hcont z) s r
  -- fundamental theorem of calculus on each slice
  have hFTC : ∀ z, ∫ t in s..r, deriv (fun t' => F t' z) t = F r z - F s z := by
    intro z
    exact intervalIntegral.integral_deriv_eq_sub' (fun t => F t z) rfl
      (fun t _ => ((hC z).differentiable (by norm_num)) t) (hcont z).continuousOn
  have hdm : AEStronglyMeasurable (fun z => F r z - F s z) μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop hRm (Eventually.of_forall fun z => ?_)
    have := hlim z
    rw [hFTC z] at this
    exact this
  have hsum := hdm.add hF.aestronglyMeasurable
  convert hsum using 1
  funext z
  simp only [Pi.add_apply]
  ring
