import UnforcedLeray.Lib.HeatR3.Smooth

/-!
# Joint continuity of the heat flow of admissible data (INF04 T8, `continuousOn_average_joint`)


for admissible `f` (B0576, B0697, B0707, B0718, B1028), `(t, x) ↦ e^{tΔ}f(x)` is continuous on
`(0, ∞) × ℝ³`. Proof: kernel-side form `∫ G_t(x - y) f(y) dy` and dominated convergence, with
the bound `G_t(x - y) ≤ C (1 + |y|)^{-m}` uniform for `t ∈ (t₀/2, 2t₀)` and `|x - x₀| < 1`.
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology Real
open scoped ENNReal
open UnforcedLeray.Gaussian (Euc gaussKernel)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The heat kernel is jointly continuous in `(t, z)` on `t > 0`. -/
theorem continuousAt_kernel_joint {t₀ : ℝ} (ht₀ : 0 < t₀) (z₀ : Space) :
    ContinuousAt (fun p : ℝ × Space => kernel p.1 p.2) (t₀, z₀) := by
  have hform : (fun p : ℝ × Space => kernel p.1 p.2) = fun p =>
      (4 * π * p.1) ^ (-((3 : ℕ) : ℝ) / 2) * Real.exp (-‖p.2‖ ^ 2 / (4 * p.1)) := by
    funext p
    rw [← Gaussian.gaussKernel_three_eq, Gaussian.gaussKernel]
  rw [hform]
  have h1 : ContinuousAt (fun p : ℝ × Space => 4 * π * p.1) (t₀, z₀) :=
    (continuous_const.mul continuous_fst).continuousAt
  have h1' : 4 * π * t₀ ≠ 0 := by positivity
  have h2 : ContinuousAt (fun p : ℝ × Space => (4 * π * p.1) ^ (-((3 : ℕ) : ℝ) / 2)) (t₀, z₀) :=
    h1.rpow_const (Or.inl h1')
  have h3 : ContinuousAt (fun p : ℝ × Space => -‖p.2‖ ^ 2 / (4 * p.1)) (t₀, z₀) :=
    ((continuous_snd.norm.pow 2).neg.continuousAt).div
      ((continuous_const.mul continuous_fst).continuousAt) (by positivity)
  exact h2.mul (Real.continuous_exp.continuousAt.comp h3)

/-- Uniform weighted bound of the kernel on a time window `t ∈ (t₀/2, 2t₀)`. -/
theorem kernel_le_weight_uniform {t₀ : ℝ} (ht₀ : 0 < t₀) {m : ℝ} (hm : 0 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Ioo (t₀ / 2) (2 * t₀), ∀ z : Space,
      kernel t z ≤ C * (1 + ‖z‖) ^ (-m) := by
  obtain ⟨C₂, hC₂0, hC₂⟩ := one_add_rpow_mul_exp_le (m := m) (b := 1 / (8 * t₀)) hm
    (by positivity)
  refine ⟨(2 * π * t₀) ^ (-((3 : ℕ) : ℝ) / 2) * C₂, by positivity, fun t ht z => ?_⟩
  have ht0 : 0 < t := lt_trans (by positivity) ht.1
  rw [← Gaussian.gaussKernel_three_eq, Gaussian.gaussKernel]
  have hA : (4 * π * t) ^ (-((3 : ℕ) : ℝ) / 2) ≤ (2 * π * t₀) ^ (-((3 : ℕ) : ℝ) / 2) := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by norm_num)
    nlinarith [ht.1, Real.pi_pos]
  have hE : Real.exp (-‖z‖ ^ 2 / (4 * t)) ≤ Real.exp (-(1 / (8 * t₀) * ‖z‖ ^ 2)) := by
    apply Real.exp_le_exp.mpr
    have h8 : 4 * t ≤ 8 * t₀ := by linarith [ht.2]
    rw [neg_div, neg_le_neg_iff, div_mul_eq_mul_div, one_mul]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) h8
  have hz := hC₂ ‖z‖ (norm_nonneg z)
  have hpos : 0 < (1 + ‖z‖) ^ m := Real.rpow_pos_of_pos (by positivity) m
  have hE' : Real.exp (-(1 / (8 * t₀) * ‖z‖ ^ 2)) ≤ C₂ * (1 + ‖z‖) ^ (-m) := by
    rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, le_div_iff₀ hpos]
    linarith [hz, mul_comm ((1 + ‖z‖) ^ m) (Real.exp (-(1 / (8 * t₀) * ‖z‖ ^ 2)))]
  calc (4 * π * t) ^ (-((3 : ℕ) : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (4 * t))
      ≤ (2 * π * t₀) ^ (-((3 : ℕ) : ℝ) / 2) * (C₂ * (1 + ‖z‖) ^ (-m)) := by
        gcongr
        · exact hE.trans hE'
    _ = (2 * π * t₀) ^ (-((3 : ℕ) : ℝ) / 2) * C₂ * (1 + ‖z‖) ^ (-m) := by ring

/-- **INF04 T8 `continuousOn_average_joint`.** For admissible `f`, `(t, x) ↦ e^{tΔ}f(x)` is
continuous on `(0, ∞) × ℝ³`. -/
theorem continuousOn_average_joint {f : Space → E} (hf : HeatAdmissible f) :
    ContinuousOn (fun z : ℝ × Space => average z.1 f z.2) (Ioi 0 ×ˢ univ) := by
  intro z₀ hz₀
  obtain ⟨t₀, x₀⟩ := z₀
  have ht₀ : 0 < t₀ := hz₀.1
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨m, hm⟩ := hf.integrable_norm
  have hm0 : (0 : ℝ) ≤ m := by positivity
  obtain ⟨C, hC0, hC⟩ := kernel_le_weight_uniform ht₀ hm0
  have hrep : (fun z : ℝ × Space => average z.1 f z.2) =
      fun z => ∫ y : Space, kernel z.1 (z.2 - y) • f y := by
    funext z
    rw [average_eq_kconv]
    rfl
  rw [hrep]
  have hnbhd : (Ioo (t₀ / 2) (2 * t₀) ×ˢ Metric.ball x₀ 1) ∈ 𝓝 (t₀, x₀) :=
    prod_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)) (Metric.ball_mem_nhds x₀ one_pos)
  refine continuousAt_of_dominated
    (bound := fun y => C * (2 + ‖x₀‖) ^ (m : ℝ) * ((1 + ‖y‖) ^ (-(m : ℝ)) * ‖f y‖)) ?_ ?_
    (hm.const_mul _) ?_
  · filter_upwards [hnbhd] with z hz
    exact (((continuous_kernel z.1).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      ).smul hf.1
  · filter_upwards [hnbhd] with z hz
    refine Eventually.of_forall fun y => ?_
    obtain ⟨ht, hx⟩ := hz
    have hx' : ‖z.2‖ ≤ 1 + ‖x₀‖ := by
      have := Metric.mem_ball.mp hx
      rw [dist_eq_norm] at this
      calc ‖z.2‖ = ‖(z.2 - x₀) + x₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖z.2 - x₀‖ + ‖x₀‖ := norm_add_le _ _
        _ ≤ 1 + ‖x₀‖ := by linarith
    have ht0 : 0 < z.1 := lt_trans (by positivity) ht.1
    rw [norm_smul, Real.norm_of_nonneg (kernel_nonneg ht0 _)]
    have hk : kernel z.1 (z.2 - y) ≤ C * ((1 + ‖z.2‖) ^ (m : ℝ) * (1 + ‖y‖) ^ (-(m : ℝ))) :=
      (hC z.1 ht (z.2 - y)).trans (mul_le_mul_of_nonneg_left
        (one_add_norm_sub_rpow_neg_le hm0 z.2 y) hC0.le)
    have hw : (1 + ‖z.2‖) ^ (m : ℝ) ≤ (2 + ‖x₀‖) ^ (m : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) hm0
    calc kernel z.1 (z.2 - y) * ‖f y‖
        ≤ C * ((1 + ‖z.2‖) ^ (m : ℝ) * (1 + ‖y‖) ^ (-(m : ℝ))) * ‖f y‖ := by gcongr
      _ ≤ C * ((2 + ‖x₀‖) ^ (m : ℝ) * (1 + ‖y‖) ^ (-(m : ℝ))) * ‖f y‖ := by gcongr
      _ = C * (2 + ‖x₀‖) ^ (m : ℝ) * ((1 + ‖y‖) ^ (-(m : ℝ)) * ‖f y‖) := by ring
  · refine Eventually.of_forall fun y => ?_
    have hk := continuousAt_kernel_joint ht₀ (x₀ - y)
    have hmap : ContinuousAt (fun z : ℝ × Space => (z.1, z.2 - y)) (t₀, x₀) :=
      (continuous_fst.prodMk (continuous_snd.sub continuous_const)).continuousAt
    exact (ContinuousAt.comp (g := fun p : ℝ × Space => kernel p.1 p.2)
      (f := fun z : ℝ × Space => (z.1, z.2 - y)) hk hmap).smul continuousAt_const

end UnforcedLeray.Heat
