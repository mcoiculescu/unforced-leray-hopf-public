import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Defs

/-!
# Time part of `paramDmuCausal` (helper leaves)

Source `the November 2 reference manuscript` 3611-3621, 4171-4186. Helper leaves for
`ParamDmu.lean`: the causal indicator `τ ↦ 1_{e.1<τ} k(τ - e.1) y₀ e` is Lipschitz on the ball with
constant `|B e|`, differentiable at `τ₀` for a.e. `e`, so the time derivative passes under the integral.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma pdc_ball_Icc {τ₀ ε τ1 τ2 : ℝ} (h1 : τ1 ∈ Metric.ball τ₀ ε) (h2 : τ2 ∈ Metric.ball τ₀ ε) :
    ∀ τ ∈ Icc τ1 τ2, τ ∈ Metric.ball τ₀ ε := by
  intro τ hτ
  rw [Metric.mem_ball, Real.dist_eq] at h1 h2 ⊢
  rw [abs_lt] at h1 h2 ⊢
  constructor <;> linarith [hτ.1, hτ.2]

lemma pdc_small (k : ℝ → Space → ℝ × Space → Space) (τ₀ : ℝ) (y₀ : Space) (ε : ℝ)
    (B : ℝ × Space → ℝ) (e : ℝ × Space) (τ1 τ2 : ℝ) (hτ1 : τ1 ∈ Metric.ball τ₀ ε)
    (hτ2 : τ2 ∈ Metric.ball τ₀ ε) (hy0 : y₀ ∈ Metric.ball y₀ ε) (hε : 0 < ε)
    (hdiff : ∀ (e : ℝ × Space) (h : ℝ), 0 < h → ∀ y ∈ Metric.ball y₀ ε,
      ContDiffAt ℝ 2 (fun y' => k h y' e) y ∧ DifferentiableAt ℝ (fun h' => k h' y e) h)
    (hlim : ∀ e : ℝ × Space, ∀ y ∈ Metric.ball y₀ ε, Tendsto (fun h => k h y e) (𝓝[>] 0) (𝓝 0))
    (hbd : ∀ (e : ℝ × Space), ∀ τ ∈ Metric.ball τ₀ ε, e.1 < τ → ∀ y ∈ Metric.ball y₀ ε,
      ‖k (τ - e.1) y e‖ ≤ B e ∧ ‖deriv (fun h => k h y e) (τ - e.1)‖ ≤ B e)
    (h1 : τ1 ≤ e.1) (h2 : e.1 < τ2) :
    ‖k (τ2 - e.1) y₀ e‖ ≤ B e * (τ2 - e.1) := by
  have hh : 0 < τ2 - e.1 := by linarith
  have hB0 : 0 ≤ B e := by
    have := (hbd e τ2 hτ2 h2 y₀ hy0).2
    exact le_trans (norm_nonneg _) this
  have hsub : ∀ s ∈ Ioo (0 : ℝ) (τ2 - e.1), ‖k (τ2 - e.1) y₀ e - k s y₀ e‖ ≤ B e * ((τ2 - e.1) - s) := by
    intro s hs
    have hmvt := (convex_Icc s (τ2 - e.1)).norm_image_sub_le_of_norm_deriv_le
      (f := fun h => k h y₀ e) (C := B e) (s := Icc s (τ2 - e.1))
      (fun c hc => (hdiff e c (by linarith [hc.1, hs.1]) y₀ hy0).2)
      (fun c hc => by
        have hmem : c + e.1 ∈ Metric.ball τ₀ ε :=
          pdc_ball_Icc hτ1 hτ2 _ ⟨by linarith [hc.1, hs.1, h1], by linarith [hc.2]⟩
        have := (hbd e (c + e.1) hmem (by linarith [hc.1, hs.1]) y₀ hy0).2
        rwa [add_sub_cancel_right] at this)
      (left_mem_Icc.2 (by linarith [hs.2])) (right_mem_Icc.2 (by linarith [hs.2]))
    have hn : ‖(τ2 - e.1) - s‖ = (τ2 - e.1) - s := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2])]
    rw [hn] at hmvt
    exact hmvt
  have hf : Tendsto (fun s => ‖k (τ2 - e.1) y₀ e - k s y₀ e‖) (𝓝[>] 0) (𝓝 ‖k (τ2 - e.1) y₀ e - 0‖) :=
    ((hlim e y₀ hy0).const_sub (k (τ2 - e.1) y₀ e)).norm
  have hg : Tendsto (fun s => B e * ((τ2 - e.1) - s)) (𝓝[>] 0) (𝓝 (B e * ((τ2 - e.1) - 0))) :=
    ((continuous_const.mul (continuous_const.sub continuous_id)).tendsto 0).mono_left
      nhdsWithin_le_nhds
  have key := le_of_tendsto_of_tendsto hf hg (by
    filter_upwards [Ioo_mem_nhdsGT hh] with s hs
    exact hsub s hs)
  rw [sub_zero, sub_zero] at key
  exact key


lemma pdc_lip (k : ℝ → Space → ℝ × Space → Space) (τ₀ : ℝ) (y₀ : Space) (ε : ℝ)
    (B : ℝ × Space → ℝ) (hε : 0 < ε)
    (hdiff : ∀ (e : ℝ × Space) (h : ℝ), 0 < h → ∀ y ∈ Metric.ball y₀ ε,
      ContDiffAt ℝ 2 (fun y' => k h y' e) y ∧ DifferentiableAt ℝ (fun h' => k h' y e) h)
    (hlim : ∀ e : ℝ × Space, ∀ y ∈ Metric.ball y₀ ε, Tendsto (fun h => k h y e) (𝓝[>] 0) (𝓝 0))
    (hbd : ∀ (e : ℝ × Space), ∀ τ ∈ Metric.ball τ₀ ε, e.1 < τ → ∀ y ∈ Metric.ball y₀ ε,
      ‖k (τ - e.1) y e‖ ≤ B e ∧ ‖deriv (fun h => k h y e) (τ - e.1)‖ ≤ B e)
    (e : ℝ × Space) :
    LipschitzOnWith (Real.nnabs (B e))
      (fun τ => if e.1 < τ then k (τ - e.1) y₀ e else 0) (Metric.ball τ₀ ε) := by
  have hy0 : y₀ ∈ Metric.ball y₀ ε := Metric.mem_ball_self hε
  have aux : ∀ τ1 ∈ Metric.ball τ₀ ε, ∀ τ2 ∈ Metric.ball τ₀ ε, τ1 ≤ τ2 →
      ‖(if e.1 < τ1 then k (τ1 - e.1) y₀ e else 0) - (if e.1 < τ2 then k (τ2 - e.1) y₀ e else 0)‖
        ≤ |B e| * (τ2 - τ1) := by
    intro τ1 hτ1 τ2 hτ2 h12
    by_cases h1 : e.1 < τ1
    · have h2 : e.1 < τ2 := lt_of_lt_of_le h1 h12
      rw [if_pos h1, if_pos h2]
      have hmvt := (convex_Icc (τ1 - e.1) (τ2 - e.1)).norm_image_sub_le_of_norm_deriv_le
        (f := fun h => k h y₀ e) (C := B e) (s := Icc (τ1 - e.1) (τ2 - e.1))
        (fun c hc => (hdiff e c (by linarith [hc.1]) y₀ hy0).2)
        (fun c hc => by
          have hmem : c + e.1 ∈ Metric.ball τ₀ ε :=
            pdc_ball_Icc hτ1 hτ2 _ ⟨by linarith [hc.1], by linarith [hc.2]⟩
          have := (hbd e (c + e.1) hmem (by linarith [hc.1]) y₀ hy0).2
          rwa [add_sub_cancel_right] at this)
        (left_mem_Icc.2 (by linarith)) (right_mem_Icc.2 (by linarith))
      have hn : ‖(τ2 - e.1) - (τ1 - e.1)‖ = τ2 - τ1 := by
        rw [show (τ2 - e.1) - (τ1 - e.1) = τ2 - τ1 by ring, Real.norm_eq_abs,
          abs_of_nonneg (by linarith)]
      rw [hn] at hmvt
      rw [norm_sub_rev]
      exact hmvt.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
    · by_cases h2 : e.1 < τ2
      · rw [if_neg h1, if_pos h2, zero_sub, norm_neg]
        have hsm := pdc_small k τ₀ y₀ ε B e τ1 τ2 hτ1 hτ2 hy0 hε hdiff hlim
          (fun e' τ hτ hlt y hy => ⟨(hbd e' τ hτ hlt y hy).1, (hbd e' τ hτ hlt y hy).2⟩)
          (not_lt.1 h1) h2
        exact le_trans hsm (mul_le_mul (le_abs_self _) (by linarith [not_lt.1 h1])
          (by linarith) (abs_nonneg _))
      · rw [if_neg h1, if_neg h2, sub_self, norm_zero]
        exact mul_nonneg (abs_nonneg _) (by linarith)
  apply LipschitzOnWith.of_dist_le_mul
  intro τ1 hτ1 τ2 hτ2
  rw [Real.coe_nnabs, Real.dist_eq, dist_eq_norm]
  rcases le_total τ1 τ2 with h12 | h12
  · rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ τ2 - τ1)]
    exact aux τ1 hτ1 τ2 hτ2 h12
  · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ τ1 - τ2), norm_sub_rev]
    exact aux τ2 hτ2 τ1 hτ1 h12

lemma pdc_time (k : ℝ → Space → ℝ × Space → Space) (τ₀ : ℝ) (y₀ : Space) (ε : ℝ)
    (B : ℝ × Space → ℝ) (hε : 0 < ε) (hB : Integrable B)
    (hdiff : ∀ (e : ℝ × Space) (h : ℝ), 0 < h → ∀ y ∈ Metric.ball y₀ ε,
      ContDiffAt ℝ 2 (fun y' => k h y' e) y ∧ DifferentiableAt ℝ (fun h' => k h' y e) h)
    (hlim : ∀ e : ℝ × Space, ∀ y ∈ Metric.ball y₀ ε, Tendsto (fun h => k h y e) (𝓝[>] 0) (𝓝 0))
    (hbd : ∀ (e : ℝ × Space), ∀ τ ∈ Metric.ball τ₀ ε, e.1 < τ → ∀ y ∈ Metric.ball y₀ ε,
      ‖k (τ - e.1) y e‖ ≤ B e ∧ ‖deriv (fun h => k h y e) (τ - e.1)‖ ≤ B e)
    (hmeas0 : ∀ (τ : ℝ) (y : Space), AEStronglyMeasurable
      (fun e : ℝ × Space => if e.1 < τ then k (τ - e.1) y e else 0) volume)
    (hmeas1 : ∀ (τ : ℝ) (y : Space), AEStronglyMeasurable
      (fun e : ℝ × Space => if e.1 < τ then deriv (fun h => k h y e) (τ - e.1) else 0) volume) :
    HasDerivAt (fun τ => ∫ e : ℝ × Space, (if e.1 < τ then k (τ - e.1) y₀ e else 0))
      (∫ e : ℝ × Space, if e.1 < τ₀ then deriv (fun h => k h y₀ e) (τ₀ - e.1) else 0) τ₀ := by
  have hy0 : y₀ ∈ Metric.ball y₀ ε := Metric.mem_ball_self hε
  have hτ0 : τ₀ ∈ Metric.ball τ₀ ε := Metric.mem_ball_self hε
  have hF_int : Integrable (fun e : ℝ × Space => if e.1 < τ₀ then k (τ₀ - e.1) y₀ e else 0) volume := by
    refine Integrable.mono' hB.norm (hmeas0 τ₀ y₀) (Eventually.of_forall fun e => ?_)
    by_cases h : e.1 < τ₀
    · rw [if_pos h]
      exact (hbd e τ₀ hτ0 h y₀ hy0).1.trans (Real.le_norm_self _)
    · rw [if_neg h, norm_zero]
      exact norm_nonneg _
  have hnull : ∀ᵐ e : ℝ × Space ∂(volume : Measure (ℝ × Space)), e.1 ≠ τ₀ := by
    rw [ae_iff]
    have hset : {e : ℝ × Space | ¬ (e.1 ≠ τ₀)} = ({τ₀} : Set ℝ) ×ˢ (univ : Set Space) := by
      ext e; simp
    rw [hset, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  refine (hasDerivAt_integral_of_dominated_loc_of_lip
    (F := fun τ e => if e.1 < τ then k (τ - e.1) y₀ e else 0)
    (F' := fun e => if e.1 < τ₀ then deriv (fun h => k h y₀ e) (τ₀ - e.1) else 0)
    (bound := B) (Metric.ball_mem_nhds τ₀ hε) (Eventually.of_forall fun τ => hmeas0 τ y₀) hF_int
    (hmeas1 τ₀ y₀) (Eventually.of_forall fun e => pdc_lip k τ₀ y₀ ε B hε hdiff hlim hbd e) hB ?_).2
  refine hnull.mono (fun e he => ?_)
  by_cases h : e.1 < τ₀
  · have hd : DifferentiableAt ℝ (fun h' => k h' y₀ e) (τ₀ - e.1) :=
      (hdiff e (τ₀ - e.1) (by linarith) y₀ hy0).2
    have h1 := HasDerivAt.comp_sub_const τ₀ e.1 hd.hasDerivAt
    rw [if_pos h]
    refine h1.congr_of_eventuallyEq ?_
    exact Filter.eventually_of_mem (Ioi_mem_nhds h) (fun τ hτ => if_pos hτ)
  · have h' : τ₀ < e.1 := lt_of_le_of_ne (not_lt.1 h) (Ne.symm he)
    rw [if_neg h]
    refine (hasDerivAt_const τ₀ (0 : Space)).congr_of_eventuallyEq ?_
    exact Filter.eventually_of_mem (Iio_mem_nhds h') (fun τ hτ => if_neg (not_lt.2 (le_of_lt hτ)))


/-- First spatial derivative of the causal integral at any receiver `c` in the ball (dominated
differentiation, source 3611-3621, 4171-4186). -/
lemma pdc_space1 (k : ℝ → Space → ℝ × Space → Space) (τ₀ : ℝ) (y₀ : Space) (ε : ℝ)
    (B : ℝ × Space → ℝ) (hε : 0 < ε) (hB : Integrable B)
    (hdiff : ∀ (e : ℝ × Space) (h : ℝ), 0 < h → ∀ y ∈ Metric.ball y₀ ε,
      ContDiffAt ℝ 2 (fun y' => k h y' e) y ∧ DifferentiableAt ℝ (fun h' => k h' y e) h)
    (hbd : ∀ (e : ℝ × Space), ∀ τ ∈ Metric.ball τ₀ ε, e.1 < τ → ∀ y ∈ Metric.ball y₀ ε,
      ‖k (τ - e.1) y e‖ ≤ B e ∧ ‖fderiv ℝ (fun y' => k (τ - e.1) y' e) y‖ ≤ B e)
    (hmeas0 : ∀ (τ : ℝ) (y : Space), AEStronglyMeasurable
      (fun e : ℝ × Space => if e.1 < τ then k (τ - e.1) y e else 0) volume)
    (hmeas2 : ∀ (τ : ℝ) (y : Space), AEStronglyMeasurable
      (fun e : ℝ × Space => if e.1 < τ then fderiv ℝ (fun y' => k (τ - e.1) y' e) y else 0) volume)
    (c : Space) (hc : c ∈ Metric.ball y₀ ε) :
    HasFDerivAt (fun y => ∫ e : ℝ × Space, (if e.1 < τ₀ then k (τ₀ - e.1) y e else 0))
      (∫ e : ℝ × Space, (if e.1 < τ₀ then fderiv ℝ (fun y' => k (τ₀ - e.1) y' e) c else 0)) c := by
  have hs : Metric.ball y₀ ε ∈ 𝓝 c := Metric.isOpen_ball.mem_nhds hc
  have hτ0 : τ₀ ∈ Metric.ball τ₀ ε := Metric.mem_ball_self hε
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y e => if e.1 < τ₀ then k (τ₀ - e.1) y e else 0)
    (F' := fun y e => if e.1 < τ₀ then fderiv ℝ (fun y' => k (τ₀ - e.1) y' e) y else 0)
    (bound := fun e => ‖B e‖) hs (Eventually.of_forall fun y => hmeas0 τ₀ y) ?_
    (hmeas2 τ₀ c) ?_ hB.norm ?_
  · refine Integrable.mono' hB.norm (hmeas0 τ₀ c) (Eventually.of_forall fun e => ?_)
    by_cases h : e.1 < τ₀
    · simp only [h, ↓reduceIte]
      exact (hbd e τ₀ hτ0 h c hc).1.trans (Real.le_norm_self _)
    · simp only [h, ↓reduceIte, norm_zero]
      exact norm_nonneg _
  · refine Eventually.of_forall fun e y hy => ?_
    by_cases h : e.1 < τ₀
    · simp only [h, ↓reduceIte]
      exact (hbd e τ₀ hτ0 h y hy).2.trans (Real.le_norm_self _)
    · simp only [h, ↓reduceIte, norm_zero]
      exact norm_nonneg _
  · refine Eventually.of_forall fun e y hy => ?_
    by_cases h : e.1 < τ₀
    · simp only [h, ↓reduceIte]
      exact ((hdiff e (τ₀ - e.1) (by linarith) y hy).1.differentiableAt (by norm_num)).hasFDerivAt
    · simp only [h, ↓reduceIte]
      exact hasFDerivAt_const _ _

end UnforcedLeray.Short.PartIIIb.Concrete

end
