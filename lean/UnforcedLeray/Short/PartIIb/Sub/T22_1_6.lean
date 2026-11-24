import UnforcedLeray.Short.PartIIb.Sub.T22_1.Stages

/-!
# `PartII-b:T22/1/6`: differentiation under the integral sign for `e^{aΔ} g`

Source `the November 2 reference manuscript`, lines 2074-2093, 2103-2105

`HeatKernelMoments` (task `T22/1/3`) and two kernel-only leaves:

* `HeatKdDominated`: a locally uniform integrable majorant of `|∂_i K_a (x - y)|`;
* `HeatKHasFDeriv`: the Fréchet derivative of `x ↦ K_a(x - y)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric

namespace UnforcedLeray.Short.IIb.CylPDE

/-- The linear map `v ↦ v₁ ∂₀K_a(z) + v₂ ∂₁K_a(z)` (the gradient of `K_a` at `z`). -/
def heatKdCLM (a : ℝ) (z : Pl) : Pl →L[ℝ] ℝ :=
  heatKd 0 a z • ContinuousLinearMap.fst ℝ ℝ ℝ + heatKd 1 a z • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- **Leaf K1** (local Gaussian majorant; source lines 2103-2105). For `a > 0`, `i`, and `x₀`
there is an integrable `G` with `|∂_i K_a(x - y)| ≤ G(y)` for all `x` within `1` of `x₀` and all
`y`. Sketch: `|∂_i K_a(z)| ≤ (|z|/(2a)) K_a(z)` and `|x - y| ≥ |x₀ - y| - 1`; take
`G(y) = C (1 + |x₀ - y|) exp(-(max(|x₀ - y| - 1, 0))²/(4a))`, integrable (Gaussian moments). -/
def HeatKdDominated : Prop :=
  ∀ a : ℝ, 0 < a → ∀ (i : Fin 2) (x₀ : Pl), ∃ G : Pl → ℝ, Integrable G ∧
    ∀ x ∈ ball x₀ 1, ∀ y : Pl, |heatKd i a (x - y)| ≤ G y

/-- **Leaf K2** (derivative of the kernel; source lines 2103-2105). `x ↦ K_a(x - y)` has Fréchet
derivative `heatKdCLM a (x - y)` (chain rule on `exp(-(z₁² + z₂²)/(4a))`; `heatKd i a z =
-z_i/(2a) K_a(z)`). -/
def HeatKHasFDeriv : Prop :=
  ∀ a : ℝ, 0 < a → ∀ x y : Pl, HasFDerivAt (fun x : Pl => heatK a (x - y)) (heatKdCLM a (x - y)) x

theorem heatGradFormula_of (hM : HeatKernelMoments) (h1 : HeatKdDominated)
    (h2 : HeatKHasFDeriv) : HeatGradFormula := by
  intro B g hgc hg a ha
  have hgB : ∀ y, |g y| ≤ B := fun y =>
    le_trans (le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_cosh _)) (hg y)
  have hKint : ∀ x : Pl, Integrable (fun y : Pl => heatK a (x - y)) := fun x =>
    ((hM a ha).2.1).comp_sub_left x
  have hKc : Continuous (heatK a) := by
    unfold heatK; fun_prop
  have hKdc : ∀ i, Continuous (heatKd i a) := by
    intro i; unfold heatKd
    have : Continuous (fun z : Pl => (![z.1, z.2] : Fin 2 → ℝ) i) := by
      fin_cases i <;> simp <;> fun_prop
    exact (this.neg.div_const _).mul hKc
  have hnorm : ∀ z : Pl, ‖heatKdCLM a z‖ ≤ |heatKd 0 a z| + |heatKd 1 a z| := by
    intro z
    unfold heatKdCLM
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ)
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ)
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hgB 0)
  have hsubc : ∀ x : Pl, Continuous (fun y : Pl => x - y) := fun x =>
    continuous_const.sub continuous_id
  have hFc : ∀ x : Pl, Continuous (fun y : Pl => g y • heatKdCLM a (x - y)) := by
    intro x
    unfold heatKdCLM
    exact hgc.smul ((((hKdc 0).comp (hsubc x)).smul continuous_const).add
      (((hKdc 1).comp (hsubc x)).smul continuous_const))
  have hdc : ∀ (i : Fin 2) (x : Pl), Continuous (fun y : Pl => heatKd i a (x - y) * g y) :=
    fun i x => ((hKdc i).comp (hsubc x)).mul hgc
  have hdint : ∀ (i : Fin 2) (x : Pl), Integrable (fun y : Pl => heatKd i a (x - y) * g y) := by
    intro i x
    obtain ⟨G, hG, hb⟩ := h1 a ha i x
    refine Integrable.mono' (hG.const_mul B) (hdc i x).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |heatKd i a (x - y)| * |g y| ≤ G y * B :=
          mul_le_mul (hb x (mem_ball_self one_pos) y) (hgB y) (abs_nonneg _)
            (le_trans (abs_nonneg _) (hb x (mem_ball_self one_pos) y))
      _ = B * G y := mul_comm _ _
  have hderiv : ∀ x₀ : Pl, HasFDerivAt (heatSG a g)
      (∫ y : Pl, g y • heatKdCLM a (x₀ - y)) x₀ := by
    intro x₀
    have hfun : heatSG a g = fun x => ∫ y : Pl, heatK a (x - y) * g y := by
      funext x; simp [heatSG, not_le.mpr ha]
    rw [hfun]
    obtain ⟨G0, hG0, hb0⟩ := h1 a ha 0 x₀
    obtain ⟨G1, hG1, hb1⟩ := h1 a ha 1 x₀
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := ball x₀ 1)
      (F := fun x y => heatK a (x - y) * g y)
      (F' := fun x y => g y • heatKdCLM a (x - y))
      (bound := fun y => B * (G0 y + G1 y)) (ball_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun x =>
        ((hKc.comp (hsubc x)).mul hgc).aestronglyMeasurable
    · refine Integrable.mono' ((hKint x₀).const_mul B)
        ((hKc.comp (hsubc x₀)).mul hgc).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by unfold heatK; positivity)]
      calc heatK a (x₀ - y) * |g y| ≤ heatK a (x₀ - y) * B :=
            mul_le_mul_of_nonneg_left (hgB y) (by unfold heatK; positivity)
        _ = B * heatK a (x₀ - y) := mul_comm _ _
    · exact (hFc x₀).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun y x hx => ?_
      calc ‖g y • heatKdCLM a (x - y)‖ = |g y| * ‖heatKdCLM a (x - y)‖ := by
            rw [norm_smul, Real.norm_eq_abs]
        _ ≤ B * (|heatKd 0 a (x - y)| + |heatKd 1 a (x - y)|) :=
              mul_le_mul (hgB y) (hnorm _) (norm_nonneg _) hB0
        _ ≤ B * (G0 y + G1 y) :=
              mul_le_mul_of_nonneg_left (add_le_add (hb0 x hx y) (hb1 x hx y)) hB0
    · exact (hG0.add hG1).const_mul B
    · refine Filter.Eventually.of_forall fun y x _ => ?_
      exact (h2 a ha x y).mul_const (g y)
  have hdiff : Differentiable ℝ (heatSG a g) := fun x => (hderiv x).differentiableAt
  have happly : ∀ (x : Pl) (v : Pl), fderiv ℝ (heatSG a g) x v
      = v.1 * heatSGd 0 a g x + v.2 * heatSGd 1 a g x := by
    intro x v
    rw [(hderiv x).fderiv]
    have hint : Integrable (fun y : Pl => g y • heatKdCLM a (x - y)) := by
      obtain ⟨G0, hG0, hb0⟩ := h1 a ha 0 x
      obtain ⟨G1, hG1, hb1⟩ := h1 a ha 1 x
      refine Integrable.mono' ((hG0.add hG1).const_mul B) (hFc x).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => ?_)
      have hx : x ∈ ball x 1 := mem_ball_self one_pos
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul (hgB y) (hnorm _) (norm_nonneg _) hB0).trans
        (mul_le_mul_of_nonneg_left (add_le_add (hb0 x hx y) (hb1 x hx y)) hB0)
    have := (ContinuousLinearMap.apply ℝ ℝ v).integral_comp_comm hint
    simp only [ContinuousLinearMap.apply_apply] at this
    rw [← this]
    have hpt : ∀ y : Pl, (g y • heatKdCLM a (x - y)) v
        = v.1 * (heatKd 0 a (x - y) * g y) + v.2 * (heatKd 1 a (x - y) * g y) := by
      intro y
      simp [heatKdCLM]
      ring
    simp_rw [hpt]
    rw [integral_add ((hdint 0 x).const_mul _) ((hdint 1 x).const_mul _),
      integral_const_mul, integral_const_mul]
    rfl
  refine ⟨hdiff, ?_, ?_⟩
  · intro i x
    fin_cases i
    · simp [B0579.pd, B0579.dir, happly]
    · simp [B0579.pd, B0579.dir, happly]
  · intro i
    rw [continuous_iff_continuousAt]
    intro x₀
    obtain ⟨G, hG, hb⟩ := h1 a ha i x₀
    refine continuousAt_of_dominated (bound := fun y => B * G y) ?_ ?_ (hG.const_mul B) ?_
    · exact Filter.Eventually.of_forall fun x => (hdc i x).aestronglyMeasurable
    · filter_upwards [ball_mem_nhds x₀ one_pos] with x hx
      refine Filter.Eventually.of_forall fun y => ?_
      rw [Real.norm_eq_abs, abs_mul]
      calc |heatKd i a (x - y)| * |g y| ≤ G y * B :=
            mul_le_mul (hb x hx y) (hgB y) (abs_nonneg _)
              (le_trans (abs_nonneg _) (hb x hx y))
        _ = B * G y := mul_comm _ _
    · exact Filter.Eventually.of_forall fun y =>
        (((hKdc i).comp (continuous_id.sub continuous_const)).mul continuous_const).continuousAt

end UnforcedLeray.Short.IIb.CylPDE
