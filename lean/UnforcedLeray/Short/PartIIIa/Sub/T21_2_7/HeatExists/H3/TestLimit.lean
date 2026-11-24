import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.LeavesOf
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H1.HeatMoment
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_2_Smooth.Basic
import UnforcedLeray.Lib.HeatCylinder.HeatKernelAgeIntegrable
import UnforcedLeray.Units.B0592
import UnforcedLeray.Units.B0289.Semigroup
import UnforcedLeray.Units.B0284.Contraction

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8/3/1`: (H3.1) the heat flow of a test converges at age zero

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836
and 3044-3050.  Statement: `HeatExists/Leaves.lean` (`AdjHeatS0TestLimit`).

Route: for a complexified cylinder test `g` (periodic, smooth, bounded, globally Lipschitz) the
periodic lift is `g` itself, so `e^{ντΔ} g x - g x = ∫ G_{ντ}(y) (g(x - y) - g x) dy` (the kernel
has unit mass).  The Lipschitz bound and the Gaussian first moment
`∫ G_θ(y) (|y₁| + |y₂|) dy = 2 √θ A₁` (scaling, `adjHM_heatKernel_scale`) give the uniform bound
`|e^{ντΔ} g x - g x| ≤ L · 2 A₁ √(ντ)`.  The cell measure is finite for `m > 1`, so the `L²`
norm is bounded by a constant times `√(ντ) → 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The first absolute moment constant of the unit-diffusivity one-dimensional heat kernel. -/
def tlA1 : ℝ := ∫ u : ℝ, |u| * UnforcedLeray.B0191.heatKernel 1 1 u

theorem tl_h1_nonneg {θ : ℝ} (hθ : 0 < θ) (s : ℝ) :
    0 ≤ UnforcedLeray.B0191.heatKernel 1 θ s :=
  (UnforcedLeray.B0191.heatKernel_pos one_pos hθ s).le

/-- Scaling of the first absolute moment: `∫ |s| G_θ(s) ds = √θ · A₁`. -/
theorem tl_abs_scale {θ : ℝ} (hθ : 0 < θ) :
    ∫ s : ℝ, |s| * UnforcedLeray.B0191.heatKernel 1 θ s = Real.sqrt θ * tlA1 := by
  set r : ℝ := Real.sqrt θ with hr_def
  have hr : 0 < r := Real.sqrt_pos.2 hθ
  have hr2 : r ^ 2 = θ := Real.sq_sqrt hθ.le
  have hscale : ∀ u : ℝ, UnforcedLeray.B0191.heatKernel 1 θ (r * u) =
      r⁻¹ * UnforcedLeray.B0191.heatKernel 1 1 u := by
    intro u
    have h := adjHM_heatKernel_scale (ν := 1) (r := r) one_pos hr u
    rw [one_mul, hr2] at h
    exact h
  have hF : ∀ u : ℝ, |r * u| * UnforcedLeray.B0191.heatKernel 1 θ (r * u) =
      |u| * UnforcedLeray.B0191.heatKernel 1 1 u := by
    intro u
    rw [abs_mul, abs_of_pos hr, hscale u]
    linear_combination (|u| * UnforcedLeray.B0191.heatKernel 1 1 u) * (mul_inv_cancel₀ hr.ne')
  have hint := MeasureTheory.Measure.integral_comp_mul_left
    (fun s : ℝ => |s| * UnforcedLeray.B0191.heatKernel 1 θ s) r
  simp only [hF] at hint
  rw [abs_inv, abs_of_pos hr, smul_eq_mul] at hint
  rw [tlA1, hint, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]

/-- The weighted one-dimensional heat kernel `|s| G_θ(s)` is integrable. -/
theorem tl_abs_heat_integrable {θ : ℝ} (hθ : 0 < θ) :
    Integrable (fun s : ℝ => |s| * UnforcedLeray.B0191.heatKernel 1 θ s) := by
  have h0 : Integrable (fun s : ℝ => UnforcedLeray.B0191.heatKernel 1 θ s) :=
    UnforcedLeray.B0289.integrable_heatKernel1 hθ
  have h2 : Integrable (fun s : ℝ => s ^ 2 * UnforcedLeray.B0191.heatKernel 1 θ s) :=
    UnforcedLeray.HeatCylinder.integrable_sq_mul_heatKernel1 hθ
  refine Integrable.mono' ((h0.add h2).const_mul (1 / 2)) ?_ ?_
  · exact continuous_abs.aestronglyMeasurable.mul h0.aestronglyMeasurable
  · refine Eventually.of_forall fun s => ?_
    have hp : 0 ≤ UnforcedLeray.B0191.heatKernel 1 θ s := tl_h1_nonneg hθ s
    have hs : |s| ≤ (1 + s ^ 2) / 2 := by nlinarith [sq_abs s, sq_nonneg (|s| - 1)]
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg s) hp)]
    simp only [Pi.add_apply]
    nlinarith [mul_le_mul_of_nonneg_right hs hp]

theorem tl_norm_le_abs_add (z : ℝ × ℝ) : ‖z‖ ≤ |z.1| + |z.2| := by
  rw [Prod.norm_def]
  exact max_le (by rw [Real.norm_eq_abs]; linarith [abs_nonneg z.2])
    (by rw [Real.norm_eq_abs]; linarith [abs_nonneg z.1])

/-- The first-moment majorant `G_θ(y) (|y₁| + |y₂|)` is integrable. -/
theorem tl_majA_integrable {θ : ℝ} (hθ : 0 < θ) :
    Integrable (fun y : ℝ × ℝ => (|y.1| * UnforcedLeray.B0191.heatKernel 1 θ y.1) *
      UnforcedLeray.B0191.heatKernel 1 θ y.2) ((volume : Measure ℝ).prod volume) :=
  (tl_abs_heat_integrable hθ).mul_prod (UnforcedLeray.B0289.integrable_heatKernel1 hθ)

theorem tl_majB_integrable {θ : ℝ} (hθ : 0 < θ) :
    Integrable (fun y : ℝ × ℝ => UnforcedLeray.B0191.heatKernel 1 θ y.1 *
      (|y.2| * UnforcedLeray.B0191.heatKernel 1 θ y.2)) ((volume : Measure ℝ).prod volume) :=
  (UnforcedLeray.B0289.integrable_heatKernel1 hθ).mul_prod (tl_abs_heat_integrable hθ)

theorem tl_majorant_integrable {θ : ℝ} (hθ : 0 < θ) :
    Integrable (fun y : ℝ × ℝ => UnforcedLeray.B0284.heatKernel2 θ y * (|y.1| + |y.2|)) := by
  rw [Measure.volume_eq_prod]
  refine ((tl_majA_integrable hθ).add (tl_majB_integrable hθ)).congr
    (Eventually.of_forall fun y => ?_)
  simp only [Pi.add_apply, UnforcedLeray.B0284.heatKernel2]
  ring

/-- The first-moment integral of the planar Gaussian: `∫ G_θ(y)(|y₁| + |y₂|) dy = 2 √θ A₁`. -/
theorem tl_majorant_integral {θ : ℝ} (hθ : 0 < θ) :
    ∫ y : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ y * (|y.1| + |y.2|) =
      2 * (Real.sqrt θ * tlA1) := by
  have hfun : (fun y : ℝ × ℝ => UnforcedLeray.B0284.heatKernel2 θ y * (|y.1| + |y.2|)) =
      fun y : ℝ × ℝ => (|y.1| * UnforcedLeray.B0191.heatKernel 1 θ y.1) *
          UnforcedLeray.B0191.heatKernel 1 θ y.2 +
        UnforcedLeray.B0191.heatKernel 1 θ y.1 *
          (|y.2| * UnforcedLeray.B0191.heatKernel 1 θ y.2) := by
    funext y
    simp only [UnforcedLeray.B0284.heatKernel2]
    ring
  have e1 : ∫ z : ℝ × ℝ, (|z.1| * UnforcedLeray.B0191.heatKernel 1 θ z.1) *
      UnforcedLeray.B0191.heatKernel 1 θ z.2 ∂((volume : Measure ℝ).prod volume) =
      (∫ s : ℝ, |s| * UnforcedLeray.B0191.heatKernel 1 θ s) *
        ∫ s : ℝ, UnforcedLeray.B0191.heatKernel 1 θ s :=
    integral_prod_mul (fun s : ℝ => |s| * UnforcedLeray.B0191.heatKernel 1 θ s)
      (fun s : ℝ => UnforcedLeray.B0191.heatKernel 1 θ s)
  have e2 : ∫ z : ℝ × ℝ, UnforcedLeray.B0191.heatKernel 1 θ z.1 *
      (|z.2| * UnforcedLeray.B0191.heatKernel 1 θ z.2) ∂((volume : Measure ℝ).prod volume) =
      (∫ s : ℝ, UnforcedLeray.B0191.heatKernel 1 θ s) *
        ∫ s : ℝ, |s| * UnforcedLeray.B0191.heatKernel 1 θ s :=
    integral_prod_mul (fun s : ℝ => UnforcedLeray.B0191.heatKernel 1 θ s)
      (fun s : ℝ => |s| * UnforcedLeray.B0191.heatKernel 1 θ s)
  rw [hfun, Measure.volume_eq_prod, integral_add (tl_majA_integrable hθ) (tl_majB_integrable hθ),
    e1, e2, tl_abs_scale hθ, UnforcedLeray.B0284.integral_heatKernel_one hθ]
  ring

/-- Lipschitz bound for a real cylinder test. -/
theorem tl_real_lip {c : ℝ} (hc : 0 < c) {ψ : ℝ × ℝ → ℝ} (hψ : UnforcedLeray.B0579.IsCylTest c ψ) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ a b : ℝ × ℝ, |ψ a - ψ b| ≤ N * ‖a - b‖ := by
  obtain ⟨N, hN, hb⟩ := Exist.cylTest_exists_fderiv_bound hc hψ
  refine ⟨N, hN, fun a b => ?_⟩
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (f := ψ) (s := univ) (x := b) (y := a)
    (fun x _ => hψ.differentiable x) (fun x _ => hb x) convex_univ
    (mem_univ _) (mem_univ _)
  simpa [Real.norm_eq_abs] using h

theorem tl_cplx_norm (a b : ℝ) : ‖(a : ℂ) + Complex.I * (b : ℂ)‖ ≤ |a| + |b| := by
  calc ‖(a : ℂ) + Complex.I * (b : ℂ)‖ ≤ ‖(a : ℂ)‖ + ‖Complex.I * (b : ℂ)‖ := norm_add_le _ _
    _ = |a| + |b| := by simp [norm_mul]

/-- The finiteness of the cell measure with density `⟨x⟩^{-2m}` for `m > 1`. -/
theorem tl_cell_finite {c m : ℝ} (hm : 1 < m) :
    UnforcedLeray.B0579.cellMeasure c (-m) Set.univ < ⊤ := by
  rw [UnforcedLeray.B0579.cellMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  calc ∫⁻ x, (UnforcedLeray.B0579.density (-m) x : ℝ≥0∞)
        ∂(volume.restrict (UnforcedLeray.B0579.cell c))
      ≤ ∫⁻ x, ENNReal.ofReal (UnforcedLeray.B0579.jb x ^ (-m)) :=
        lintegral_mono' Measure.restrict_le_self (fun x => le_of_eq rfl)
    _ < ⊤ := (UnforcedLeray.B0592.integrable_jb_rpow_neg hm).lintegral_lt_top

/-- **Pointwise bound.** For `g` continuous, bounded and `L`-Lipschitz, the Gaussian average
minus `g x` is bounded by `L · 2 A₁ √(ντ)`. -/
theorem tl_point_bound {ν τ : ℝ} (hθ : 0 < ν * τ) {g : ℝ × ℝ → ℂ} (hcont : Continuous g)
    {B L : ℝ} (hB : ∀ y, ‖g y‖ ≤ B) (hL0 : 0 ≤ L)
    (hL : ∀ a b, ‖g a - g b‖ ≤ L * ‖a - b‖) (x : ℝ × ℝ) :
    ‖(∫ y, ((adjHeatKer ν τ (x - y) : ℝ) : ℂ) * g y) - g x‖ ≤
      L * (2 * (Real.sqrt (ν * τ) * tlA1)) := by
  have hGnn : ∀ y, 0 ≤ adjHeatKer ν τ y := fun y => adjHeatKer_nonneg hθ y
  have hGi : Integrable (fun y => adjHeatKer ν τ y) :=
    UnforcedLeray.B0284.integrable_heatKernel2 hθ
  have hG1 : ∫ y, adjHeatKer ν τ y = 1 := UnforcedLeray.B0284.integral_heatKernel2 hθ
  have hGC : Integrable (fun y => ((adjHeatKer ν τ y : ℝ) : ℂ)) := hGi.ofReal
  have hmaj : Integrable (fun y => adjHeatKer ν τ y * (L * (|y.1| + |y.2|))) := by
    refine ((tl_majorant_integrable hθ).const_mul L).congr (Eventually.of_forall fun y => ?_)
    simp only [adjHeatKer, UnforcedLeray.B0284.heatKernel2]
    ring
  have hval : ∫ y, adjHeatKer ν τ y * (|y.1| + |y.2|) = 2 * (Real.sqrt (ν * τ) * tlA1) :=
    tl_majorant_integral hθ
  -- change of variables `y ↦ x - y`
  have hsub : ∫ y, ((adjHeatKer ν τ (x - y) : ℝ) : ℂ) * g y =
      ∫ y, ((adjHeatKer ν τ y : ℝ) : ℂ) * g (x - y) := by
    have h := integral_sub_left_eq_self
      (fun y : ℝ × ℝ => ((adjHeatKer ν τ (x - y) : ℝ) : ℂ) * g y) volume x
    simp only [sub_sub_cancel] at h
    exact h.symm
  have hI1 : Integrable (fun y => ((adjHeatKer ν τ y : ℝ) : ℂ) * g (x - y)) := by
    refine Integrable.mono' (hGi.mul_const B) ?_ (Eventually.of_forall fun y => ?_)
    · exact ((Complex.continuous_ofReal.comp (continuous_adjHeatKer ν τ)).mul
        (hcont.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hGnn y)]
      exact mul_le_mul_of_nonneg_left (hB _) (hGnn y)
  have hI2 : Integrable (fun y => ((adjHeatKer ν τ y : ℝ) : ℂ) * g x) := hGC.mul_const (g x)
  have hint1 : ∫ y, ((adjHeatKer ν τ y : ℝ) : ℂ) * g x = g x := by
    rw [integral_mul_const, integral_complex_ofReal, hG1]
    simp
  have hdiff : (∫ y, ((adjHeatKer ν τ y : ℝ) : ℂ) * g (x - y)) - g x =
      ∫ y, ((adjHeatKer ν τ y : ℝ) : ℂ) * (g (x - y) - g x) := by
    have h : ∫ y, ((adjHeatKer ν τ y : ℝ) : ℂ) * (g (x - y) - g x) =
        (∫ y, ((adjHeatKer ν τ y : ℝ) : ℂ) * g (x - y)) -
          ∫ y, ((adjHeatKer ν τ y : ℝ) : ℂ) * g x := by
      rw [← integral_sub hI1 hI2]
      congr 1
      funext y
      ring
    rw [h, hint1]
  rw [hsub, hdiff]
  calc ‖∫ y, ((adjHeatKer ν τ y : ℝ) : ℂ) * (g (x - y) - g x)‖
      ≤ ∫ y, ‖((adjHeatKer ν τ y : ℝ) : ℂ) * (g (x - y) - g x)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y, adjHeatKer ν τ y * (L * (|y.1| + |y.2|)) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _) hmaj
          (Eventually.of_forall fun y => ?_)
        dsimp only
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hGnn y)]
        have h1 : ‖(x - y) - x‖ ≤ |y.1| + |y.2| := by
          rw [sub_sub_cancel_left, norm_neg]
          exact tl_norm_le_abs_add y
        have h2 : ‖g (x - y) - g x‖ ≤ L * (|y.1| + |y.2|) :=
          (hL _ _).trans (mul_le_mul_of_nonneg_left h1 hL0)
        exact mul_le_mul_of_nonneg_left h2 (hGnn y)
    _ = L * (2 * (Real.sqrt (ν * τ) * tlA1)) := by
        rw [show (fun y : ℝ × ℝ => adjHeatKer ν τ y * (L * (|y.1| + |y.2|))) =
            fun y : ℝ × ℝ => L * (adjHeatKer ν τ y * (|y.1| + |y.2|)) from
              funext fun y => by ring, integral_const_mul, hval]

/-- The heat flow of a periodic, continuous, bounded, Lipschitz function converges in the
weighted `L²` norm of the cell at age zero. -/
theorem tl_limit_of_props {ν c m : ℝ} (hν : 0 < ν) (hc : 0 < c) (hm : 1 < m) {g : ℝ × ℝ → ℂ}
    (hper : ∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x) (hcont : Continuous g) {B L : ℝ}
    (hB : ∀ y, ‖g y‖ ≤ B) (hL0 : 0 ≤ L) (hL : ∀ a b, ‖g a - g b‖ ≤ L * ‖a - b‖) :
    Tendsto (fun τ => eLpNorm (fun x => adjS0Fun ν c τ g x - g x) 2
      (UnforcedLeray.B0579.cellMeasure c (-m))) (𝓝[>] 0) (𝓝 0) := by
  set μ := UnforcedLeray.B0579.cellMeasure c (-m) with hμ
  have hfin : μ Set.univ < ⊤ := tl_cell_finite hm
  have hpt : ∀ τ : ℝ, 0 < τ → ∀ x : ℝ × ℝ,
      ‖adjS0Fun ν c τ g x - g x‖ ≤ L * (2 * tlA1) * Real.sqrt (ν * τ) := by
    intro τ hτ x
    have hθ : 0 < ν * τ := mul_pos hν hτ
    have hrw : adjS0Fun ν c τ g x = ∫ y, ((adjHeatKer ν τ (x - y) : ℝ) : ℂ) * g y := by
      unfold adjS0Fun
      rw [perRep_eq_self_of_periodic hc hper]
    rw [hrw]
    have h := tl_point_bound hθ hcont hB hL0 hL x
    calc _ ≤ L * (2 * (Real.sqrt (ν * τ) * tlA1)) := h
      _ = L * (2 * tlA1) * Real.sqrt (ν * τ) := by ring
  have ha : μ Set.univ ^ (ENNReal.toReal 2)⁻¹ ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) hfin.ne
  have hcont0 : Tendsto (fun τ : ℝ => L * (2 * tlA1) * Real.sqrt (ν * τ)) (𝓝[>] 0) (𝓝 0) := by
    have h : Continuous (fun τ : ℝ => L * (2 * tlA1) * Real.sqrt (ν * τ)) := by fun_prop
    have h0 := (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using h0
  have hE := ENNReal.tendsto_ofReal hcont0
  rw [ENNReal.ofReal_zero] at hE
  have hU := ENNReal.Tendsto.const_mul hE (Or.inr ha)
  rw [mul_zero] at hU
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU ?_ ?_
  · exact Eventually.of_forall fun τ => zero_le
  · filter_upwards [eventually_mem_nhdsWithin] with τ hτ
    exact eLpNorm_le_of_ae_bound (Eventually.of_forall fun x => hpt τ (Set.mem_Ioi.1 hτ) x)

/-- **(H3.1) The heat flow of a test converges to it** (SP 2819-2836): for a complexified
cylinder test `g = ψ₁ + iψ₂`, `e^{ντΔ} g → g` in `X_{-m,c}` as `τ → 0+`. -/
theorem adjHeatS0TestLimit (m : ℝ) (hm : 8 < m) : AdjHeatS0TestLimit m := by
  intro ν c hν hc g hg
  obtain ⟨ψ₁, ψ₂, h₁, h₂, rfl⟩ := hg
  obtain ⟨M₁, hM₁, hb₁⟩ := Exist.cylTest_exists_bound hc h₁
  obtain ⟨M₂, hM₂, hb₂⟩ := Exist.cylTest_exists_bound hc h₂
  obtain ⟨N₁, hN₁, hl₁⟩ := tl_real_lip hc h₁
  obtain ⟨N₂, hN₂, hl₂⟩ := tl_real_lip hc h₂
  refine tl_limit_of_props (B := M₁ + M₂) (L := N₁ + N₂) hν hc (by linarith) ?_ ?_ ?_
    (by linarith) ?_
  · intro x
    simp only [h₁.periodic, h₂.periodic]
  · exact (Complex.continuous_ofReal.comp h₁.continuous).add
      (continuous_const.mul (Complex.continuous_ofReal.comp h₂.continuous))
  · intro y
    refine le_trans (tl_cplx_norm _ _) ?_
    linarith [hb₁ y, hb₂ y]
  · intro a b
    have e : ((ψ₁ a : ℝ) : ℂ) + Complex.I * ((ψ₂ a : ℝ) : ℂ) -
        (((ψ₁ b : ℝ) : ℂ) + Complex.I * ((ψ₂ b : ℝ) : ℂ)) =
        ((ψ₁ a - ψ₁ b : ℝ) : ℂ) + Complex.I * ((ψ₂ a - ψ₂ b : ℝ) : ℂ) := by
      push_cast
      ring
    show ‖((ψ₁ a : ℝ) : ℂ) + Complex.I * ((ψ₂ a : ℝ) : ℂ) -
        (((ψ₁ b : ℝ) : ℂ) + Complex.I * ((ψ₂ b : ℝ) : ℂ))‖ ≤ (N₁ + N₂) * ‖a - b‖
    rw [e, add_mul]
    refine le_trans (tl_cplx_norm _ _) ?_
    linarith [hl₁ a b, hl₂ a b]

end UnforcedLeray.Short.IIIa
