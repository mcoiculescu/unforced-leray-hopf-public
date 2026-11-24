import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_7_5_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.HeatDeriv

/-!
# Part II-b, task `PartII-b:T12/7/5/1/1` (`DeqpdJointDeriv`): differentiation under the integral

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
For `s > t`, `s' ↦ ∫ K_{ν(s'-t)}(w) Ψ_i(s', z-w) dw` is differentiated under the integral
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le` on `ball s ((s-t)/2)`). The age variable
`θ = ν(s'-t)` stays in `(θ₀/2, 2θ₀)` with `θ₀ = ν(s-t)`, which gives the Gaussian majorant
`|∂_θ K_θ(w)| ≤ A (1+|w|²) K_{2θ₀}(w)` and the kernel comparison `K_θ ≤ 4 K_{2θ₀}`.
Helpers use the prefix `djd`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Age derivative of the flat kernel at a positive age (`flatHeatKernel = heatKernel2` for
positive age). -/
theorem djd_flat_hasDerivAt {θ : ℝ} (hθ : 0 < θ) (w : ℝ × ℝ) :
    HasDerivAt (fun τ : ℝ => flatHeatKernel τ w)
      (UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ w) θ := by
  refine (UnforcedLeray.HeatCylinder.hasDerivAt_heatKernel2_age hθ w).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hθ] with τ hτ
  exact flatHeat_kernel_eq hτ w

/-- Derivative of the slice `a ↦ Φ(a, p)` of a differentiable function on `Coord`. -/
theorem djd_slice_hasDerivAt (Φ : Coord → ℝ) (hΦ : Differentiable ℝ Φ) (a : ℝ) (p : ℝ × ℝ) :
    HasDerivAt (fun y : ℝ => Φ (y, p)) (cpd 0 Φ (a, p)) a := by
  have hf : HasDerivAt (fun y : ℝ => ((y, p) : Coord)) ((1 : ℝ), (0 : ℝ × ℝ)) a :=
    (hasDerivAt_id' a).prodMk (hasDerivAt_const a p)
  exact (hΦ (a, p)).hasFDerivAt.comp_hasDerivAt a hf

/-- Nonnegativity of the constant `4 (θ₀⁻² + 2/θ₀)` of the age-derivative majorant. -/
theorem djd_A_nonneg {θ₀ : ℝ} (hθ₀ : 0 < θ₀) : 0 ≤ 4 * (θ₀⁻¹ ^ 2 + 2 / θ₀) := by
  positivity

/-- Kernel comparison: `K_θ(w) ≤ 4 K_{2θ₀}(w)` for `θ₀/2 < θ < 2θ₀` (radial formula). -/
theorem djd_kernel_le {θ₀ θ : ℝ} (hθ₀ : 0 < θ₀) (hlo : θ₀ / 2 < θ) (hhi : θ < 2 * θ₀)
    (w : ℝ × ℝ) :
    UnforcedLeray.B0284.heatKernel2 θ w ≤ 4 * UnforcedLeray.B0284.heatKernel2 (2 * θ₀) w := by
  have hθ : 0 < θ := by linarith
  have h2 : 0 < 2 * θ₀ := by linarith
  rw [UnforcedLeray.HeatCylinder.heatKernel2_eq_radial hθ w,
    UnforcedLeray.HeatCylinder.heatKernel2_eq_radial h2 w]
  have hR : 0 ≤ w.1 ^ 2 + w.2 ^ 2 := by positivity
  have he : (w.1 ^ 2 + w.2 ^ 2) / (4 * (2 * θ₀)) ≤ (w.1 ^ 2 + w.2 ^ 2) / (4 * θ) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_nonneg hR (show (0 : ℝ) ≤ 2 * θ₀ - θ by linarith)]
  have hE : Real.exp (-((w.1 ^ 2 + w.2 ^ 2) / (4 * θ))) ≤
      Real.exp (-((w.1 ^ 2 + w.2 ^ 2) / (4 * (2 * θ₀)))) :=
    Real.exp_le_exp.2 (neg_le_neg he)
  have hP : (4 * Real.pi * θ)⁻¹ ≤ (2 * Real.pi * θ₀)⁻¹ := by
    rw [inv_le_inv₀ (by positivity : (0 : ℝ) < 4 * Real.pi * θ)
      (by positivity : (0 : ℝ) < 2 * Real.pi * θ₀)]
    nlinarith [Real.pi_pos, hlo]
  calc (4 * Real.pi * θ)⁻¹ * Real.exp (-((w.1 ^ 2 + w.2 ^ 2) / (4 * θ)))
      ≤ (2 * Real.pi * θ₀)⁻¹ * Real.exp (-((w.1 ^ 2 + w.2 ^ 2) / (4 * (2 * θ₀)))) :=
        mul_le_mul hP hE (Real.exp_nonneg _) (inv_nonneg.2 (by positivity))
    _ = 4 * ((4 * Real.pi * (2 * θ₀))⁻¹ *
          Real.exp (-((w.1 ^ 2 + w.2 ^ 2) / (4 * (2 * θ₀))))) := by
        ring

/-- **Task `PartII-b:T12/7/5/1/1`**: differentiation of `s ↦ ∫ K_{ν(s-t)}(w) Ψ_i(s, z-w) dw`
(SP 1923-1927). -/
theorem deqpdJointDeriv : UnforcedLeray.Short.IIb.DeqpdJointDeriv := by
  intro ν t hν Ψ hΨ i s hts z
  have hΦ : ContDiff ℝ ∞ (fun x : Coord => Ψ x i) := (hΨ.smooth i).smooth
  have hΦc : HasCompactSupport (fun x : Coord => Ψ x i) := (hΨ.smooth i).compact
  have hΦd : Differentiable ℝ (fun x : Coord => Ψ x i) := hΦ.differentiable (by simp)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x : Coord, ‖Ψ x i‖ ≤ M :=
    hΦ.continuous.bounded_above_of_compact_support hΦc
  have hD0 : Continuous (fun x : Coord => cpd 0 (fun y => Ψ y i) x) := by
    unfold cpd
    exact (hΦ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hD0c : HasCompactSupport (fun x : Coord => cpd 0 (fun y => Ψ y i) x) :=
    hΦc.fderiv_apply ℝ (cdir 0)
  obtain ⟨M₁, hM₁⟩ : ∃ M₁ : ℝ, ∀ x : Coord, ‖cpd 0 (fun y => Ψ y i) x‖ ≤ M₁ :=
    hD0.bounded_above_of_compact_support hD0c
  have hθ₀ : 0 < ν * (s - t) := mul_pos hν (sub_pos.2 hts)
  have h2 : 0 < 2 * (ν * (s - t)) := by linarith
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 4 * ((ν * (s - t))⁻¹ ^ 2 + 2 / (ν * (s - t))) := ⟨_, rfl⟩
  have hAnn : 0 ≤ A := by
    rw [hA]
    exact djd_A_nonneg hθ₀
  have hmem : ∀ x ∈ Metric.ball s ((s - t) / 2),
      ν * (s - t) / 2 < ν * (x - t) ∧ ν * (x - t) < 2 * (ν * (s - t)) := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff] at hx
    obtain ⟨h1, h2'⟩ := hx
    constructor
    · nlinarith [mul_pos hν (show (0 : ℝ) < x - t - (s - t) / 2 by linarith)]
    · nlinarith [mul_pos hν (show (0 : ℝ) < 2 * (s - t) - (x - t) by linarith)]
  have hsmem : Metric.ball s ((s - t) / 2) ∈ 𝓝 s := Metric.ball_mem_nhds s (by linarith)
  have hpath : ∀ x : ℝ, Continuous (fun w : ℝ × ℝ => ((x, z - w) : Coord)) :=
    fun x => continuous_const.prodMk (continuous_const.sub continuous_id)
  have hΨc : ∀ x : ℝ, Continuous (fun w : ℝ × ℝ => Ψ (x, z - w) i) :=
    fun x => hΦ.continuous.comp (hpath x)
  have hD0w : ∀ x : ℝ, Continuous (fun w : ℝ × ℝ => cpd 0 (fun y => Ψ y i) (x, z - w)) :=
    fun x => hD0.comp (hpath x)
  have hKint : Integrable (fun w : ℝ × ℝ => flatHeatKernel (ν * (s - t)) w) :=
    (UnforcedLeray.B0284.integrable_heatKernel2 hθ₀).congr
      (ae_of_all _ fun w => (flatHeat_kernel_eq hθ₀ w).symm)
  have hF_meas : ∀ᶠ x in 𝓝 s, AEStronglyMeasurable
      (fun w : ℝ × ℝ => flatHeatKernel (ν * (x - t)) w * Ψ (x, z - w) i) volume := by
    filter_upwards [hsmem] with x hx
    have hθx : 0 < ν * (x - t) := by linarith [(hmem x hx).1]
    exact (((deqhdK_cont hθx.ne').congr
      (fun w => (flatHeat_kernel_eq hθx w).symm)).mul (hΨc x)).aestronglyMeasurable
  have hF_int : Integrable (fun w : ℝ × ℝ => flatHeatKernel (ν * (s - t)) w * Ψ (s, z - w) i) :=
    hKint.mul_bdd (hΨc s).aestronglyMeasurable (ae_of_all _ fun w => hM (s, z - w))
  have hF'_meas : AEStronglyMeasurable (fun w : ℝ × ℝ =>
      ν * (UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative (ν * (s - t)) w * Ψ (s, z - w) i) +
        flatHeatKernel (ν * (s - t)) w * cpd 0 (fun y => Ψ y i) (s, z - w)) volume :=
    (((UnforcedLeray.HeatCylinder.integrable_heatKernel2AgeDerivative hθ₀).aestronglyMeasurable.mul
      (hΨc s).aestronglyMeasurable).const_mul ν).add
      (hKint.aestronglyMeasurable.mul (hD0w s).aestronglyMeasurable)
  have bound_int : Integrable (fun w : ℝ × ℝ =>
      (ν * A * M) * ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * (ν * (s - t))) w) +
        (4 * M₁) * UnforcedLeray.B0284.heatKernel2 (2 * (ν * (s - t))) w) :=
    ((UnforcedLeray.HeatCylinder.integrable_one_add_sq_mul_heatKernel2 h2).const_mul (ν * A * M)).add
      ((UnforcedLeray.B0284.integrable_heatKernel2 h2).const_mul (4 * M₁))
  have h_bound : ∀ᵐ w ∂(volume : Measure (ℝ × ℝ)), ∀ x ∈ Metric.ball s ((s - t) / 2),
      ‖ν * (UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative (ν * (x - t)) w * Ψ (x, z - w) i) +
        flatHeatKernel (ν * (x - t)) w * cpd 0 (fun y => Ψ y i) (x, z - w)‖ ≤
        (ν * A * M) * ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * (ν * (s - t))) w) +
          (4 * M₁) * UnforcedLeray.B0284.heatKernel2 (2 * (ν * (s - t))) w := by
    refine ae_of_all _ fun w x hx => ?_
    obtain ⟨h1, h3⟩ := hmem x hx
    have hθx : 0 < ν * (x - t) := by linarith
    have hage : |UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative (ν * (x - t)) w| ≤
        A * ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * (ν * (s - t))) w) := by
      rw [hA]
      exact UnforcedLeray.HeatCylinder.abs_heatKernel2AgeDerivative_le_local hθ₀ h1 h3 w
    have hK2 : UnforcedLeray.B0284.heatKernel2 (ν * (x - t)) w ≤
        4 * UnforcedLeray.B0284.heatKernel2 (2 * (ν * (s - t))) w :=
      djd_kernel_le hθ₀ h1 h3 w
    have hKnn : 0 ≤ UnforcedLeray.B0284.heatKernel2 (ν * (x - t)) w :=
      UnforcedLeray.B0284.heatKernel2_nonneg hθx w
    have hK2nn : 0 ≤ UnforcedLeray.B0284.heatKernel2 (2 * (ν * (s - t))) w :=
      UnforcedLeray.B0284.heatKernel2_nonneg h2 w
    have hQ : 0 ≤ (1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * (ν * (s - t))) w :=
      mul_nonneg (by positivity) hK2nn
    have hAQ : 0 ≤ A * ((1 + w.1 ^ 2 + w.2 ^ 2) *
        UnforcedLeray.B0284.heatKernel2 (2 * (ν * (s - t))) w) := mul_nonneg hAnn hQ
    have hΨb : |Ψ (x, z - w) i| ≤ M := by
      rw [← Real.norm_eq_abs]
      exact hM (x, z - w)
    have hC0 : |cpd 0 (fun y => Ψ y i) (x, z - w)| ≤ M₁ := by
      rw [← Real.norm_eq_abs]
      exact hM₁ (x, z - w)
    have hn1 : ‖UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative (ν * (x - t)) w *
        Ψ (x, z - w) i‖ ≤
        A * ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * (ν * (s - t))) w) * M := by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul hage hΨb (abs_nonneg _) hAQ
    have hn0 : ‖ν * (UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative (ν * (x - t)) w *
        Ψ (x, z - w) i)‖ ≤
        ν * (A * ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * (ν * (s - t))) w) * M) := by
      rw [norm_mul, Real.norm_of_nonneg hν.le]
      exact mul_le_mul_of_nonneg_left hn1 hν.le
    have hn2 : ‖flatHeatKernel (ν * (x - t)) w * cpd 0 (fun y => Ψ y i) (x, z - w)‖ ≤
        4 * UnforcedLeray.B0284.heatKernel2 (2 * (ν * (s - t))) w * M₁ := by
      rw [flatHeat_kernel_eq hθx w, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hKnn]
      exact mul_le_mul hK2 hC0 (abs_nonneg _) (mul_nonneg (by norm_num) hK2nn)
    have e : ν * (A * ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * (ν * (s - t))) w) * M) +
        4 * UnforcedLeray.B0284.heatKernel2 (2 * (ν * (s - t))) w * M₁ =
        (ν * A * M) * ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * (ν * (s - t))) w) +
          (4 * M₁) * UnforcedLeray.B0284.heatKernel2 (2 * (ν * (s - t))) w := by
      ring
    refine (norm_add_le _ _).trans ?_
    linarith [hn0, hn2, e]
  have h_diff : ∀ᵐ w ∂(volume : Measure (ℝ × ℝ)), ∀ x ∈ Metric.ball s ((s - t) / 2),
      HasDerivAt (fun x' : ℝ => flatHeatKernel (ν * (x' - t)) w * Ψ (x', z - w) i)
        (ν * (UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative (ν * (x - t)) w * Ψ (x, z - w) i) +
          flatHeatKernel (ν * (x - t)) w * cpd 0 (fun y => Ψ y i) (x, z - w)) x := by
    refine ae_of_all _ fun w x hx => ?_
    have hθx : 0 < ν * (x - t) := by linarith [(hmem x hx).1]
    have hlin : HasDerivAt (fun y : ℝ => ν * (y - t)) ν x := by
      simpa using ((hasDerivAt_id' x).sub_const t).const_mul ν
    have hK0 := (djd_flat_hasDerivAt hθx w).comp x hlin
    have hK : HasDerivAt (fun y : ℝ => flatHeatKernel (ν * (y - t)) w)
        (UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative (ν * (x - t)) w * ν) x := hK0
    have hP : HasDerivAt (fun y : ℝ => Ψ (y, z - w) i)
        (cpd 0 (fun u => Ψ u i) (x, z - w)) x :=
      djd_slice_hasDerivAt (fun u => Ψ u i) hΦd x (z - w)
    exact (hK.mul hP).congr_deriv (by ring)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure (ℝ × ℝ))) (x₀ := s) (s := Metric.ball s ((s - t) / 2))
    (F := fun x w => flatHeatKernel (ν * (x - t)) w * Ψ (x, z - w) i)
    (F' := fun x w => ν * (UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative (ν * (x - t)) w *
        Ψ (x, z - w) i) + flatHeatKernel (ν * (x - t)) w * cpd 0 (fun y => Ψ y i) (x, z - w))
    (bound := fun w => (ν * A * M) * ((1 + w.1 ^ 2 + w.2 ^ 2) *
        UnforcedLeray.B0284.heatKernel2 (2 * (ν * (s - t))) w) +
        (4 * M₁) * UnforcedLeray.B0284.heatKernel2 (2 * (ν * (s - t))) w)
    hsmem hF_meas hF_int hF'_meas h_bound bound_int h_diff
  exact key.2

end UnforcedLeray.Short.IIb
