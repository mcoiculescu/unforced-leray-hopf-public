import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.DiffContOnCl

/-!
# Holomorphic dependence of parameter integrals (INF20 T20.2, general part)

Blueprint target INF20 T20.2 (scoping note `INF19-INF20-INF29-INF30-Algebra.md`, §5 Level 3).
Mathlib has no lemma "an integrand holomorphic in a parameter, with a locally uniform integrable
majorant, has a holomorphic integral" (scoping note §3, INF20 coverage). This file proves it:

* `hasDerivAt_integral_of_holomorphic`: the derivative exists at `z₀` and is the integral of the
  parameter derivative, given a majorant on one ball around `z₀`;
* `differentiableOn_integral_of_holomorphic`: holomorphy on an open set from local majorants;
* `differentiableOn_integral_of_compact_majorant`: the form used by the manuscript, a majorant on
  every compact subset (tex 1994, unit B0131: "On every compact subset of that half-plane, the
  same integrable majorants accommodate all factors |log θ|^m. Differentiation under the
  integral proves holomorphy"; tex 6884–6892, unit B0374; tex 6922–6933, unit B0379);
* `differentiableOn_integral_of_dominated`: one global majorant.

The derivative bound is Cauchy's estimate (`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`)
on circles of radius `ε / 4`, so no bound on the parameter derivative is assumed. The
measurability of the parameter derivative is proved as an a.e. limit of difference quotients.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric Topology

namespace UnforcedLeray.Special

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The parameter derivative of an a.e. holomorphic family of a.e.-strongly measurable functions
is a.e.-strongly measurable: it is the a.e. limit of difference quotients along `z₀ + h n`,
`h n → 0`, `h n ≠ 0`, `z₀ + h n ∈ U` (INF20 T20.2). -/
theorem aestronglyMeasurable_deriv_param {U : Set ℂ} (hU : IsOpen U) {F : ℂ → α → E}
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (F z) μ)
    (hF : ∀ᵐ x ∂μ, DifferentiableOn ℂ (fun z => F z x) U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    AEStronglyMeasurable (fun x => deriv (fun z => F z x) z₀) μ := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  set h : ℕ → ℂ := fun n => (((r / 2) / ((n : ℝ) + 1) : ℝ) : ℂ) with hh_def
  have hpos : ∀ n : ℕ, 0 < (r / 2) / ((n : ℝ) + 1) := fun n => by positivity
  have hne : ∀ n, h n ≠ 0 := fun n => by
    simp only [hh_def, ne_eq, Complex.ofReal_eq_zero]
    exact (hpos n).ne'
  have hlim : Tendsto h atTop (𝓝 0) := by
    have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (r / 2)
    rw [mul_zero] at h1
    have h1' : Tendsto (fun n : ℕ => (r / 2) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      h1.congr fun n => by ring
    have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1'
    rw [Complex.ofReal_zero] at h2
    exact h2
  have hh0 : Tendsto h atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hne⟩
  have hmem : ∀ n, z₀ + h n ∈ U := fun n => by
    apply hball
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hh_def, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (hpos n)]
    calc (r / 2) / ((n : ℝ) + 1) ≤ r / 2 := div_le_self (by positivity) (by
            have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
            linarith)
      _ < r := half_lt_self hr
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n x => (h n)⁻¹ • (F (z₀ + h n) x - F z₀ x))
    (fun n => ((hmeas _ (hmem n)).sub (hmeas _ hz₀)).const_smul _) ?_
  filter_upwards [hF] with x hx
  have hd : HasDerivAt (fun z => F z x) (deriv (fun z => F z x) z₀) z₀ :=
    ((hx z₀ hz₀).differentiableAt (hU.mem_nhds hz₀)).hasDerivAt
  exact hd.tendsto_slope_zero.comp hh0

/-- **Differentiation under the integral for holomorphic integrands** (INF20 T20.2).
If `F z` is a.e.-strongly measurable for `z ∈ U`, `z ↦ F z x` is holomorphic on the open set `U`
for a.e. `x`, and `‖F z x‖ ≤ H x` on a ball `ball z₀ ε ⊆ U` with `H` integrable, then
`z ↦ ∫ F z x dμ` has complex derivative `∫ ∂_z F z₀ x dμ` at `z₀`. -/
theorem hasDerivAt_integral_of_holomorphic {U : Set ℂ} (hU : IsOpen U) {F : ℂ → α → E}
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (F z) μ)
    (hF : ∀ᵐ x ∂μ, DifferentiableOn ℂ (fun z => F z x) U)
    {z₀ : ℂ} {ε : ℝ} (hε : 0 < ε) (hεU : ball z₀ ε ⊆ U) {H : α → ℝ} (hH : Integrable H μ)
    (hbd : ∀ᵐ x ∂μ, ∀ z ∈ ball z₀ ε, ‖F z x‖ ≤ H x) :
    HasDerivAt (fun z => ∫ x, F z x ∂μ) (∫ x, deriv (fun z => F z x) z₀ ∂μ) z₀ := by
  have hz₀ : z₀ ∈ U := hεU (mem_ball_self hε)
  have hF_meas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (F z) μ :=
    eventually_of_mem (hU.mem_nhds hz₀) hmeas
  have hF_int : Integrable (F z₀) μ :=
    hH.mono' (hmeas z₀ hz₀) (hbd.mono fun x hx => hx z₀ (mem_ball_self hε))
  have hF'_meas := aestronglyMeasurable_deriv_param hU hmeas hF hz₀
  have hr : 0 < ε / 4 := by positivity
  have h_bound : ∀ᵐ x ∂μ, ∀ z ∈ ball z₀ (ε / 2),
      ‖deriv (fun w => F w x) z‖ ≤ H x / (ε / 4) := by
    filter_upwards [hF, hbd] with x hx hxb
    intro z hz
    have hsub : closedBall z (ε / 4) ⊆ ball z₀ ε := by
      intro w hw
      rw [mem_closedBall] at hw
      rw [mem_ball] at hz ⊢
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ < ε := by linarith
    have hdc : DiffContOnCl ℂ (fun w => F w x) (ball z (ε / 4)) :=
      hx.diffContOnCl_ball (hsub.trans hεU)
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdc fun w hw => ?_
    exact hxb w (hsub (sphere_subset_closedBall hw))
  have h_diff : ∀ᵐ x ∂μ, ∀ z ∈ ball z₀ (ε / 2),
      HasDerivAt (fun w => F w x) (deriv (fun w => F w x) z) z := by
    filter_upwards [hF] with x hx
    intro z hz
    have hzU : z ∈ U := hεU (ball_subset_ball (by linarith) hz)
    exact ((hx z hzU).differentiableAt (hU.mem_nhds hzU)).hasDerivAt
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds z₀ (half_pos hε))
    hF_meas hF_int hF'_meas h_bound (hH.div_const _) h_diff).2

/-- **Holomorphy of parameter integrals from local majorants** (INF20 T20.2). -/
theorem differentiableOn_integral_of_holomorphic {U : Set ℂ} (hU : IsOpen U) {F : ℂ → α → E}
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (F z) μ)
    (hF : ∀ᵐ x ∂μ, DifferentiableOn ℂ (fun z => F z x) U)
    (hloc : ∀ z₀ ∈ U, ∃ ε > 0, ∃ H : α → ℝ, Integrable H μ ∧
      ∀ᵐ x ∂μ, ∀ z ∈ ball z₀ ε, ‖F z x‖ ≤ H x) :
    DifferentiableOn ℂ (fun z => ∫ x, F z x ∂μ) U := by
  intro z₀ hz₀
  obtain ⟨ε, hε, H, hH, hbd⟩ := hloc z₀ hz₀
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  have hη : 0 < min ε δ := lt_min hε hδ
  have hηU : ball z₀ (min ε δ) ⊆ U := (ball_subset_ball (min_le_right _ _)).trans hδU
  have hbd' : ∀ᵐ x ∂μ, ∀ z ∈ ball z₀ (min ε δ), ‖F z x‖ ≤ H x :=
    hbd.mono fun x hx z hz => hx z (ball_subset_ball (min_le_left _ _) hz)
  exact (hasDerivAt_integral_of_holomorphic hU hmeas hF hη hηU hH hbd').differentiableAt
    |>.differentiableWithinAt

/-- **Holomorphy of parameter integrals from compact majorants** (INF20 T20.2; the hypothesis
form of tex 1994, B0131: an integrable majorant on every compact subset of `U`). -/
theorem differentiableOn_integral_of_compact_majorant {U : Set ℂ} (hU : IsOpen U)
    {F : ℂ → α → E} (hmeas : ∀ z ∈ U, AEStronglyMeasurable (F z) μ)
    (hF : ∀ᵐ x ∂μ, DifferentiableOn ℂ (fun z => F z x) U)
    (hK : ∀ K ⊆ U, IsCompact K → ∃ H : α → ℝ, Integrable H μ ∧
      ∀ᵐ x ∂μ, ∀ z ∈ K, ‖F z x‖ ≤ H x) :
    DifferentiableOn ℂ (fun z => ∫ x, F z x ∂μ) U := by
  refine differentiableOn_integral_of_holomorphic hU hmeas hF fun z₀ hz₀ => ?_
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  have hsub : closedBall z₀ (δ / 2) ⊆ U :=
    (closedBall_subset_ball (half_lt_self hδ)).trans hδU
  obtain ⟨H, hH, hbd⟩ := hK _ hsub (isCompact_closedBall z₀ (δ / 2))
  exact ⟨δ / 2, half_pos hδ, H, hH, hbd.mono fun x hx z hz => hx z (ball_subset_closedBall hz)⟩

/-- **Holomorphy of parameter integrals from one global majorant** (INF20 T20.2, the signature
proposed in the scoping note, with the majorant bound required a.e. uniformly in `z ∈ U`). -/
theorem differentiableOn_integral_of_dominated {U : Set ℂ} (hU : IsOpen U) {F : ℂ → α → E}
    {H : α → ℝ} (hH : Integrable H μ) (hmeas : ∀ z ∈ U, AEStronglyMeasurable (F z) μ)
    (hF : ∀ᵐ x ∂μ, DifferentiableOn ℂ (fun z => F z x) U)
    (hbd : ∀ᵐ x ∂μ, ∀ z ∈ U, ‖F z x‖ ≤ H x) :
    DifferentiableOn ℂ (fun z => ∫ x, F z x ∂μ) U :=
  differentiableOn_integral_of_compact_majorant hU hmeas hF fun _ hKU _ =>
    ⟨H, hH, hbd.mono fun _ hx z hz => hx z (hKU hz)⟩

end UnforcedLeray.Special
