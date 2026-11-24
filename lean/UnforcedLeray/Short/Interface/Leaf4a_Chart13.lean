import UnforcedLeray.Short.Interface.WindowSteps2
import UnforcedLeray.Units.B0424.Calc
import UnforcedLeray.Units.B0424.Chart

/-!
# Interface: Step W1a, the chart equation (`eq:free-stress-13`)

Proves `windowChartEquationLocal : WindowChartEquationLocal` (`WindowSteps2.lean`): the free
equation `IsSourceFreeSolution` gives the chart equation `ChartEquationHolds` against every
spacetime test `Ξ`. The test is the real phase test `G(τ,y) = e^t Ξ(t, e^{t/2} y) e_i`,
`t = τ - τ₀` (`phaseScal` of `Units/B0424/Calc.lean`, times the real unit vector
`coordinateVector i`).

The argument is a change of variables. `x = e^{t/2} y` with Jacobian `e^{3t/2}`
(`integral_dilChart`) turns the chart weight `e^{-t/2}` into `e^{t}`, the weight of `L₀ᵗG`
(`L0S_phaseScal`); `τ = τ₀ + t` (`integral_shift`) turns the phase integral into the chart
integral. Source of record: `the November 2 reference manuscript` lines 1426-1431
(the chart `v(t,x) = e^{-t/2} w(τ₀+t, e^{-t/2}x)`); old manuscript `paper/main.tex` lines
7479-7491 (`eq:free-stress-13`).
Real scalar components only: the test is `Space`-valued, not `CVec3`-valued.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Cons.C08 UnforcedLeray.Parabolic
open UnforcedLeray.B0424

/-! ### Calculus for real vector tests `p ↦ f p • e` -/

theorem L4a_hasFDerivAt_slice_y (f : ℝ × Space → ℝ) (hf : Differentiable ℝ f) (t : ℝ) (y : Space) :
    HasFDerivAt (fun y' : Space => f (t, y'))
      ((fderiv ℝ f (t, y)).comp ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space))) y := by
  have key : HasFDerivAt (fun y' : Space => ((t, y') : ℝ × Space))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) y :=
    (hasFDerivAt_const t y).prodMk (hasFDerivAt_id y)
  exact (hf (t, y)).hasFDerivAt.comp y key

theorem L4a_hasFDerivAt_slice_t (f : ℝ × Space → ℝ) (hf : Differentiable ℝ f) (x : Space) (t : ℝ) :
    HasFDerivAt (fun s : ℝ => f (s, x))
      ((fderiv ℝ f (t, x)).comp ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] Space))) t := by
  have key : HasFDerivAt (fun s : ℝ => ((s, x) : ℝ × Space))
      ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] Space)) t :=
    (hasFDerivAt_id t).prodMk (hasFDerivAt_const x t)
  exact (hf (t, x)).hasFDerivAt.comp t key

theorem L4a_fderiv_slice_y (f : ℝ × Space → ℝ) (hf : Differentiable ℝ f) (t : ℝ) (y v : Space) :
    fderiv ℝ (fun y' : Space => f (t, y')) y v = fderiv ℝ f (t, y) (0, v) := by
  rw [(L4a_hasFDerivAt_slice_y f hf t y).fderiv]
  simp

theorem L4a_fderiv_slice_t (f : ℝ × Space → ℝ) (hf : Differentiable ℝ f) (x : Space) (t : ℝ) :
    fderiv ℝ (fun s : ℝ => f (s, x)) t 1 = fderiv ℝ f (t, x) (1, 0) := by
  rw [(L4a_hasFDerivAt_slice_t f hf x t).fderiv]
  simp

theorem L4a_timeDeriv_smul (f : ℝ × Space → ℝ) (hf : Differentiable ℝ f) (e : Space)
    (t : ℝ) (x : Space) :
    timeDerivative (fun p => f p • e) t x = fderiv ℝ f (t, x) (1, 0) • e := by
  unfold timeDerivative
  show fderiv ℝ (fun s : ℝ => f (s, x) • e) t 1 = _
  rw [fderiv_smul_const (L4a_hasFDerivAt_slice_t f hf x t).differentiableAt e,
    ContinuousLinearMap.smulRight_apply, L4a_fderiv_slice_t f hf x t]

theorem L4a_spatialDeriv_smul (f : ℝ × Space → ℝ) (hf : Differentiable ℝ f) (e : Space)
    (t : ℝ) (y v : Space) :
    spatialDerivative (fun p => f p • e) t y v = fderiv ℝ f (t, y) (0, v) • e := by
  unfold spatialDerivative
  show fderiv ℝ (fun y' : Space => f (t, y') • e) y v = _
  rw [fderiv_smul_const (L4a_hasFDerivAt_slice_y f hf t y).differentiableAt e,
    ContinuousLinearMap.smulRight_apply, L4a_fderiv_slice_y f hf t y v]

theorem L4a_spatialLap_smul (f : ℝ × Space → ℝ) (hf : ContDiff ℝ ∞ f) (e : Space)
    (t : ℝ) (x : Space) :
    spatialLaplacian (fun p => f p • e) t x = sLap f (t, x) • e := by
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have h2 : ∀ i : Fin 3,
      fderiv ℝ (fun y => spatialDerivative (fun p => f p • e) t y (coordinateVector i)) x
          (coordinateVector i) =
        fderiv ℝ (sD i f) (t, x) (0, coordinateVector i) • e := by
    intro i
    have hsd : Differentiable ℝ (sD i f) :=
      (UnforcedLeray.B0424.contDiff_sD hf i).differentiable (by simp)
    have hfun : (fun y => spatialDerivative (fun p => f p • e) t y (coordinateVector i)) =
        fun y => sD i f (t, y) • e :=
      funext fun y => L4a_spatialDeriv_smul f hfd e t y (coordinateVector i)
    rw [hfun, fderiv_smul_const (L4a_hasFDerivAt_slice_y (sD i f) hsd t x).differentiableAt e,
      ContinuousLinearMap.smulRight_apply,
      L4a_fderiv_slice_y (sD i f) hsd t x (coordinateVector i)]
  unfold spatialLaplacian
  rw [Finset.sum_congr rfl (fun i _ => h2 i), ← Finset.sum_smul]
  rfl

theorem L4a_inner_cv (x : Space) (i : Fin 3) : inner ℝ x (coordinateVector i) = x i := by
  simp [coordinateVector, EuclideanSpace.inner_single_right]

/-! ### The four weak-form terms of the real test `Φ e_i` -/

theorem L4a_pair (w : ℝ → SpatialField) (Φ : ℝ × Space → ℝ) (i : Fin 3) (t : ℝ) (x : Space) :
    pairTerm w (fun p => Φ p • coordinateVector i) (t, x) = Φ (t, x) * w t x i := by
  simp only [pairTerm]
  rw [real_inner_smul_right, L4a_inner_cv]

theorem L4a_temporal (w : ℝ → SpatialField) (Φ : ℝ × Space → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (i : Fin 3) (t : ℝ) (x : Space) :
    temporalTerm w (fun p => Φ p • coordinateVector i) (t, x) = tD Φ (t, x) * w t x i := by
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  simp only [temporalTerm]
  rw [L4a_timeDeriv_smul Φ hΦd (coordinateVector i) t x, real_inner_smul_right, L4a_inner_cv]
  try rfl

theorem L4a_dilation (w : ℝ → SpatialField) (Φ : ℝ × Space → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (i : Fin 3) (t : ℝ) (x : Space) :
    dilationTerm w (fun p => Φ p • coordinateVector i) (t, x) =
      (∑ j : Fin 3, x j * sD j Φ (t, x)) * w t x i := by
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  simp only [dilationTerm]
  rw [L4a_spatialDeriv_smul Φ hΦd (coordinateVector i) t x x, real_inner_smul_right,
    L4a_inner_cv, ← UnforcedLeray.B0424.sum_mul_fderiv_coord (fderiv ℝ Φ (t, x)) x]
  try rfl

theorem L4a_diffusion (w : ℝ → SpatialField) (Φ : ℝ × Space → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (i : Fin 3) (t : ℝ) (x : Space) :
    diffusionTerm w (fun p => Φ p • coordinateVector i) (t, x) = sLap Φ (t, x) * w t x i := by
  simp only [diffusionTerm]
  rw [L4a_spatialLap_smul Φ hΦ (coordinateVector i) t x, real_inner_smul_right, L4a_inner_cv]

/-- The weak mode integrand of the real phase test, pointwise:
`(μ-½)⟨w,G⟩ + ⟨𝒯₀ᵗ-part⟩ - h⟨w,ΔG⟩ = μ⟨w,G⟩ + w_i · L₀ᵗΦ`. -/
theorem L4a_weakMode (h μ : ℝ) (w : ℝ → SpatialField) (Φ : ℝ × Space → ℝ)
    (hΦ : ContDiff ℝ ∞ Φ) (i : Fin 3) (t : ℝ) (x : Space) :
    weakModeIntegrand h μ w (fun p => Φ p • coordinateVector i) (t, x) =
      μ * pairTerm w (fun p => Φ p • coordinateVector i) (t, x) +
        w t x i * L0S h Φ (t, x) := by
  unfold weakModeIntegrand driftAdjointTerm
  rw [L4a_pair w Φ i t x, L4a_temporal w Φ hΦ i t x, L4a_dilation w Φ hΦ i t x,
    L4a_diffusion w Φ hΦ i t x]
  simp only [L0S]
  ring

/-! ### The phase test and its support -/

/-- The real phase test `G(τ,y) = e^t Ξ(t, e^{t/2} y) e_i`, `t = τ - τ₀`. -/
def L4a_phaseTest (τ₀ : ℝ) (Ξ : PS 3 → ℝ) (i : Fin 3) : SpaceTime → Space :=
  fun p => phaseScal τ₀ Ξ p • coordinateVector i

theorem L4a_phaseScal_shift (τ₀ t : ℝ) (Ξ : PS 3 → ℝ) (y : Space) :
    phaseScal τ₀ Ξ (τ₀ + t, y) = Real.exp t * Ξ (t, Real.exp (t / 2) • y) := by
  show Real.exp (τ₀ + t - τ₀) * Ξ (τ₀ + t - τ₀, Real.exp ((τ₀ + t - τ₀) / 2) • y) = _
  rw [show τ₀ + t - τ₀ = t by ring]

theorem L4a_pair_test (g : ℝ → SpatialField) (τ₀ t : ℝ) (Ξ : PS 3 → ℝ) (i : Fin 3) (y : Space) :
    pairTerm g (L4a_phaseTest τ₀ Ξ i) (τ₀ + t, y) =
      Real.exp t * Ξ (t, Real.exp (t / 2) • y) * g (τ₀ + t) y i := by
  have h1 := L4a_pair g (phaseScal τ₀ Ξ) i (τ₀ + t) y
  rw [L4a_phaseScal_shift] at h1
  exact h1

theorem L4a_L0S_shift (h τ₀ t : ℝ) (Ξ : PS 3 → ℝ) (hΞ : ContDiff ℝ ∞ Ξ) (y : Space) :
    L0S h (phaseScal τ₀ Ξ) (τ₀ + t, y) = Real.exp t *
      (-(tD Ξ (t, Real.exp (t / 2) • y)) - h * Real.exp t * sLap Ξ (t, Real.exp (t / 2) • y)) := by
  rw [L0S_phaseScal τ₀ hΞ h]
  show Real.exp (τ₀ + t - τ₀) * (-(tD Ξ (τ₀ + t - τ₀, Real.exp ((τ₀ + t - τ₀) / 2) • y)) -
      h * Real.exp (τ₀ + t - τ₀) *
        sLap Ξ (τ₀ + t - τ₀, Real.exp ((τ₀ + t - τ₀) / 2) • y)) = _
  rw [show τ₀ + t - τ₀ = t by ring]

/-- If `Ξ` vanishes outside the ball of radius `R`, the phase test vanishes outside the
set `{|τ - τ₀| ≤ R} × {‖y‖ ≤ R e^{R/2}}`. -/
theorem L4a_phaseScal_zero (Ξ : PS 3 → ℝ) (R : ℝ) (hz : ∀ X : PS 3, R < ‖X‖ → Ξ X = 0)
    (τ₀ τ : ℝ) (y : Space)
    (h : R < (|τ - τ₀|) ∨ ((|τ - τ₀|) ≤ R ∧ R * Real.exp (R / 2) < ‖y‖)) :
    phaseScal τ₀ Ξ (τ, y) = 0 := by
  show Real.exp (τ - τ₀) * Ξ (τ - τ₀, Real.exp ((τ - τ₀) / 2) • y) = 0
  apply mul_eq_zero_of_right
  apply hz
  rcases h with h1 | ⟨h1, h2⟩
  · have h3 : ‖τ - τ₀‖ ≤ ‖(τ - τ₀, Real.exp ((τ - τ₀) / 2) • y)‖ :=
      norm_fst_le (τ - τ₀, Real.exp ((τ - τ₀) / 2) • y)
    have h4 : R < ‖τ - τ₀‖ := by rw [Real.norm_eq_abs]; exact h1
    linarith
  · have hA : Real.exp (-R / 2) ≤ Real.exp ((τ - τ₀) / 2) :=
      Real.exp_le_exp.2 (by linarith [(abs_le.1 h1).1])
    have hk : Real.exp (-R / 2) * Real.exp (R / 2) = 1 := by
      rw [← Real.exp_add, show -R / 2 + R / 2 = 0 by ring, Real.exp_zero]
    have h6 : Real.exp (-R / 2) * (R * Real.exp (R / 2)) < Real.exp (-R / 2) * ‖y‖ :=
      mul_lt_mul_of_pos_left h2 (Real.exp_pos _)
    have h7 : R = Real.exp (-R / 2) * (R * Real.exp (R / 2)) := by
      linear_combination (-R) * hk
    have h8 : Real.exp (-R / 2) * ‖y‖ ≤ Real.exp ((τ - τ₀) / 2) * ‖y‖ :=
      mul_le_mul_of_nonneg_right hA (norm_nonneg _)
    have h9 : R < ‖Real.exp ((τ - τ₀) / 2) • y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      linarith
    exact lt_of_lt_of_le h9 (norm_snd_le (τ - τ₀, Real.exp ((τ - τ₀) / 2) • y))

/-! ### The chart identities -/

theorem L4a_chartField_apply (τ₀ t : ℝ) (g : ℝ → SpatialField) (y : Space) (i : Fin 3) :
    chartField τ₀ g t (Real.exp (t / 2) • y) i = Real.exp (-(t / 2)) * g (τ₀ + t) y i := by
  have hk : Real.exp (-(t / 2)) • (Real.exp (t / 2) • y) = y := by
    rw [smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]
  unfold chartField
  rw [hk]
  simp

/-- The chart LHS integrand, pointwise after `x = e^{t/2} y` (weight `e^{3t/2} e^{-t/2} = e^t`). -/
theorem L4a_chart_lhs (h τ₀ t : ℝ) (w : ℝ → SpatialField) (Ξ : PS 3 → ℝ) (i : Fin 3) (y : Space) :
    Real.exp (3 * t / 2) • (chartField τ₀ w t (Real.exp (t / 2) • y) i *
        (-(tD Ξ (t, Real.exp (t / 2) • y)) - h * Real.exp t * sLap Ξ (t, Real.exp (t / 2) • y))) =
      w (τ₀ + t) y i * (Real.exp t *
        (-(tD Ξ (t, Real.exp (t / 2) • y)) - h * Real.exp t * sLap Ξ (t, Real.exp (t / 2) • y))) := by
  have hexp : Real.exp (3 * t / 2) * Real.exp (-(t / 2)) = Real.exp t := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [L4a_chartField_apply τ₀ t w y i, smul_eq_mul]
  linear_combination (w (τ₀ + t) y i *
    (-(tD Ξ (t, Real.exp (t / 2) • y)) - h * Real.exp t * sLap Ξ (t, Real.exp (t / 2) • y))) * hexp

/-- The chart RHS integrand, pointwise: `e^{3t/2} · (-(f + μw))(chart) · Ξ = -(μ⟨w,G⟩ + ⟨f,G⟩)`. -/
theorem L4a_chart_rhs (μ τ₀ t : ℝ) (w f : ℝ → SpatialField) (Ξ : PS 3 → ℝ) (i : Fin 3)
    (y : Space) :
    Real.exp (3 * t / 2) • ((-(chartField τ₀ f t (Real.exp (t / 2) • y) i +
        μ * chartField τ₀ w t (Real.exp (t / 2) • y) i)) * Ξ (t, Real.exp (t / 2) • y)) =
      -(μ * (Real.exp t * Ξ (t, Real.exp (t / 2) • y) * w (τ₀ + t) y i) +
        Real.exp t * Ξ (t, Real.exp (t / 2) • y) * f (τ₀ + t) y i) := by
  have hexp : Real.exp (3 * t / 2) * Real.exp (-(t / 2)) = Real.exp t := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [L4a_chartField_apply τ₀ t f y i, L4a_chartField_apply τ₀ t w y i, smul_eq_mul]
  linear_combination (-(f (τ₀ + t) y i + μ * w (τ₀ + t) y i) *
    Ξ (t, Real.exp (t / 2) • y)) * hexp

/-! ### Main step -/

theorem windowChartEquationLocal : WindowChartEquationLocal := by
  unfold WindowChartEquationLocal ChartEquationHolds
  intro h μ P w f τ₀ i hh hP hw hf hfree Ξ hΞ
  obtain ⟨hΞs, hΞc⟩ := hΞ
  unfold IsSourceFreeSolution at hfree
  obtain ⟨hint, hsol⟩ := hfree
  have hΦs : ContDiff ℝ ∞ (phaseScal τ₀ Ξ) := contDiff_phaseScal τ₀ hΞs
  -- support of Ξ inside a ball of radius R
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : PS 3)).1 hΞc.isCompact.isBounded
  have hzeroΞ : ∀ X : PS 3, R < ‖X‖ → Ξ X = 0 := by
    intro X hX
    by_contra hne
    have hmem : X ∈ tsupport Ξ := subset_tsupport _ (Function.mem_support.2 hne)
    have h2 := hR hmem
    rw [Metric.mem_closedBall, dist_zero_right] at h2
    linarith
  have hK : IsCompact
      (Icc (τ₀ - R) (τ₀ + R) ×ˢ Metric.closedBall (0 : Space) (R * Real.exp (R / 2))) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hΦzero : ∀ z : SpaceTime,
      z ∉ (Icc (τ₀ - R) (τ₀ + R) ×ˢ Metric.closedBall (0 : Space) (R * Real.exp (R / 2))) →
        phaseScal τ₀ Ξ z = 0 := by
    rintro ⟨τ, y⟩ hz
    apply L4a_phaseScal_zero Ξ R hzeroΞ τ₀ τ y
    by_cases hle : (|τ - τ₀|) ≤ R
    · right
      refine ⟨hle, ?_⟩
      by_contra hc
      apply hz
      have hτ : τ ∈ Icc (τ₀ - R) (τ₀ + R) :=
        ⟨by linarith [(abs_le.1 hle).1], by linarith [(abs_le.1 hle).2]⟩
      exact Set.mk_mem_prod hτ (mem_closedBall_zero_iff.2 (not_lt.1 hc))
    · exact Or.inl (not_le.1 hle)
  have hsm : ContDiff ℝ ∞ (L4a_phaseTest τ₀ Ξ i) := by
    unfold L4a_phaseTest
    exact hΦs.smul contDiff_const
  have hsupp : HasCompactSupport (L4a_phaseTest τ₀ Ξ i) :=
    HasCompactSupport.intro hK (fun z hz => by simp [L4a_phaseTest, hΦzero z hz])
  have hG : IsSimilarityTest (L4a_phaseTest τ₀ Ξ i) := ⟨hsm, hsupp⟩
  obtain ⟨hA, hT, hDil, hDiff, hF⟩ := hint _ hG
  have hEq := hsol _ hG
  -- pointwise: the weak integrand splits as μ⟨w,G⟩ + w_i L₀ᵗΦ
  have hpt : ∀ z : SpaceTime,
      weakModeIntegrand h μ w (L4a_phaseTest τ₀ Ξ i) z =
        μ * pairTerm w (L4a_phaseTest τ₀ Ξ i) z + w z.1 z.2 i * L0S h (phaseScal τ₀ Ξ) z := by
    rintro ⟨t, x⟩
    exact L4a_weakMode h μ w (phaseScal τ₀ Ξ) hΦs i t x
  have hWint : Integrable
      (fun z : SpaceTime => weakModeIntegrand h μ w (L4a_phaseTest τ₀ Ξ i) z) := by
    have hdrift : Integrable (fun z : SpaceTime => -temporalTerm w (L4a_phaseTest τ₀ Ξ i) z +
        (3 / 2 : ℝ) * pairTerm w (L4a_phaseTest τ₀ Ξ i) z +
        (1 / 2 : ℝ) * dilationTerm w (L4a_phaseTest τ₀ Ξ i) z) :=
      ((hT.neg).add (hA.const_mul (3 / 2 : ℝ))).add (hDil.const_mul (1 / 2 : ℝ))
    exact ((hA.const_mul (μ - 1 / 2)).add hdrift).sub (hDiff.const_mul h)
  have hBint : Integrable (fun z : SpaceTime => w z.1 z.2 i * L0S h (phaseScal τ₀ Ξ) z) := by
    refine (hWint.sub (hA.const_mul μ)).congr (Eventually.of_forall fun z => ?_)
    simp only [Pi.sub_apply, hpt z]
    ring
  have hsplit : (∫ z : SpaceTime, weakModeIntegrand h μ w (L4a_phaseTest τ₀ Ξ i) z) =
      μ * (∫ z : SpaceTime, pairTerm w (L4a_phaseTest τ₀ Ξ i) z) +
        ∫ z : SpaceTime, w z.1 z.2 i * L0S h (phaseScal τ₀ Ξ) z := by
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_add (hA.const_mul μ) hBint,
      integral_const_mul]
  -- right side: change of variables x = e^{t/2} y, then τ = τ₀ + t
  have hR : (∫ X : PS 3, (-(chartField τ₀ f X.1 X.2 i + μ * chartField τ₀ w X.1 X.2 i)) * Ξ X) =
      -(μ * (∫ z : SpaceTime, pairTerm w (L4a_phaseTest τ₀ Ξ i) z) +
        ∫ z : SpaceTime, pairTerm f (L4a_phaseTest τ₀ Ξ i) z) := by
    calc (∫ X : PS 3, (-(chartField τ₀ f X.1 X.2 i + μ * chartField τ₀ w X.1 X.2 i)) * Ξ X)
        = ∫ p : SpaceTime, Real.exp (3 * p.1 / 2) •
            ((-(chartField τ₀ f (dilChart p).1 (dilChart p).2 i +
              μ * chartField τ₀ w (dilChart p).1 (dilChart p).2 i)) * Ξ (dilChart p)) :=
          integral_dilChart _
      _ = ∫ p : SpaceTime, -(μ * pairTerm w (L4a_phaseTest τ₀ Ξ i) (τ₀ + p.1, p.2) +
            pairTerm f (L4a_phaseTest τ₀ Ξ i) (τ₀ + p.1, p.2)) := by
          congr 1
          funext p
          obtain ⟨t, y⟩ := p
          dsimp only
          rw [L4a_pair_test w τ₀ t Ξ i y, L4a_pair_test f τ₀ t Ξ i y]
          exact L4a_chart_rhs μ τ₀ t w f Ξ i y
      _ = ∫ z : SpaceTime, -(μ * pairTerm w (L4a_phaseTest τ₀ Ξ i) z +
            pairTerm f (L4a_phaseTest τ₀ Ξ i) z) :=
          integral_shift τ₀ (fun z : SpaceTime => -(μ * pairTerm w (L4a_phaseTest τ₀ Ξ i) z +
            pairTerm f (L4a_phaseTest τ₀ Ξ i) z))
      _ = -(μ * (∫ z : SpaceTime, pairTerm w (L4a_phaseTest τ₀ Ξ i) z) +
            ∫ z : SpaceTime, pairTerm f (L4a_phaseTest τ₀ Ξ i) z) := by
          rw [integral_neg, integral_add (hA.const_mul μ) hF, integral_const_mul]
  -- left side: x = e^{t/2} y, then τ = τ₀ + t
  have hL : (∫ X : PS 3, chartField τ₀ w X.1 X.2 i * (-(tD Ξ X) - h * Real.exp X.1 * sLap Ξ X)) =
      ∫ z : SpaceTime, w z.1 z.2 i * L0S h (phaseScal τ₀ Ξ) z := by
    calc (∫ X : PS 3, chartField τ₀ w X.1 X.2 i * (-(tD Ξ X) - h * Real.exp X.1 * sLap Ξ X))
        = ∫ p : SpaceTime, Real.exp (3 * p.1 / 2) •
            (chartField τ₀ w (dilChart p).1 (dilChart p).2 i *
              (-(tD Ξ (dilChart p)) - h * Real.exp (dilChart p).1 * sLap Ξ (dilChart p))) :=
          integral_dilChart _
      _ = ∫ p : SpaceTime, w (τ₀ + p.1) p.2 i * L0S h (phaseScal τ₀ Ξ) (τ₀ + p.1, p.2) := by
          congr 1
          funext p
          obtain ⟨t, y⟩ := p
          dsimp only
          rw [L4a_L0S_shift h τ₀ t Ξ hΞs y]
          exact L4a_chart_lhs h τ₀ t w Ξ i y
      _ = ∫ z : SpaceTime, w z.1 z.2 i * L0S h (phaseScal τ₀ Ξ) z :=
          integral_shift τ₀ (fun z : SpaceTime => w z.1 z.2 i * L0S h (phaseScal τ₀ Ξ) z)
  -- the free equation, tested against G
  have key : (∫ z : SpaceTime, w z.1 z.2 i * L0S h (phaseScal τ₀ Ξ) z) =
      -(μ * (∫ z : SpaceTime, pairTerm w (L4a_phaseTest τ₀ Ξ i) z) +
        ∫ z : SpaceTime, pairTerm f (L4a_phaseTest τ₀ Ξ i) z) := by
    linarith [hsplit, hEq]
  exact hL.trans (key.trans hR.symm)

end UnforcedLeray.Short.Interface
