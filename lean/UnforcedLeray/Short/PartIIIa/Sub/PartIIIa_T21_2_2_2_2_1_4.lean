import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_2_1

/-!
# `PartIII-a:T21/2/2/2/2/1/4`: weighted product rule, decomposition

Source: `the November 2 reference manuscript` (SP) lines 3060-3073.

`WeightedProductRule` is the differentiation of `r ↦ ∫ w(r,x) ‖f(r,x)‖² dμ`.  The proof is the
slope formulation: `slope F r r' = ∫ S_{r'}` with `S_{r'} = (r'-r)⁻¹ (w(r')‖f(r')‖² - w(r)‖f(r)‖²)`,
and `∫ S_{r'} → ∫ D` follows from `tendsto_integral_of_L1` once `D` and the integrands are
integrable and `∫⁻ ‖S_{r'} - D‖ₑ → 0`.  The two leaves below are exactly those facts.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.E0

/-- The hypotheses of `WeightedProductRule` (identical to the statement's). -/
def WPRHyp (μ : Measure (ℝ × ℝ)) (w : ℝ → ℝ × ℝ → ℝ) (f : ℝ → ℝ × ℝ → ℂ) (f' : ℝ × ℝ → ℂ)
    (r : ℝ) : Prop :=
  (∀ r', Measurable (w r')) ∧ (∀ᶠ r' in 𝓝 r, AEStronglyMeasurable (f r') μ) ∧
    (∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ x : ℝ × ℝ, ∀ r' ∈ ball r δ,
      DifferentiableAt ℝ (fun q => w q x) r' ∧ 0 ≤ w r' x ∧ w r' x ≤ C * w r x ∧
      |deriv (fun q => w q x) r'| ≤ C * w r x) ∧
    (∀ x : ℝ × ℝ, HasDerivAt (fun q => f q x) (f' x) r) ∧
    Tendsto (fun r' => ∫⁻ x, ENNReal.ofReal (w r x) *
        ‖(r' - r)⁻¹ • (f r' x - f r x) - f' x‖ₑ ^ 2 ∂μ) (𝓝[≠] r) (𝓝 0) ∧
    (∫⁻ x, ENNReal.ofReal (w r x) * ‖f r x‖ₑ ^ 2 ∂μ) < ⊤ ∧
    (∫⁻ x, ENNReal.ofReal (w r x) * ‖f' x‖ₑ ^ 2 ∂μ) < ⊤

/-- **Leaf (integrability)**: the derivative integrand and the energy integrands (at `r` and at
`r'` near `r`) are integrable.  `D = ∂_r w ‖f‖² + 2 w Re(conj f f')`: `|∂_r w| ≤ C w` and weighted
Cauchy-Schwarz; for `r'` near `r`, `w(r') ≤ C w(r)` and `‖f(r')‖² ≤ 2‖f(r)‖² + 2 h²‖Q_h‖²`. -/
def WPRInteg : Prop :=
  ∀ (μ : Measure (ℝ × ℝ)) (w : ℝ → ℝ × ℝ → ℝ) (f : ℝ → ℝ × ℝ → ℂ) (f' : ℝ × ℝ → ℂ) (r : ℝ),
    WPRHyp μ w f f' r →
    Integrable (fun x => deriv (fun q => w q x * ‖f q x‖ ^ 2) r) μ ∧
    Integrable (fun x => w r x * ‖f r x‖ ^ 2) μ ∧
    (∀ᶠ r' in 𝓝[≠] r, Integrable (fun x => w r' x * ‖f r' x‖ ^ 2) μ)

/-- **Leaf (L¹ convergence of the slopes)**:
`∫⁻ ‖(r'-r)⁻¹ (w(r')‖f(r')‖² - w(r)‖f(r)‖²) - ∂_r(w‖f‖²)(r)‖ₑ → 0` as `r' → r`, via the four-term
decomposition `(Δ_h - ∂w) N_h + ∂w (N_h - N) + 2 w Re⟨f r, Q_h - f'⟩ + h w ‖Q_h‖²`. -/
def WPRL1 : Prop :=
  ∀ (μ : Measure (ℝ × ℝ)) (w : ℝ → ℝ × ℝ → ℝ) (f : ℝ → ℝ × ℝ → ℂ) (f' : ℝ × ℝ → ℂ) (r : ℝ),
    WPRHyp μ w f f' r →
    Tendsto (fun r' => ∫⁻ x, ‖(r' - r)⁻¹ • (w r' x * ‖f r' x‖ ^ 2 - w r x * ‖f r x‖ ^ 2) -
        deriv (fun q => w q x * ‖f q x‖ ^ 2) r‖ₑ ∂μ) (𝓝[≠] r) (𝓝 0)

theorem weightedProductRule_of (h1 : WPRInteg) (h2 : WPRL1) : WeightedProductRule := by
  intro μ w f f' r hw hf hC hd hT hf0 hf1
  have hH : WPRHyp μ w f f' r := ⟨hw, hf, hC, hd, hT, hf0, hf1⟩
  obtain ⟨hD, hr, hev⟩ := h1 μ w f f' r hH
  have hL := h2 μ w f f' r hH
  rw [hasDerivAt_iff_tendsto_slope]
  have hint : Tendsto (fun r' => ∫ x, (r' - r)⁻¹ • (w r' x * ‖f r' x‖ ^ 2 - w r x * ‖f r x‖ ^ 2) ∂μ)
      (𝓝[≠] r) (𝓝 (∫ x, deriv (fun q => w q x * ‖f q x‖ ^ 2) r ∂μ)) := by
    refine tendsto_integral_of_L1 _ hD.aestronglyMeasurable ?_ hL
    filter_upwards [hev] with r' hr'
    exact ((hr'.sub hr).smul ((r' - r)⁻¹)).congr (by filter_upwards with x; simp)
  refine hint.congr' ?_
  filter_upwards [hev] with r' hr'
  rw [integral_smul, integral_sub hr' hr, slope_def_field, div_eq_inv_mul]
  rfl

end UnforcedLeray.Short.IIIa.E0
