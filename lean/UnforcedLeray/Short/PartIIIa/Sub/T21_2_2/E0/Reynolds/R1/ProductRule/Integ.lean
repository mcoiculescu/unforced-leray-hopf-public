import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_2_1_4

/-!
# `PartIII-a:T21/2/2/2/2/1/4`, leaf `WPRInteg` (integrability)

Source: `the November 2 reference manuscript` (SP) lines 3060-3073.
Pointwise: `D = ∂_r w ‖f‖² + 2 w Re⟨f, f'⟩`, `|∂_r w| ≤ C w` (ball hypothesis at `r`), and
`2‖f‖‖f'‖ ≤ ‖f‖² + ‖f'‖²` (AM-GM, no Cauchy-Schwarz needed).  For `r'` near `r`,
`f r' = f r + h • (D_h + f')` with `D_h = h⁻¹ • (f r' - f r) - f'`, `h = r' - r`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.E0

/-- A pointwise derivative of a family whose members are a.e. strongly measurable is a.e.
strongly measurable (limit of difference quotients along a sequence `r + 1/(n+1)`). -/
theorem wpr_aesm_of_hasDerivAt {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {μ : Measure X} (F : ℝ → X → E) (r : ℝ)
    (hF : ∀ᶠ q in 𝓝 r, AEStronglyMeasurable (F q) μ) (D : X → E)
    (hD : ∀ x, HasDerivAt (fun q => F q x) (D x) r) : AEStronglyMeasurable D μ := by
  have hseq : Tendsto (fun n : ℕ => r + 1 / ((n : ℝ) + 1)) atTop (𝓝 r) := by
    have h1 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h2 := (tendsto_const_nhds (x := r)).add h1
    simpa using h2
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hseq.eventually hF)
  have hT : Tendsto (fun n : ℕ => r + 1 / (((n + N : ℕ) : ℝ) + 1)) atTop (𝓝 r) := by
    have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat N)
    have h2 := (tendsto_const_nhds (x := r)).add h1
    simpa [Function.comp_def] using h2
  have hT' : Tendsto (fun n : ℕ => r + 1 / (((n + N : ℕ) : ℝ) + 1)) atTop (𝓝[≠] r) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hT, Eventually.of_forall fun n => ?_⟩
    have hpos : (0 : ℝ) < 1 / (((n + N : ℕ) : ℝ) + 1) := by positivity
    intro h
    simp only [Set.mem_singleton_iff] at h
    linarith
  have hF0 : AEStronglyMeasurable (F r) μ := hF.self_of_nhds
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun x => (r + 1 / (((n + N : ℕ) : ℝ) + 1) - r)⁻¹ •
        (F (r + 1 / (((n + N : ℕ) : ℝ) + 1)) x - F r x)) μ := fun n =>
    ((hN (n + N) (Nat.le_add_left N n)).sub hF0).const_smul _
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ =>
      (r + 1 / (((n + N : ℕ) : ℝ) + 1) - r)⁻¹ •
        (F (r + 1 / (((n + N : ℕ) : ℝ) + 1)) x - F r x)) atTop (𝓝 (D x)) :=
    ae_of_all _ fun x => (hasDerivAt_iff_tendsto_slope.1 (hD x)).comp hT'
  exact aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim

/-- `|w|²`-type identity: `‖a * ‖z‖²‖ₑ = ofReal a * ‖z‖ₑ²` for `a ≥ 0`. -/
theorem wpr_enorm_wsq {E : Type*} [NormedAddCommGroup E] (a : ℝ) (ha : 0 ≤ a) (z : E) :
    ‖a * ‖z‖ ^ 2‖ₑ = ENNReal.ofReal a * ‖z‖ₑ ^ 2 := by
  rw [enorm_mul, Real.enorm_eq_ofReal ha, Real.enorm_eq_ofReal (sq_nonneg ‖z‖),
    ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg z)]

/-- Integrability of `a ‖g‖²` from a finite weighted `lintegral`. -/
theorem wpr_integrable_wsq {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} (a : X → ℝ) (ha : ∀ x, 0 ≤ a x) (ha_m : AEStronglyMeasurable a μ)
    (g : X → E) (hg : AEStronglyMeasurable g μ)
    (hfin : ∫⁻ x, ENNReal.ofReal (a x) * ‖g x‖ₑ ^ 2 ∂μ < ⊤) :
    Integrable (fun x => a x * ‖g x‖ ^ 2) μ := by
  refine ⟨ha_m.mul (hg.norm.pow 2), ?_⟩
  show ∫⁻ x, ‖a x * ‖g x‖ ^ 2‖ₑ ∂μ < ⊤
  calc ∫⁻ x, ‖a x * ‖g x‖ ^ 2‖ₑ ∂μ = ∫⁻ x, ENNReal.ofReal (a x) * ‖g x‖ₑ ^ 2 ∂μ :=
        lintegral_congr fun x => wpr_enorm_wsq _ (ha x) _
    _ < ⊤ := hfin

end UnforcedLeray.Short.IIIa.E0

open UnforcedLeray.Short.IIIa.E0 in
theorem wprInteg : UnforcedLeray.Short.IIIa.E0.WPRInteg := by
  intro μ w f f' r hH
  obtain ⟨hw, hf, ⟨C, δ, hC0, hδ, hball⟩, hd, hT, hf0, hf1⟩ := hH
  have hrb : r ∈ ball r δ := mem_ball_self hδ
  have hw0 : ∀ x, 0 ≤ w r x := fun x => (hball x r hrb).2.1
  have hfr : AEStronglyMeasurable (f r) μ := hf.self_of_nhds
  have hf' : AEStronglyMeasurable f' μ := wpr_aesm_of_hasDerivAt f r hf f' hd
  have hI0 : Integrable (fun x => w r x * ‖f r x‖ ^ 2) μ :=
    wpr_integrable_wsq (w r) hw0 (hw r).aestronglyMeasurable (f r) hfr hf0
  have hI1 : Integrable (fun x => w r x * ‖f' x‖ ^ 2) μ :=
    wpr_integrable_wsq (w r) hw0 (hw r).aestronglyMeasurable f' hf' hf1
  -- pointwise derivative of the integrand in `r`
  have hDpt : ∀ x, HasDerivAt (fun q => w q x * ‖f q x‖ ^ 2)
      (deriv (fun q => w q x) r * ‖f r x‖ ^ 2 + w r x * (2 * inner ℝ (f r x) (f' x))) r :=
    fun x => ((hball x r hrb).1.hasDerivAt).mul (hd x).norm_sq
  have hFev : ∀ᶠ q in 𝓝 r, AEStronglyMeasurable (fun x => w q x * ‖f q x‖ ^ 2) μ := by
    filter_upwards [hf] with q hq
    exact (hw q).aestronglyMeasurable.mul (hq.norm.pow 2)
  have hD1m : AEStronglyMeasurable (fun x => deriv (fun q => w q x * ‖f q x‖ ^ 2) r) μ :=
    wpr_aesm_of_hasDerivAt (fun q x => w q x * ‖f q x‖ ^ 2) r hFev _
      (fun x => (hDpt x).differentiableAt.hasDerivAt)
  have hbound : ∀ x, ‖deriv (fun q => w q x * ‖f q x‖ ^ 2) r‖ ≤
      (C + 1) * (w r x * ‖f r x‖ ^ 2) + w r x * ‖f' x‖ ^ 2 := by
    intro x
    rw [(hDpt x).deriv, Real.norm_eq_abs, abs_le]
    have hdw : |deriv (fun q => w q x) r| ≤ C * w r x := (hball x r hrb).2.2.2
    obtain ⟨h1, h2⟩ := abs_le.1 hdw
    obtain ⟨h3, h4⟩ := abs_le.1 (abs_real_inner_le_norm (f r x) (f' x))
    have hwx := hw0 x
    have hA : 0 ≤ ‖f r x‖ := norm_nonneg _
    have hB : 0 ≤ ‖f' x‖ := norm_nonneg _
    have e1 := mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖f r x‖)
    have e2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖f r x‖)
    have e3 := mul_le_mul_of_nonneg_left h4 hwx
    have e4 := mul_le_mul_of_nonneg_left h3 hwx
    have e5 := mul_nonneg hwx (sq_nonneg (‖f r x‖ - ‖f' x‖))
    have e6 := mul_nonneg hC0 (mul_nonneg hwx (sq_nonneg ‖f r x‖))
    constructor <;> nlinarith
  have hG : Integrable (fun x => (C + 1) * (w r x * ‖f r x‖ ^ 2) + w r x * ‖f' x‖ ^ 2) μ :=
    (hI0.const_mul (C + 1)).add hI1
  have part1 : Integrable (fun x => deriv (fun q => w q x * ‖f q x‖ ^ 2) r) μ :=
    Integrable.mono' hG hD1m (ae_of_all _ fun x => hbound x)
  have hsmall : ∀ᶠ r' in 𝓝[≠] r,
      ∫⁻ x, ENNReal.ofReal (w r x) * ‖(r' - r)⁻¹ • (f r' x - f r x) - f' x‖ₑ ^ 2 ∂μ < 1 :=
    hT.eventually (gt_mem_nhds zero_lt_one)
  have hball_ev : ∀ᶠ r' in 𝓝[≠] r, r' ∈ ball r δ :=
    nhdsWithin_le_nhds (ball_mem_nhds r hδ)
  have hfev : ∀ᶠ r' in 𝓝[≠] r, AEStronglyMeasurable (f r') μ :=
    nhdsWithin_le_nhds hf
  have part3 : ∀ᶠ r' in 𝓝[≠] r, Integrable (fun x => w r' x * ‖f r' x‖ ^ 2) μ := by
    filter_upwards [hsmall, hball_ev, hfev, eventually_mem_nhdsWithin] with r' hs hb hfr' hne'
    have hne : r' - r ≠ 0 := sub_ne_zero.2 hne'
    have hDm : AEStronglyMeasurable (fun x => (r' - r)⁻¹ • (f r' x - f r x) - f' x) μ :=
      (((hfr'.sub hfr).const_smul ((r' - r)⁻¹)).sub hf')
    have hDI : Integrable (fun x => w r x * ‖(r' - r)⁻¹ • (f r' x - f r x) - f' x‖ ^ 2) μ :=
      wpr_integrable_wsq (w r) hw0 (hw r).aestronglyMeasurable _ hDm (hs.trans ENNReal.one_lt_top)
    have hmaj : Integrable (fun x => 2 * C * (w r x * ‖f r x‖ ^ 2)
        + 4 * C * (r' - r) ^ 2 * (w r x * ‖(r' - r)⁻¹ • (f r' x - f r x) - f' x‖ ^ 2)
        + 4 * C * (r' - r) ^ 2 * (w r x * ‖f' x‖ ^ 2)) μ :=
      ((hI0.const_mul (2 * C)).add (hDI.const_mul (4 * C * (r' - r) ^ 2))).add
        (hI1.const_mul (4 * C * (r' - r) ^ 2))
    refine Integrable.mono' hmaj ((hw r').aestronglyMeasurable.mul (hfr'.norm.pow 2))
      (ae_of_all _ fun x => ?_)
    show ‖w r' x * ‖f r' x‖ ^ 2‖ ≤ _
    have hwle := hball x r' hb
    have hw'0 : 0 ≤ w r' x := hwle.2.1
    set D : ℂ := (r' - r)⁻¹ • (f r' x - f r x) - f' x with hDdef
    have hfeq : f r' x = f r x + (r' - r) • (D + f' x) := by
      rw [hDdef, sub_add_cancel, smul_inv_smul₀ hne]
      abel
    have hnorm : ‖f r' x‖ ≤ ‖f r x‖ + |r' - r| * (‖D‖ + ‖f' x‖) := by
      calc ‖f r' x‖ = ‖f r x + (r' - r) • (D + f' x)‖ := by rw [← hfeq]
        _ ≤ ‖f r x‖ + ‖(r' - r) • (D + f' x)‖ := norm_add_le _ _
        _ = ‖f r x‖ + |r' - r| * ‖D + f' x‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ ‖f r x‖ + |r' - r| * (‖D‖ + ‖f' x‖) := by
          gcongr
          exact norm_add_le _ _
    have hsq : ‖f r' x‖ ^ 2 ≤ 2 * ‖f r x‖ ^ 2 + 4 * (r' - r) ^ 2 * (‖D‖ ^ 2 + ‖f' x‖ ^ 2) := by
      have h1 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      have h2 : (|r' - r| * (‖D‖ + ‖f' x‖)) ^ 2 ≤ 2 * (r' - r) ^ 2 * (‖D‖ ^ 2 + ‖f' x‖ ^ 2) := by
        rw [mul_pow, sq_abs]
        nlinarith [sq_nonneg (‖D‖ - ‖f' x‖), sq_nonneg (r' - r)]
      nlinarith [sq_nonneg (‖f r x‖ - |r' - r| * (‖D‖ + ‖f' x‖))]
    have hCw : 0 ≤ C * w r x := mul_nonneg hC0 (hw0 x)
    have hwCw : w r' x * ‖f r' x‖ ^ 2 ≤ C * w r x * ‖f r' x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hwle.2.2.1 (sq_nonneg _)
    have hfin := mul_le_mul_of_nonneg_left hsq hCw
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw'0 (sq_nonneg _))]
    nlinarith
  have part2 : Integrable (fun x => w r x * ‖f r x‖ ^ 2) μ := hI0
  exact ⟨part1, part2, part3⟩
