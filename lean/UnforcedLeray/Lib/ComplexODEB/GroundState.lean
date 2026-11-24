import UnforcedLeray.Analysis.Rayleigh.RealSpeed.Profile
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# B0034 helper: ground-state factorization on a finite interval

*Provenance (Wave 2 block 2H PLAN1b).* Copy of the compiled draft

`Lib/ComplexODE` (the copies `Lib/ComplexODE/NeutralSolution` and `Lib/ComplexODE/L1Dependence`
replace the drafts `Analysis/Rayleigh/Evans/NeutralSolution` and `L1ContinuousGronwall`), with
namespace `UnforcedLeray.ComplexODEB` in place of `UnforcedLeray.B0034`. Do not import it
together with `Units/B0034` helpers that pull in those drafts.

Tool of the continuation behind B0034 (`paper/main.tex`, lines 1012–1021; blueprint
unit B0034). The manuscript excludes real limiting speeds by the factorization with
`h_c = e^t(Ω-c)` (the whole-line version is `paper/main.tex`, Chapter 01 §3.4 of the
Lin-free route, commit 4dd0a82; for the annulus it is Lin 2003, Lemma 5.8). For a real
solution of `f'' = (β² + Q) f` and a comparison function with `h'' = (1 + Q) h`, the
bracket `B = f f' - (h'/h) f²` satisfies

`B' = (f' - (h'/h) f)² + (β² - 1) f²`,

so `(β² - 1) ∫ f² ≤ B(q) - B(p)` on every interval where `h ≠ 0`. When the bracket
vanishes at both ends (Dirichlet data, or a simple zero of `h` where `f` vanishes)
and `β > 1`, `f = 0`.
-/

set_option autoImplicit false

noncomputable section
open Set Filter Topology MeasureTheory
namespace UnforcedLeray.ComplexODEB

/-- The ground-state bracket `f f' - (h'/h) f²`. -/
def groundBracket (f f' h h' : ℝ → ℝ) (t : ℝ) : ℝ :=
  f t * f' t - h' t / h t * f t ^ 2

/-- Pointwise derivative of the ground-state bracket. -/
theorem hasDerivAt_groundBracket {β Q : ℝ} {f f' h h' h'' : ℝ → ℝ} {t : ℝ}
    (hf : HasDerivAt f (f' t) t) (hf' : HasDerivAt f' ((β ^ 2 + Q) * f t) t)
    (hh : HasDerivAt h (h' t) t) (hh' : HasDerivAt h' (h'' t) t) (hne : h t ≠ 0)
    (hode : h'' t = (1 + Q) * h t) :
    HasDerivAt (groundBracket f f' h h')
      ((f' t - h' t / h t * f t) ^ 2 + (β ^ 2 - 1) * f t ^ 2) t := by
  have h1 := hf.mul hf'
  have h2 := (hh'.div hh hne).mul (hf.pow 2)
  refine (h1.sub h2).congr_deriv ?_
  simp only [Pi.pow_apply, Pi.div_apply]
  rw [hode]
  field_simp
  push_cast
  ring

/-- The bracket inequality on a closed interval where `h` does not vanish. -/
theorem integral_sq_le_groundBracket {p q β : ℝ} (hpq : p ≤ q)
    {f f' h h' h'' Q : ℝ → ℝ}
    (hf : ∀ t ∈ Icc p q, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Icc p q, HasDerivAt f' ((β ^ 2 + Q t) * f t) t)
    (hh : ∀ t ∈ Icc p q, HasDerivAt h (h' t) t)
    (hh' : ∀ t ∈ Icc p q, HasDerivAt h' (h'' t) t)
    (hne : ∀ t ∈ Icc p q, h t ≠ 0)
    (hode : ∀ t ∈ Icc p q, h'' t = (1 + Q t) * h t) :
    (β ^ 2 - 1) * (∫ t in p..q, f t ^ 2) ≤
      groundBracket f f' h h' q - groundBracket f f' h h' p := by
  have hd : ∀ t ∈ Icc p q, HasDerivAt (groundBracket f f' h h')
      ((f' t - h' t / h t * f t) ^ 2 + (β ^ 2 - 1) * f t ^ 2) t := fun t ht =>
    hasDerivAt_groundBracket (hf t ht) (hf' t ht) (hh t ht) (hh' t ht) (hne t ht) (hode t ht)
  have hfc : ContinuousOn f (Icc p q) := fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hbc : ContinuousOn (groundBracket f f' h h') (Icc p q) := fun t ht =>
    (hd t ht).continuousAt.continuousWithinAt
  have hint : IntegrableOn (fun t => (β ^ 2 - 1) * f t ^ 2) (Icc p q) :=
    (continuousOn_const.mul (hfc.pow 2)).integrableOn_compact isCompact_Icc
  have key := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hpq hbc
    (fun t ht => (hd t (Ioo_subset_Icc_self ht)).hasDerivWithinAt) hint
    (fun t _ => le_add_of_nonneg_left (sq_nonneg _))
  rwa [intervalIntegral.integral_const_mul] at key

/-- The bracket inequality with limits at the ends of an open interval. -/
theorem integral_sq_eq_zero_of_groundBracket {p q β : ℝ} (hpq : p < q) (hβ : 1 < β)
    {f f' h h' h'' Q : ℝ → ℝ}
    (hfc : ContinuousOn f (Icc p q))
    (hf : ∀ t ∈ Ioo p q, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Ioo p q, HasDerivAt f' ((β ^ 2 + Q t) * f t) t)
    (hh : ∀ t ∈ Ioo p q, HasDerivAt h (h' t) t)
    (hh' : ∀ t ∈ Ioo p q, HasDerivAt h' (h'' t) t)
    (hne : ∀ t ∈ Ioo p q, h t ≠ 0)
    (hode : ∀ t ∈ Ioo p q, h'' t = (1 + Q t) * h t)
    (hl : Tendsto (groundBracket f f' h h') (𝓝[>] p) (𝓝 0))
    (hr : Tendsto (groundBracket f f' h h') (𝓝[<] q) (𝓝 0)) :
    (∫ t in p..q, f t ^ 2) = 0 := by
  set B := groundBracket f f' h h' with hB
  have hint : IntegrableOn (fun t => f t ^ 2) (uIcc p q) := by
    rw [uIcc_of_le hpq.le]
    exact (hfc.pow 2).integrableOn_compact isCompact_Icc
  have hβ2 : 0 < β ^ 2 - 1 := by nlinarith
  -- inequality on compact subintervals
  have hsub : ∀ l r, p < l → l ≤ r → r < q →
      (β ^ 2 - 1) * (∫ t in l..r, f t ^ 2) ≤ B r - B l := by
    intro l r hl hlr hr
    have hs : Icc l r ⊆ Ioo p q := Icc_subset_Ioo hl hr
    exact integral_sq_le_groundBracket hlr (fun t ht => hf t (hs ht)) (fun t ht => hf' t (hs ht))
      (fun t ht => hh t (hs ht)) (fun t ht => hh' t (hs ht)) (fun t ht => hne t (hs ht))
      (fun t ht => hode t (hs ht))
  -- first limit: the left end
  have hstep : ∀ r, p < r → r < q → (β ^ 2 - 1) * (∫ t in p..r, f t ^ 2) ≤ B r := by
    intro r hpr hrq
    have hcont : ContinuousOn (fun x => ∫ t in x..r, f t ^ 2) (uIcc p r) := by
      apply intervalIntegral.continuousOn_primitive_interval_left
      apply hint.mono_set
      rw [uIcc_of_le hpq.le, uIcc_of_le hpr.le]
      exact Icc_subset_Icc le_rfl hrq.le
    have hlim : Tendsto (fun x => (β ^ 2 - 1) * (∫ t in x..r, f t ^ 2) + B x)
        (𝓝[>] p) (𝓝 ((β ^ 2 - 1) * (∫ t in p..r, f t ^ 2) + 0)) := by
      refine Tendsto.add (Tendsto.const_mul _ ?_) hl
      have hc := hcont p (by rw [uIcc_of_le hpr.le]; exact left_mem_Icc.mpr hpr.le)
      refine hc.tendsto.mono_left (nhdsWithin_le_of_mem ?_)
      rw [uIcc_of_le hpr.le]
      exact Icc_mem_nhdsGT hpr
    have hev : ∀ᶠ x in 𝓝[>] p, (β ^ 2 - 1) * (∫ t in x..r, f t ^ 2) + B x ≤ B r := by
      filter_upwards [Ioo_mem_nhdsGT hpr] with x hx
      linarith [hsub x r hx.1 hx.2.le hrq]
    have := le_of_tendsto hlim hev
    linarith
  -- second limit: the right end
  have hcont2 : ContinuousOn (fun x => ∫ t in p..x, f t ^ 2) (uIcc p q) :=
    intervalIntegral.continuousOn_primitive_interval hint
  have hlim2 : Tendsto (fun x => (β ^ 2 - 1) * (∫ t in p..x, f t ^ 2) - B x)
      (𝓝[<] q) (𝓝 ((β ^ 2 - 1) * (∫ t in p..q, f t ^ 2) - 0)) := by
    refine Tendsto.sub (Tendsto.const_mul _ ?_) hr
    have hc := hcont2 q (by rw [uIcc_of_le hpq.le]; exact right_mem_Icc.mpr hpq.le)
    refine hc.tendsto.mono_left (nhdsWithin_le_of_mem ?_)
    rw [uIcc_of_le hpq.le]
    exact Icc_mem_nhdsLT hpq
  have hev2 : ∀ᶠ x in 𝓝[<] q, (β ^ 2 - 1) * (∫ t in p..x, f t ^ 2) - B x ≤ 0 := by
    filter_upwards [Ioo_mem_nhdsLT hpq] with x hx
    linarith [hstep x hx.1 hx.2]
  have hle := le_of_tendsto hlim2 hev2
  have hnn : 0 ≤ ∫ t in p..q, f t ^ 2 :=
    intervalIntegral.integral_nonneg hpq.le (fun t _ => sq_nonneg _)
  have : (β ^ 2 - 1) * (∫ t in p..q, f t ^ 2) ≤ 0 := by linarith
  nlinarith

/-- A continuous function with vanishing square integral vanishes inside. -/
theorem eq_zero_of_integral_sq_eq_zero {p q : ℝ} {f : ℝ → ℝ}
    (hfc : ContinuousOn f (Icc p q)) (h0 : (∫ t in p..q, f t ^ 2) = 0) :
    ∀ t ∈ Ioo p q, f t = 0 := by
  intro t₀ ht₀
  by_contra hne
  have hpq : p < q := ht₀.1.trans ht₀.2
  have hca : ContinuousAt f t₀ := hfc.continuousAt (Icc_mem_nhds ht₀.1 ht₀.2)
  have hev : ∀ᶠ t in 𝓝 t₀, f t ≠ 0 := hca.eventually_ne hne
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set l : ℝ := max p (t₀ - δ / 2) with hl
  set r : ℝ := min q (t₀ + δ / 2) with hr
  have hlr : l < r := by
    have h1 : p < q := hpq
    have h2 : p < t₀ + δ / 2 := by linarith [ht₀.1]
    have h3 : t₀ - δ / 2 < q := by linarith [ht₀.2]
    have h4 : t₀ - δ / 2 < t₀ + δ / 2 := by linarith
    exact max_lt (lt_min h1 h2) (lt_min h3 h4)
  have hpl : p ≤ l := le_max_left _ _
  have hrq : r ≤ q := min_le_left _ _
  have hint : IntegrableOn (fun t => f t ^ 2) (Icc p q) :=
    (hfc.pow 2).integrableOn_compact isCompact_Icc
  have hpos : 0 < ∫ t in l..r, f t ^ 2 := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on _ _ hlr
    · exact ((hfc.pow 2).mono (Icc_subset_Icc hpl hrq)).intervalIntegrable_of_Icc hlr.le
    · intro t ht
      have hdist : dist t t₀ < δ := by
        rw [Real.dist_eq, abs_lt]
        constructor
        · linarith [le_max_right p (t₀ - δ / 2), ht.1]
        · linarith [min_le_right q (t₀ + δ / 2), ht.2]
      have hft := hball hdist
      positivity
  have hmono : (∫ t in l..r, f t ^ 2) ≤ ∫ t in p..q, f t ^ 2 :=
    intervalIntegral.integral_mono_interval hpl hlr.le hrq
      (Eventually.of_forall fun t => sq_nonneg (f t)) ((hfc.pow 2).intervalIntegrable_of_Icc hpq.le)
  linarith

/-- The bracket tends to zero at a point where `f` vanishes and `h` does not. -/
theorem tendsto_groundBracket_of_ne {s : Set ℝ} {p : ℝ} {f f' h h' : ℝ → ℝ}
    (hf : ContinuousWithinAt f s p) (hf' : ContinuousWithinAt f' s p)
    (hh : ContinuousWithinAt h s p) (hh' : ContinuousWithinAt h' s p)
    (hp : f p = 0) (hne : h p ≠ 0) :
    Tendsto (groundBracket f f' h h') (𝓝[s] p) (𝓝 0) := by
  have hc := (hf.mul hf').sub ((hh'.div hh hne).mul (hf.pow 2))
  have h0 : groundBracket f f' h h' p = 0 := by simp [groundBracket, hp]
  rw [← h0]
  exact hc

/-- The bracket tends to zero at a simple zero of `h` where `f` vanishes. -/
theorem tendsto_groundBracket_of_simple_zero {s : Set ℝ} {p : ℝ} {f f' h h' : ℝ → ℝ}
    (hf : HasDerivWithinAt f (f' p) s p) (hf' : ContinuousWithinAt f' s p)
    (hh : HasDerivWithinAt h (h' p) s p) (hh' : ContinuousWithinAt h' s p)
    (hp : f p = 0) (hhp : h p = 0) (hne : h' p ≠ 0) :
    Tendsto (groundBracket f f' h h') (𝓝[s \ {p}] p) (𝓝 0) := by
  have hsf := hasDerivWithinAt_iff_tendsto_slope.mp hf
  have hsh := hasDerivWithinAt_iff_tendsto_slope.mp hh
  have hle : 𝓝[s \ {p}] p ≤ 𝓝[s] p := nhdsWithin_mono _ sdiff_subset
  have h1 : Tendsto (fun t => f t * f' t) (𝓝[s \ {p}] p) (𝓝 0) := by
    have := (hf.continuousWithinAt.mul hf').tendsto.mono_left hle
    simp only [Pi.mul_apply, hp, zero_mul] at this
    exact this
  have hlin : Tendsto (fun t : ℝ => t - p) (𝓝[s \ {p}] p) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => t - p) (𝓝 p) (𝓝 (p - p)) := (tendsto_id.sub_const p)
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun t => h' t * (t - p) * slope f p t ^ 2 / slope h p t)
      (𝓝[s \ {p}] p) (𝓝 (h' p * 0 * f' p ^ 2 / h' p)) :=
    (((hh'.tendsto.mono_left hle).mul hlin).mul (hsf.pow 2)).div hsh hne
  rw [mul_zero, zero_mul, zero_div] at h2
  have heq : ∀ᶠ t in 𝓝[s \ {p}] p,
      h' t * (t - p) * slope f p t ^ 2 / slope h p t = h' t / h t * f t ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htp : t - p ≠ 0 := sub_ne_zero.mpr ht.2
    rw [slope_def_field, slope_def_field, hp, hhp, sub_zero, sub_zero]
    by_cases hht : h t = 0
    · simp [hht]
    · field_simp
  have h2' := h2.congr' heq
  have := h1.sub h2'
  rw [sub_zero] at this
  exact this

end UnforcedLeray.ComplexODEB
