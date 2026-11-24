import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1.AdjDerivOf
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Strong `L²` derivative from pointwise derivatives (source `shorter-proof-2026-11-02.tex`
1650-1656, the `L²` domination step of `T₀(t)*`)

Abstract measure theory: along any sequence `x n → t`, the difference quotients of `s ↦ F s`
converge in `L²(μ)` to `D`, by dominated convergence applied to the pointwise error
`(x n - t)⁻¹ (f (x n) - f t) - f' t`, with the mean value inequality supplying the majorant `2 g`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.B0223 (MeridC)

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- The pointwise difference-quotient error `(s - t)⁻¹ (f s a - f t a) - f' t a`. -/
def lpErrFn {α : Type} (f f' : ℝ → α → MeridC) (t s : ℝ) : α → MeridC :=
  fun a => (s - t)⁻¹ • (f s a - f t a) - f' t a

/-- The `L²` majorant `(2 g)²` in `ℝ≥0∞` form. -/
def lpBnd {α : Type} (g : α → ℝ) : α → ℝ≥0∞ := fun a => (2 * ‖g a‖ₑ) ^ (2:ℝ)

theorem lpErrFn_aesm {α : Type} [MeasurableSpace α] {μ : Measure α} (f f' : ℝ → α → MeridC) (t s : ℝ)
    (h1 : AEStronglyMeasurable (f s) μ) (h2 : AEStronglyMeasurable (f t) μ)
    (h3 : AEStronglyMeasurable (f' t) μ) : AEStronglyMeasurable (lpErrFn f f' t s) μ := by
  unfold lpErrFn
  have h4 : AEStronglyMeasurable (fun a => f s a - f t a) μ := h1.sub h2
  have h5 : AEStronglyMeasurable ((s - t)⁻¹ • (fun a => f s a - f t a)) μ := h4.const_smul _
  exact h5.sub h3

/-- Mean value bound for the difference-quotient error. -/
theorem lpSlope_err_norm_le {t ε g : ℝ} (hε : 0 < ε) (φ : ℝ → MeridC) (φ' : ℝ → MeridC)
    (hd : ∀ r ∈ Ioo (t - ε) (t + ε), HasDerivAt φ (φ' r) r)
    (hb : ∀ r ∈ Ioo (t - ε) (t + ε), ‖φ' r‖ ≤ g) {s : ℝ} (hs : s ∈ Ioo (t - ε) (t + ε)) :
    ‖(s - t)⁻¹ • (φ s - φ t) - φ' t‖ ≤ 2 * g := by
  have hconv : Convex ℝ (Ioo (t - ε) (t + ε)) := convex_Ioo _ _
  have ht : t ∈ Ioo (t - ε) (t + ε) := ⟨by linarith, by linarith⟩
  have hmvt : ‖φ s - φ t‖ ≤ g * ‖s - t‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := φ) (f' := φ') (C := g)
      (fun r hr => (hd r hr).hasDerivWithinAt) hb hconv ht hs
  have ht' : ‖φ' t‖ ≤ g := hb t ht
  rcases eq_or_ne s t with h | h
  · have hg0 : 0 ≤ g := le_trans (norm_nonneg _) ht'
    simp only [h, sub_self, inv_zero, zero_smul, zero_sub, norm_neg]
    linarith
  · have hst : 0 < ‖s - t‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h)
    have h1 : ‖(s - t)⁻¹ • (φ s - φ t)‖ ≤ g := by
      rw [norm_smul, norm_inv]
      calc ‖s - t‖⁻¹ * ‖φ s - φ t‖ ≤ ‖s - t‖⁻¹ * (g * ‖s - t‖) := by gcongr
        _ = g := by
          have := hst.ne'
          field_simp
    calc ‖(s - t)⁻¹ • (φ s - φ t) - φ' t‖ ≤ ‖(s - t)⁻¹ • (φ s - φ t)‖ + ‖φ' t‖ :=
          norm_sub_le _ _
      _ ≤ g + g := add_le_add h1 ht'
      _ = 2 * g := by ring

/-- Pointwise convergence of the difference-quotient error along `x → t`. -/
theorem lpSlope_err_tendsto {t : ℝ} (φ : ℝ → MeridC) (d : MeridC) (hd : HasDerivAt φ d t)
    (x : ℕ → ℝ) (hx : Tendsto x atTop (𝓝[≠] t)) :
    Tendsto (fun n => (x n - t)⁻¹ • (φ (x n) - φ t) - d) atTop (𝓝 0) := by
  have h := ((hasDerivAt_iff_tendsto_slope.mp hd).comp hx).sub_const d
  rw [sub_self] at h
  refine Tendsto.congr (fun n => ?_) h
  simp only [Function.comp_apply, slope_def_module]

theorem lpBnd_lintegral_ne_top {α : Type} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ} (hg : MemLp g 2 μ) :
    ∫⁻ a, lpBnd g a ∂μ ≠ ∞ := by
  have hgfin := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (μ := μ) (f := g) (p := 2)
    (by norm_num) (by norm_num) hg.eLpNorm_lt_top
  simp only [ENNReal.toReal_ofNat] at hgfin
  have h : ∀ a, lpBnd g a = 4 * ‖g a‖ₑ ^ (2:ℝ) := by
    intro a
    simp only [lpBnd, ENNReal.rpow_two, mul_pow]
    norm_num
  simp_rw [h]
  rw [lintegral_const_mul' _ _ (by norm_num)]
  exact ENNReal.mul_ne_top (by norm_num) hgfin.ne

/-- **Strong `L²` derivative from pointwise derivatives** (source 1650-1656), see
`LpHasDerivOfPointwise` in `AdjDerivOf.lean`. -/
theorem lp_hasDerivAt_of_pointwise : LpHasDerivOfPointwise := by
  intro α _ μ F D f f' g t ε hε hg hF hD hpt
  rw [hasDerivAt_iff_tendsto_slope, tendsto_iff_seq_tendsto]
  intro x hx
  have hxt : Tendsto x atTop (𝓝 t) := hx.mono_right nhdsWithin_le_nhds
  have hB : Ioo (t - ε) (t + ε) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hxB : ∀ᶠ n in atTop, x n ∈ Ioo (t - ε) (t + ε) := hxt.eventually hB
  have hrep : ∀ n, (⇑(slope F t (x n)) - ⇑D : α → MeridC) =ᵐ[μ] lpErrFn f f' t (x n) := by
    intro n
    filter_upwards [Lp.coeFn_smul ((x n - t)⁻¹) (F (x n) - F t),
      Lp.coeFn_sub (F (x n)) (F t), hF (x n), hF t, hD] with a h1 h2 h3 h4 h5
    simp only [slope_def_module, lpErrFn, h1, h2, h3, h4, h5, Pi.sub_apply, Pi.smul_apply]
  have hF_m : ∀ s, AEStronglyMeasurable (f s) μ := fun s =>
    (Lp.aestronglyMeasurable (F s)).congr (hF s)
  have hD_m : AEStronglyMeasurable (f' t) μ := (Lp.aestronglyMeasurable D).congr hD
  have hn_m : ∀ n, AEStronglyMeasurable (lpErrFn f f' t (x n)) μ := fun n =>
    lpErrFn_aesm f f' t (x n) (hF_m (x n)) (hF_m t) hD_m
  have h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => ‖lpErrFn f f' t (x n) a‖ₑ ^ (2:ℝ)) atTop (𝓝 0) := by
    filter_upwards [hpt] with a ha
    have hd : HasDerivAt (fun s => f s a) (f' t a) t := (ha t ⟨by linarith, by linarith⟩).1
    have h2 : Tendsto (fun n => (x n - t)⁻¹ • (f (x n) a - f t a) - f' t a) atTop (𝓝 0) :=
      lpSlope_err_tendsto (fun s => f s a) (f' t a) hd x hx
    have h3 : Tendsto (fun n => ‖lpErrFn f f' t (x n) a‖ₑ) atTop (𝓝 0) := by
      have := (continuous_enorm.tendsto (0 : MeridC)).comp h2
      rw [enorm_zero] at this
      exact this
    have h4 := (ENNReal.continuous_rpow_const (y := (2:ℝ))).tendsto (0 : ℝ≥0∞)
    rw [ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2)] at h4
    exact h4.comp h3
  have hbdd : ∀ᶠ n in atTop, ∀ᵐ a ∂μ, ‖lpErrFn f f' t (x n) a‖ₑ ^ (2:ℝ) ≤ lpBnd g a := by
    filter_upwards [hxB] with n hn_mem
    filter_upwards [hpt] with a ha
    have hb : ‖lpErrFn f f' t (x n) a‖ ≤ 2 * g a :=
      lpSlope_err_norm_le hε (fun s => f s a) (fun r => f' r a)
        (fun r hr => (ha r hr).1) (fun r hr => (ha r hr).2) hn_mem
    have h2 : ‖lpErrFn f f' t (x n) a‖ ≤ 2 * ‖g a‖ := by
      have := le_abs_self (g a)
      rw [Real.norm_eq_abs]
      linarith
    have hle : ‖lpErrFn f f' t (x n) a‖ₑ ≤ 2 * ‖g a‖ₑ := by
      rw [← ofReal_norm_eq_enorm]
      calc ENNReal.ofReal ‖lpErrFn f f' t (x n) a‖ ≤ ENNReal.ofReal (2 * ‖g a‖) :=
            ENNReal.ofReal_le_ofReal h2
        _ = 2 * ‖g a‖ₑ := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ofReal_norm_eq_enorm]
    exact ENNReal.rpow_le_rpow hle (by norm_num)
  have hmeas : ∀ᶠ n in atTop, AEMeasurable (fun a => ‖lpErrFn f f' t (x n) a‖ₑ ^ (2:ℝ)) μ :=
    Eventually.of_forall fun n => ((hn_m n).aemeasurable.enorm).pow_const _
  have hint : Tendsto (fun n => ∫⁻ a, ‖lpErrFn f f' t (x n) a‖ₑ ^ (2:ℝ) ∂μ) atTop
      (𝓝 (∫⁻ _a, (0:ℝ≥0∞) ∂μ)) :=
    tendsto_lintegral_filter_of_dominated_convergence' (lpBnd g) hmeas hbdd
      (lpBnd_lintegral_ne_top hg) h_lim
  rw [lintegral_zero] at hint
  have hfinal : Tendsto (fun n => eLpNorm (lpErrFn f f' t (x n)) 2 μ) atTop (𝓝 0) := by
    have h5 := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto (0 : ℝ≥0∞)
    rw [ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 1 / 2)] at h5
    refine Tendsto.congr (fun n => ?_) (h5.comp hint)
    simp only [Function.comp_apply]
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num),
      ENNReal.toReal_ofNat]
  refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ D).mpr ?_
  exact hfinal.congr' (Eventually.of_forall fun n => (eLpNorm_congr_ae (hrep n)).symm)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
