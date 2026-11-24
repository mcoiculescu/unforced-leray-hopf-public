import UnforcedLeray.Lib.HeatR3.LineBridge
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Order.Interval.Basic

/-!
# The Duhamel formula on the line (INF05 T18, `lineDuhamel`)


items `lineDuhamel` and `deriv_lineDuhamel`. Unit B0157 (tex 2379–2393, `eq:st18-t00156`): the
decaying mean stream `ψ̄` solves `ψ̄_s - νψ̄_ηη = g`, `ψ̄(0) = ψ̄₀`, i.e.

`ψ̄(s) = e^{νs∂²}ψ̄₀ + ∫₀ˢ e^{ν(s-r)∂²}g(r) dr`   (`lineDuhamel ν ψ̄₀ g s`),

and its negative derivative `-∂_ηψ̄` is the same Duhamel formula for the derivatives of the
data (`hasDerivAt_lineDuhamel`, `deriv_lineDuhamel`): this is the computation behind
"its negative derivative solves the averaged horizontal velocity equation with the correct
datum" (tex 2387–2389).

Bypass BP7 of the scoping note: the derivative is put on the data (bounded `C¹` data, bounded
uniformly in `r ∈ [0, s]`), so the Duhamel integrand is dominated by a constant and no singular
kernel bound `‖∂G_θ‖_{L¹} ~ θ^{-1/2}` is needed. At `r = s` the heat time is `0` and the
Gaussian `lineGauss 0` is the zero function (Lean's `0 ^ (-1/2) = 0`); this endpoint is a null
set and does not affect the integral.

Not built here: `mean_stream_eq` (the identification `-∂_ηψ̄ = v̄₁` needs the averaged mild
formulation of the velocity, which is not formalized; scoping note T18).
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology Real intervalIntegral
open scoped Interval

theorem lineGauss_zero (ξ : ℝ) : lineGauss 0 ξ = 0 := by
  rw [lineGauss, mul_zero, Real.zero_rpow (by norm_num), zero_mul]

theorem lineHeat_zero (f : ℝ → ℝ) : lineHeat 0 f = 0 := by
  funext η
  simp [lineHeat, lineGauss_zero]

theorem measurable_lineGauss_uncurry : Measurable fun q : ℝ × ℝ => lineGauss q.1 q.2 := by
  unfold lineGauss
  fun_prop

/-- `|e^{θ∂²}f| ≤ M` for `|f| ≤ M`, `θ ≥ 0`. -/
theorem abs_lineHeat_le {θ : ℝ} (hθ : 0 ≤ θ) {f : ℝ → ℝ} {M : ℝ} (hM : ∀ ξ, |f ξ| ≤ M)
    (η : ℝ) : |lineHeat θ f η| ≤ M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  rcases hθ.eq_or_lt with rfl | hθ
  · rw [lineHeat_zero, Pi.zero_apply, abs_zero]; exact hM0
  rw [← Real.norm_eq_abs, lineHeat]
  calc ‖∫ ξ, lineGauss θ ξ * f (η - ξ)‖ ≤ ∫ ξ, lineGauss θ ξ * M :=
        norm_integral_le_of_norm_le ((integrable_lineGauss hθ).mul_const M)
          (Eventually.of_forall fun ξ => by
            rw [norm_mul, Real.norm_of_nonneg (lineGauss_nonneg hθ ξ), Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left (hM _) (lineGauss_nonneg hθ ξ))
    _ = M := by rw [MeasureTheory.integral_mul_const, integral_lineGauss hθ, one_mul]

/-- **Differentiation of the line heat flow on the data side.** For `θ > 0` and `f ∈ C¹` with
`|f|, |f'| ≤ M`: `∂_η e^{θ∂²}f = e^{θ∂²}f'`. -/
theorem hasDerivAt_lineHeat_data {θ : ℝ} (hθ : 0 < θ) {f f' : ℝ → ℝ}
    (hf : ∀ η, HasDerivAt f (f' η) η) {M : ℝ} (hM : ∀ ξ, |f ξ| ≤ M) (hM' : ∀ ξ, |f' ξ| ≤ M)
    (η : ℝ) : HasDerivAt (lineHeat θ f) (lineHeat θ f' η) η := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hf'm : Measurable f' := by
    have : f' = deriv f := funext fun x => (hf x).deriv.symm
    rw [this]; exact measurable_deriv f
  have hmeas : ∀ η' : ℝ, AEStronglyMeasurable (fun ξ => lineGauss θ ξ * f (η' - ξ)) volume :=
    fun η' => ((continuous_lineGauss θ).mul
      (hfc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun η' ξ => lineGauss θ ξ * f (η' - ξ))
    (F' := fun η' ξ => lineGauss θ ξ * f' (η' - ξ))
    (bound := fun ξ => lineGauss θ ξ * M) (x₀ := η) (s := univ) univ_mem
    (Eventually.of_forall hmeas)
    (((integrable_lineGauss hθ).mul_const M).mono' (hmeas η) (Eventually.of_forall fun ξ => by
      rw [norm_mul, Real.norm_of_nonneg (lineGauss_nonneg hθ ξ), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hM _) (lineGauss_nonneg hθ ξ)))
    ((continuous_lineGauss θ).aestronglyMeasurable.mul
      (hf'm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
    (Eventually.of_forall fun ξ η' _ => by
      rw [norm_mul, Real.norm_of_nonneg (lineGauss_nonneg hθ ξ), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hM' _) (lineGauss_nonneg hθ ξ))
    ((integrable_lineGauss hθ).mul_const M)
    (Eventually.of_forall fun ξ η' _ => by
      have h1 : HasDerivAt (fun z : ℝ => z - ξ) 1 η' := (hasDerivAt_id η').sub_const ξ
      have h2 := (hf (η' - ξ)).comp η' h1
      rw [mul_one] at h2
      exact h2.const_mul (lineGauss θ ξ))
  exact key.2

/-- **INF05 T18 `lineDuhamel`** (B0157, tex 2379–2393, `eq:st18-t00156`). The mild solution of
`ψ_s - νψ_ηη = g(s)`, `ψ(0) = ψ₀`:
`ψ(s, η) = e^{νs∂²}ψ₀(η) + ∫₀ˢ e^{ν(s-r)∂²}g(r)(η) dr`. Meaningful for `ν > 0`, `s ≥ 0`. -/
def lineDuhamel (ν : ℝ) (ψ₀ : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (s η : ℝ) : ℝ :=
  lineHeat (ν * s) ψ₀ η + ∫ r in (0 : ℝ)..s, lineHeat (ν * (s - r)) (g r) η

/-- Measurability of the Duhamel integrand in the time variable. -/
theorem stronglyMeasurable_lineHeat_param {g : ℝ → ℝ → ℝ} (hgm : Measurable (Function.uncurry g))
    (ν s η : ℝ) : StronglyMeasurable fun r => lineHeat (ν * (s - r)) (g r) η := by
  have h1 : Measurable fun q : ℝ × ℝ => lineGauss (ν * (s - q.1)) q.2 :=
    measurable_lineGauss_uncurry.comp
      ((measurable_const.mul (measurable_const.sub measurable_fst)).prodMk measurable_snd)
  have h2 : Measurable fun q : ℝ × ℝ => g q.1 (η - q.2) :=
    hgm.comp (measurable_fst.prodMk (measurable_const.sub measurable_snd))
  exact (h1.mul h2).stronglyMeasurable.integral_prod_right'

/-- **INF05 T18 `deriv_lineDuhamel`, pointwise form** (B0157, tex 2387–2389). For `ν, s > 0`,
`ψ₀ ∈ C¹` and `g(r) ∈ C¹` (`r ∈ [0, s]`) with `ψ₀, ψ₀', g, ∂_ηg` bounded by `M`, and
`g`, `∂_ηg` jointly measurable: `∂_η` of the Duhamel solution is the Duhamel solution of the
differentiated data. -/
theorem hasDerivAt_lineDuhamel {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) {ψ₀ ψ₁ : ℝ → ℝ}
    {g g₁ : ℝ → ℝ → ℝ} {M : ℝ} (hψ : ∀ η, HasDerivAt ψ₀ (ψ₁ η) η) (hψb : ∀ η, |ψ₀ η| ≤ M)
    (hψ₁b : ∀ η, |ψ₁ η| ≤ M) (hgm : Measurable (Function.uncurry g))
    (hg₁m : Measurable (Function.uncurry g₁))
    (hg : ∀ r ∈ Icc 0 s, ∀ η, HasDerivAt (g r) (g₁ r η) η)
    (hgb : ∀ r ∈ Icc 0 s, ∀ η, |g r η| ≤ M) (hg₁b : ∀ r ∈ Icc 0 s, ∀ η, |g₁ r η| ≤ M)
    (η : ℝ) : HasDerivAt (lineDuhamel ν ψ₀ g s) (lineDuhamel ν ψ₁ g₁ s η) η := by
  have h0 := hasDerivAt_lineHeat_data (mul_pos hν hs) hψ hψb hψ₁b η
  have hIoc : Ι (0 : ℝ) s = Ioc 0 s := uIoc_of_le hs.le
  have hθ : ∀ r ∈ Ι (0 : ℝ) s, 0 ≤ ν * (s - r) := fun r hr => by
    rw [hIoc] at hr; exact mul_nonneg hν.le (by linarith [hr.2])
  have hIcc : ∀ r ∈ Ι (0 : ℝ) s, r ∈ Icc 0 s := fun r hr => by
    rw [hIoc] at hr; exact ⟨hr.1.le, hr.2⟩
  have hfin : volume (Ι (0 : ℝ) s) ≠ ⊤ := by
    rw [hIoc, Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hI : HasDerivAt (fun η' => ∫ r in (0 : ℝ)..s, lineHeat (ν * (s - r)) (g r) η')
      (∫ r in (0 : ℝ)..s, lineHeat (ν * (s - r)) (g₁ r) η) η := by
    refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun η' r => lineHeat (ν * (s - r)) (g r) η')
      (F' := fun η' r => lineHeat (ν * (s - r)) (g₁ r) η')
      (bound := fun _ => M) (x₀ := η) (s := univ) univ_mem ?_ ?_ ?_ ?_
      intervalIntegrable_const ?_).2
    · exact Eventually.of_forall fun η' =>
        (stronglyMeasurable_lineHeat_param hgm ν s η').aestronglyMeasurable
    · rw [intervalIntegrable_iff]
      exact Measure.integrableOn_of_bounded (M := M) hfin
        (stronglyMeasurable_lineHeat_param hgm ν s η).aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall fun r hr => by
          rw [Real.norm_eq_abs]; exact abs_lineHeat_le (hθ r hr) (hgb r (hIcc r hr)) η))
    · exact (stronglyMeasurable_lineHeat_param hg₁m ν s η).aestronglyMeasurable
    · exact Eventually.of_forall fun r hr η' _ => by
        rw [Real.norm_eq_abs]; exact abs_lineHeat_le (hθ r hr) (hg₁b r (hIcc r hr)) η'
    · filter_upwards [Measure.ae_ne volume s] with r hrs hr η' _
      have hr' : r ∈ Ioc 0 s := by rw [← hIoc]; exact hr
      have hpos : 0 < ν * (s - r) :=
        mul_pos hν (by have := lt_of_le_of_ne hr'.2 hrs; linarith)
      exact hasDerivAt_lineHeat_data hpos (hg r (hIcc r hr)) (hgb r (hIcc r hr))
        (hg₁b r (hIcc r hr)) η'
  exact h0.add hI

/-- **INF05 T18 `deriv_lineDuhamel`** (B0157). Under the hypotheses of
`hasDerivAt_lineDuhamel`: `∂_η lineDuhamel ν ψ₀ g s = lineDuhamel ν ψ₀' (∂_ηg) s`. -/
theorem deriv_lineDuhamel {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) {ψ₀ ψ₁ : ℝ → ℝ}
    {g g₁ : ℝ → ℝ → ℝ} {M : ℝ} (hψ : ∀ η, HasDerivAt ψ₀ (ψ₁ η) η) (hψb : ∀ η, |ψ₀ η| ≤ M)
    (hψ₁b : ∀ η, |ψ₁ η| ≤ M) (hgm : Measurable (Function.uncurry g))
    (hg₁m : Measurable (Function.uncurry g₁))
    (hg : ∀ r ∈ Icc 0 s, ∀ η, HasDerivAt (g r) (g₁ r η) η)
    (hgb : ∀ r ∈ Icc 0 s, ∀ η, |g r η| ≤ M) (hg₁b : ∀ r ∈ Icc 0 s, ∀ η, |g₁ r η| ≤ M) :
    deriv (lineDuhamel ν ψ₀ g s) = lineDuhamel ν ψ₁ g₁ s :=
  funext fun η =>
    (hasDerivAt_lineDuhamel hν hs hψ hψb hψ₁b hgm hg₁m hg hgb hg₁b η).deriv

end UnforcedLeray.Heat
