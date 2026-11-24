import UnforcedLeray.Lib.ComplexODEB.Neutral
import UnforcedLeray.Analysis.Rayleigh.Evans.NontangentialCoefficientLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# B0034 helper: the critical-layer Cauchy integral on a log-annulus

*Provenance (Wave 2 block 2H PLAN1b).* Copy of the compiled draft

`Lib/ComplexODE` (the copies `Lib/ComplexODE/NeutralSolution` and `Lib/ComplexODE/L1Dependence`
replace the drafts `Analysis/Rayleigh/Evans/NeutralSolution` and `L1ContinuousGronwall`), with
namespace `UnforcedLeray.ComplexODEB` in place of `UnforcedLeray.B0034`. Do not import it
together with `Units/B0034` helpers that pull in those drafts.

Step of the local bifurcation behind B0034 (`paper/main.tex`, lines 1012–1021; Lin
2003, Theorem 5.9; the whole-line version is the critical-layer limit (3.7c) of the
Lin-free route, commit 4dd0a82). With `J = Ω - a_*` (`gaussianOffset`), which has
the single simple zero `t_*` and `J' < 0`, and a `C¹` real weight `φ`,

`∫_a^b φ(t) / (J(t) - z) dt → I₊(φ)` as `z → 0` inside a cone `‖z‖ ≤ C Im z`,

with `Im I₊(φ) = -π φ(t_*) / J'(t_*)` (`tendsto_cauchyIntegral`, `im_cauchyLimit`).
The proof splits `φ = (φ - κ J') + κ J'` with `κ = φ(t_*)/J'(t_*)`: the first part
converges by dominated convergence (`|φ - κJ'| ≤ L|t - t_*| ≤ (L/m)|J|` and
`|J| ≤ (2C+1)‖J - z‖` in the cone), the second is `κ (log(J(b) - z) - log(J(a) - z))`.
-/

set_option autoImplicit false

noncomputable section
open Set Filter Topology MeasureTheory Complex
namespace UnforcedLeray.ComplexODEB
open UnforcedLeray.Rayleigh UnforcedLeray.Rayleigh.Evans UnforcedLeray.Sturm
open UnforcedLeray.GaussianPotential

/-! ### The offset `J = Ω - a_*` -/

/-- `J' = Ω' = -2 x Ω` in log radius. -/
def offsetDeriv (t : ℝ) : ℝ := -2 * neutralRadius t * neutralOmega t

theorem hasDerivAt_gaussianOffset (t : ℝ) : HasDerivAt gaussianOffset (offsetDeriv t) t := by
  have h := (hasDerivAt_neutralOmega t).sub_const gaussianCriticalSpeed
  exact h

theorem continuous_offsetDeriv : Continuous offsetDeriv := by
  unfold offsetDeriv
  exact (continuous_const.mul continuous_neutralRadius).mul continuous_neutralOmega

theorem offsetDeriv_neg (t : ℝ) : offsetDeriv t < 0 := by
  unfold offsetDeriv
  have h1 := neutralRadius_pos t
  have h2 := neutralOmega_pos t
  nlinarith [mul_pos h1 h2]

theorem gaussianOffset_critical : gaussianOffset neutralCriticalTime = 0 := by
  unfold gaussianOffset gaussianCriticalSpeed
  simp

theorem continuous_gaussianOffset' : Continuous gaussianOffset :=
  continuous_neutralOmega.sub continuous_const

/-- Explicit lower bound for `|J'|` on `[a, b]`. -/
def offsetLower (a b : ℝ) : ℝ := Real.exp (2 * a) / 2 * neutralOmega b

theorem offsetLower_pos (a b : ℝ) : 0 < offsetLower a b := by
  unfold offsetLower
  have := neutralOmega_pos b
  positivity

theorem offsetLower_le_abs_offsetDeriv {a b t : ℝ} (ht : t ∈ Icc a b) :
    offsetLower a b ≤ |offsetDeriv t| := by
  unfold offsetLower offsetDeriv
  rw [abs_of_neg (by have := offsetDeriv_neg t; unfold offsetDeriv at this; exact this)]
  have hx : Real.exp (2 * a) / 4 ≤ neutralRadius t := by
    unfold neutralRadius
    gcongr
    linarith [ht.1]
  have hΩ : neutralOmega b ≤ neutralOmega t :=
    UnforcedLeray.Rayleigh.RealSpeed.neutralOmega_strictAnti.antitone ht.2
  have h0 : 0 ≤ neutralOmega b := (neutralOmega_pos b).le
  have h1 : 0 ≤ Real.exp (2 * a) / 4 := by positivity
  nlinarith [mul_le_mul hx hΩ h0 (neutralRadius_pos t).le]

/-- `J` separates points of `[a, b]` at the explicit rate `offsetLower a b`. -/
theorem offsetLower_mul_le {a b t s : ℝ} (ht : t ∈ Icc a b) (hs : s ∈ Icc a b) :
    offsetLower a b * |t - s| ≤ |gaussianOffset t - gaussianOffset s| := by
  rcases lt_trichotomy s t with hst | hst | hst
  · obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope gaussianOffset offsetDeriv hst
      continuous_gaussianOffset'.continuousOn (fun x _ => hasDerivAt_gaussianOffset x)
    have hξab : ξ ∈ Icc a b := ⟨by linarith [hs.1, hξ.1], by linarith [ht.2, hξ.2]⟩
    have hpos : 0 < t - s := sub_pos.mpr hst
    have heq : gaussianOffset t - gaussianOffset s = offsetDeriv ξ * (t - s) := by
      rw [hξeq]; field_simp
    rw [heq, abs_mul, abs_of_pos hpos]
    exact mul_le_mul_of_nonneg_right (offsetLower_le_abs_offsetDeriv hξab) hpos.le
  · subst hst; simp
  · obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope gaussianOffset offsetDeriv hst
      continuous_gaussianOffset'.continuousOn (fun x _ => hasDerivAt_gaussianOffset x)
    have hξab : ξ ∈ Icc a b := ⟨by linarith [ht.1, hξ.1], by linarith [hs.2, hξ.2]⟩
    have hpos : 0 < s - t := sub_pos.mpr hst
    have heq : gaussianOffset s - gaussianOffset t = offsetDeriv ξ * (s - t) := by
      rw [hξeq]; field_simp
    rw [abs_sub_comm t s, abs_sub_comm (gaussianOffset t) (gaussianOffset s), heq, abs_mul,
      abs_of_pos hpos]
    exact mul_le_mul_of_nonneg_right (offsetLower_le_abs_offsetDeriv hξab) hpos.le

theorem offsetLower_mul_le_critical {a b t : ℝ} (ht : t ∈ Icc a b)
    (hcrit : neutralCriticalTime ∈ Icc a b) :
    offsetLower a b * |t - neutralCriticalTime| ≤ |gaussianOffset t| := by
  have h := offsetLower_mul_le ht hcrit
  rwa [gaussianOffset_critical, sub_zero] at h

theorem gaussianOffset_pos_of_lt {t : ℝ} (ht : t < neutralCriticalTime) : 0 < gaussianOffset t := by
  have h := UnforcedLeray.Rayleigh.RealSpeed.neutralOmega_strictAnti ht
  have h0 := gaussianOffset_critical
  unfold gaussianOffset at h0 ⊢
  linarith

theorem gaussianOffset_neg_of_gt {t : ℝ} (ht : neutralCriticalTime < t) : gaussianOffset t < 0 := by
  have h := UnforcedLeray.Rayleigh.RealSpeed.neutralOmega_strictAnti ht
  have h0 := gaussianOffset_critical
  unfold gaussianOffset at h0 ⊢
  linarith

/-! ### The approach cone -/

/-- In the cone `‖z‖ ≤ C Im z`, `|x| + ‖z‖ ≤ (2C+1) ‖x - z‖` for real `x`. -/
theorem abs_add_norm_le_cone {C : ℝ} (hC : 0 < C) {z : ℂ} (hz : z ∈ criticalApproachCone C)
    (x : ℝ) : |x| + ‖z‖ ≤ (2 * C + 1) * ‖(x : ℂ) - z‖ := by
  have h1 : z.im ≤ ‖(x : ℂ) - z‖ := by
    have h := Complex.abs_im_le_norm ((x : ℂ) - z)
    simpa only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg,
      abs_of_pos hz.1] using h
  have h2 : ‖z‖ ≤ C * ‖(x : ℂ) - z‖ := hz.2.trans (mul_le_mul_of_nonneg_left h1 hC.le)
  have h3 : |x| ≤ ‖(x : ℂ) - z‖ + ‖z‖ := by
    have h := norm_le_norm_sub_add ((x : ℂ)) z
    simpa [Complex.norm_real, Real.norm_eq_abs] using h
  nlinarith

theorem norm_sub_pos_of_cone {C : ℝ} {z : ℂ} (hz : z ∈ criticalApproachCone C) (x : ℝ) :
    0 < ‖(x : ℂ) - z‖ :=
  norm_pos_iff.mpr (criticalDenominator_ne_zero x hz.1)

/-! ### The Cauchy limit -/

/-- Coefficient of the singular part. -/
def cauchyCoeff (φ : ℝ → ℝ) : ℝ := φ neutralCriticalTime / offsetDeriv neutralCriticalTime

/-- The regular numerator `φ - κ J'`, which vanishes at `t_*`. -/
def cauchyNum (φ : ℝ → ℝ) (t : ℝ) : ℝ := φ t - cauchyCoeff φ * offsetDeriv t

/-- The nontangential boundary value `I₊(φ)`. -/
def cauchyLimit (a b : ℝ) (φ : ℝ → ℝ) : ℂ :=
  ((∫ t in a..b, cauchyNum φ t / gaussianOffset t : ℝ) : ℂ) +
    (cauchyCoeff φ : ℂ) *
      (((Real.log ‖((gaussianOffset b : ℝ) : ℂ)‖ - Real.log (gaussianOffset a) : ℝ) : ℂ) - (Real.pi : ℂ) * I)

theorem im_cauchyLimit (a b : ℝ) (φ : ℝ → ℝ) :
    (cauchyLimit a b φ).im = -Real.pi * cauchyCoeff φ := by
  unfold cauchyLimit
  rw [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  simp
  ring

theorem cauchyNum_critical (φ : ℝ → ℝ) : cauchyNum φ neutralCriticalTime = 0 := by
  unfold cauchyNum cauchyCoeff
  have := offsetDeriv_neg neutralCriticalTime
  rw [div_mul_cancel₀ _ this.ne, sub_self]


theorem offsetDeriv_contDiff : ContDiff ℝ 1 offsetDeriv := by
  unfold offsetDeriv neutralRadius neutralOmega neutralRadius
  fun_prop

/-- The singular part: `∫ J'/(J - z) = log(J(b) - z) - log(J(a) - z)`. -/
theorem tendsto_singular_part {a b : ℝ} (hcrit : neutralCriticalTime ∈ Ioo a b) {C : ℝ} :
    Tendsto (fun z : ℂ => ∫ t in a..b, (offsetDeriv t : ℂ) / ((gaussianOffset t : ℂ) - z))
      (𝓝[criticalApproachCone C] 0)
      (𝓝 (((Real.log ‖((gaussianOffset b : ℝ) : ℂ)‖ - Real.log (gaussianOffset a) : ℝ) : ℂ) -
        (Real.pi : ℂ) * I)) := by
  have hJa : 0 < gaussianOffset a := gaussianOffset_pos_of_lt hcrit.1
  have hJb : gaussianOffset b < 0 := gaussianOffset_neg_of_gt hcrit.2
  have heq : ∀ᶠ z in 𝓝[criticalApproachCone C] (0 : ℂ),
      Complex.log ((gaussianOffset b : ℂ) - z) - Complex.log ((gaussianOffset a : ℂ) - z) =
        ∫ t in a..b, (offsetDeriv t : ℂ) / ((gaussianOffset t : ℂ) - z) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hslit : ∀ t : ℝ, (gaussianOffset t : ℂ) - z ∈ Complex.slitPlane := fun t => by
      rw [Complex.mem_slitPlane_iff]
      right
      simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, ne_eq, neg_eq_zero]
      exact hz.1.ne'
    have hd : ∀ t ∈ uIcc a b, HasDerivAt (fun s => Complex.log ((gaussianOffset s : ℂ) - z))
        ((offsetDeriv t : ℂ) / ((gaussianOffset t : ℂ) - z)) t := fun t _ =>
      ((hasDerivAt_gaussianOffset t).ofReal_comp.sub_const z).clog_real (hslit t)
    have hcont : Continuous (fun t => (offsetDeriv t : ℂ) / ((gaussianOffset t : ℂ) - z)) :=
      (Complex.continuous_ofReal.comp continuous_offsetDeriv).div
        ((Complex.continuous_ofReal.comp continuous_gaussianOffset').sub continuous_const)
        (fun t => criticalDenominator_ne_zero _ hz.1)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable a b)]
  have hA : Tendsto (fun z : ℂ => Complex.log ((gaussianOffset b : ℂ) - z))
      (𝓝[criticalApproachCone C] 0)
      (𝓝 ((Real.log ‖((gaussianOffset b : ℝ) : ℂ)‖ : ℂ) - (Real.pi : ℂ) * I)) := by
    have hlog := Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero
      (z := (gaussianOffset b : ℂ)) (by simpa using hJb) (by simp)
    refine hlog.comp ?_
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have : Tendsto (fun z : ℂ => (gaussianOffset b : ℂ) - z) (𝓝 0)
          (𝓝 ((gaussianOffset b : ℂ) - 0)) := tendsto_const_nhds.sub tendsto_id
      rw [sub_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [mem_setOf_eq, Complex.sub_im, Complex.ofReal_im, zero_sub, neg_lt_zero]
      exact hz.1
  have hB : Tendsto (fun z : ℂ => Complex.log ((gaussianOffset a : ℂ) - z))
      (𝓝[criticalApproachCone C] 0) (𝓝 ((Real.log (gaussianOffset a) : ℝ) : ℂ)) := by
    have hslit : ((gaussianOffset a : ℝ) : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left
      simpa using hJa
    have hc := (continuousAt_clog hslit).tendsto
    have hlim : Tendsto (fun z : ℂ => (gaussianOffset a : ℂ) - z) (𝓝[criticalApproachCone C] 0)
        (𝓝 ((gaussianOffset a : ℂ))) := by
      have : Tendsto (fun z : ℂ => (gaussianOffset a : ℂ) - z) (𝓝 0)
          (𝓝 ((gaussianOffset a : ℂ) - 0)) := tendsto_const_nhds.sub tendsto_id
      rw [sub_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have := hc.comp hlim
    rwa [← Complex.ofReal_log hJa.le] at this
  refine Tendsto.congr' heq ?_
  convert hA.sub hB using 2
  push_cast
  ring

/-- The regular part converges by dominated convergence inside the cone. -/
theorem tendsto_regular_part {a b : ℝ} (hcrit : neutralCriticalTime ∈ Ioo a b) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) {C : ℝ} (hC : 0 < C) :
    Tendsto (fun z : ℂ => ∫ t in a..b, (cauchyNum φ t : ℂ) / ((gaussianOffset t : ℂ) - z))
      (𝓝[criticalApproachCone C] 0)
      (𝓝 ((∫ t in a..b, cauchyNum φ t / gaussianOffset t : ℝ) : ℂ)) := by
  have hab : a < b := hcrit.1.trans hcrit.2
  have hcritI : neutralCriticalTime ∈ Icc a b := Ioo_subset_Icc_self hcrit
  have hnum : ContDiff ℝ 1 (cauchyNum φ) := by
    unfold cauchyNum
    exact hφ.sub (contDiff_const.mul offsetDeriv_contDiff)
  -- Lipschitz bound of the numerator
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hnum.continuous_deriv le_rfl).continuousOn (s := Icc a b))
  have hlip : ∀ t ∈ Icc a b, |cauchyNum φ t| ≤ L * |t - neutralCriticalTime| := by
    intro t ht
    have h := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := cauchyNum φ) (f' := deriv (cauchyNum φ))
      (fun x _ => ((hnum.differentiable one_ne_zero) x).hasDerivAt.hasDerivWithinAt) hL hcritI ht
    rwa [cauchyNum_critical, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at h
  set m := offsetLower a b with hm
  have hmpos : 0 < m := offsetLower_pos a b
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL a (left_mem_Icc.mpr hab.le))
  set K : ℝ := L / m * (2 * C + 1) with hK
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => K)
  · filter_upwards [self_mem_nhdsWithin] with z hz
    apply Continuous.aestronglyMeasurable
    exact (Complex.continuous_ofReal.comp hnum.continuous).div
      ((Complex.continuous_ofReal.comp continuous_gaussianOffset').sub continuous_const)
      (fun t => criticalDenominator_ne_zero _ hz.1)
  · filter_upwards [self_mem_nhdsWithin] with z hz
    refine Eventually.of_forall fun t ht => ?_
    rw [uIoc_of_le hab.le] at ht
    have htI : t ∈ Icc a b := Ioc_subset_Icc_self ht
    have hden := norm_sub_pos_of_cone hz (gaussianOffset t)
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ hden]
    have h1 := hlip t htI
    have h2 := offsetLower_mul_le_critical htI hcritI
    have h3 := abs_add_norm_le_cone hC hz (gaussianOffset t)
    have h4 : L * |t - neutralCriticalTime| ≤ L / m * |gaussianOffset t| := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hmpos]
      nlinarith [mul_le_mul_of_nonneg_left h2 hL0]
    have h5 : L / m * |gaussianOffset t| ≤ L / m * ((2 * C + 1) * ‖(gaussianOffset t : ℂ) - z‖) :=
      mul_le_mul_of_nonneg_left (by linarith [norm_nonneg z]) (div_nonneg hL0 hmpos.le)
    rw [hK]
    nlinarith
  · exact intervalIntegrable_const
  · filter_upwards [(volume : Measure ℝ).ae_ne neutralCriticalTime] with t ht _
    have hJ : (gaussianOffset t : ℂ) ≠ 0 := by
      exact_mod_cast gaussianOffset_ne_zero_off_critical ht
    have hc : ContinuousAt (fun z : ℂ => (cauchyNum φ t : ℂ) / ((gaussianOffset t : ℂ) - z)) 0 :=
      continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by simpa using hJ)
    have hv : (cauchyNum φ t : ℂ) / ((gaussianOffset t : ℂ) - 0) =
        ((cauchyNum φ t / gaussianOffset t : ℝ) : ℂ) := by
      rw [sub_zero, Complex.ofReal_div]
    rw [← hv]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds

/-- The critical-layer Cauchy integral has the nontangential boundary value `I₊(φ)`. -/
theorem tendsto_cauchyIntegral {a b : ℝ} (hcrit : neutralCriticalTime ∈ Ioo a b) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) {C : ℝ} (hC : 0 < C) :
    Tendsto (fun z : ℂ => ∫ t in a..b, (φ t : ℂ) / ((gaussianOffset t : ℂ) - z))
      (𝓝[criticalApproachCone C] 0) (𝓝 (cauchyLimit a b φ)) := by
  have hsum := (tendsto_regular_part hcrit hφ hC).add
    ((tendsto_singular_part hcrit (C := C)).const_mul (cauchyCoeff φ : ℂ))
  refine Tendsto.congr' ?_ hsum
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hden : ∀ t : ℝ, (gaussianOffset t : ℂ) - z ≠ 0 := fun t =>
    criticalDenominator_ne_zero _ hz.1
  have hc1 : Continuous (fun t => (cauchyNum φ t : ℂ) / ((gaussianOffset t : ℂ) - z)) := by
    have hnum : Continuous (cauchyNum φ) := by
      unfold cauchyNum
      exact hφ.continuous.sub (continuous_const.mul continuous_offsetDeriv)
    exact (Complex.continuous_ofReal.comp hnum).div
      ((Complex.continuous_ofReal.comp continuous_gaussianOffset').sub continuous_const) hden
  have hc2 : Continuous (fun t => (offsetDeriv t : ℂ) / ((gaussianOffset t : ℂ) - z)) :=
    (Complex.continuous_ofReal.comp continuous_offsetDeriv).div
      ((Complex.continuous_ofReal.comp continuous_gaussianOffset').sub continuous_const) hden
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
    (hc1.intervalIntegrable a b) ((hc2.intervalIntegrable a b).const_mul _)]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [cauchyNum, Complex.ofReal_sub, Complex.ofReal_mul]
  field_simp [hden t]
  ring

end UnforcedLeray.ComplexODEB
