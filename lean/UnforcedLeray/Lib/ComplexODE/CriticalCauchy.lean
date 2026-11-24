import UnforcedLeray.Lib.ComplexODE.CauchyLimit
import UnforcedLeray.Analysis.Rayleigh.Evans.Coefficients
import UnforcedLeray.Analysis.Sturm.NeutralProfile

/-!
# The nontangential critical-layer limit (INF18 target O2)

Wave 1 block 1H part 3, scoping note

bypass B8 (ii). Blueprint unit B0034 (Lin's continuation, `paper/main.tex` lines 1011--1021):
the bifurcation from the neutral Dirichlet mode needs the boundary value of the Cauchy integral
`∫ W g/(Ω - c)` as the speed `c` tends to the critical speed `a_* = e^{-2}` from the upper
half-plane. `Ω` is the Gaussian angular speed in log radius; it crosses `a_*` exactly at
`t_* = log √8`, with `Ω'(t_*) < 0`.

`Iplus a b g` is the explicit limit: the absolutely convergent real integral
`∫_a^b (W g/(Ω - a_*) - (W g)(t_*)/(Ω'(t_*)(t - t_*)))` (the principal value) plus
`(W g)(t_*) (log ((b - t_*)/(t_* - a)) - π i)/Ω'(t_*)`. The integrand's value at the single point
`t = t_*`, where Lean's real division returns `0`, does not affect the integral.

Main result: `tendsto_critical_cauchy`. The limit holds along every closed cone
`κ |c - a_*| ≤ Im (c - a_*)`, `κ > 0`; `Im I₊ = π W(t_*) g(t_*)/|Ω'(t_*)|`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped Interval ContDiff

namespace UnforcedLeray.Rayleigh.Evans

open UnforcedLeray.ComplexODE Sturm GaussianPotential

/-- The cone of speeds `c` with `κ |c - a_*| ≤ Im (c - a_*)` and `Im c > 0`. -/
def criticalSpeedCone (κ : ℝ) : Set ℂ :=
  {c | κ * ‖c - (gaussianCriticalSpeed : ℂ)‖ ≤ (c - (gaussianCriticalSpeed : ℂ)).im ∧
    0 < (c - (gaussianCriticalSpeed : ℂ)).im}

/-- The boundary value `I₊` of `∫_a^b W g/(Ω - c)` at the critical speed. -/
def Iplus (a b : ℝ) (g : ℝ → ℝ) : ℂ :=
  (((∫ t in a..b, (Wlog t * g t / (neutralOmega t - gaussianCriticalSpeed) -
      Wlog neutralCriticalTime * g neutralCriticalTime /
        (deriv neutralOmega neutralCriticalTime * (t - neutralCriticalTime)))) : ℝ) : ℂ) +
    ((Wlog neutralCriticalTime * g neutralCriticalTime : ℝ) : ℂ) *
      (((Real.log ((b - neutralCriticalTime) / (neutralCriticalTime - a)) : ℂ) -
        Real.pi * I) / ((deriv neutralOmega neutralCriticalTime : ℝ) : ℂ))

theorem deriv_neutralOmega_eq (t : ℝ) :
    deriv neutralOmega t = -2 * neutralRadius t * neutralOmega t :=
  (hasDerivAt_neutralOmega t).deriv

theorem deriv_neutralOmega_critical_neg : deriv neutralOmega neutralCriticalTime < 0 := by
  rw [deriv_neutralOmega_eq, neutralRadius_at_critical, neutralOmega_at_critical]
  have := Real.exp_pos (-2)
  linarith

theorem neutralOmega_critical_eq : neutralOmega neutralCriticalTime = gaussianCriticalSpeed := by
  rw [neutralOmega_at_critical]
  rfl

theorem Iplus_im (a b : ℝ) (g : ℝ → ℝ) :
    (Iplus a b g).im = Real.pi * Wlog neutralCriticalTime * g neutralCriticalTime /
      |deriv neutralOmega neutralCriticalTime| := by
  have hd := deriv_neutralOmega_critical_neg
  rw [abs_of_neg hd]
  unfold Iplus
  rw [Complex.add_im, Complex.ofReal_im, zero_add, Complex.im_ofReal_mul, Complex.div_ofReal_im]
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub, add_zero]
  field_simp

/-- **INF18 O2. Nontangential critical-layer limit.** For `a < t_* < b`, a real `C¹` weight `g`
and `κ > 0`, as `c → a_*` inside the cone `κ |c - a_*| ≤ Im (c - a_*)`,
`∫_a^b W g/(Ω - c) dt → I₊`, and `Im I₊ = π W(t_*) g(t_*)/|Ω'(t_*)|`. -/
theorem tendsto_critical_cauchy {a b : ℝ} (ha : a < neutralCriticalTime)
    (hb : neutralCriticalTime < b) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun c : ℂ => ∫ t in a..b, ((Wlog t * g t : ℝ) : ℂ) / ((neutralOmega t : ℂ) - c))
      (𝓝[criticalSpeedCone κ] (gaussianCriticalSpeed : ℂ)) (𝓝 (Iplus a b g)) ∧
    (Iplus a b g).im = Real.pi * Wlog neutralCriticalTime * g neutralCriticalTime /
      |deriv neutralOmega neutralCriticalTime| := by
  refine ⟨?_, Iplus_im a b g⟩
  set s := neutralCriticalTime with hs
  set d := deriv neutralOmega s with hd
  have hd0 : d < 0 := deriv_neutralOmega_critical_neg
  have hsI : s ∈ Icc a b := ⟨ha.le, hb.le⟩
  -- lower bound on |Ω'| on [a, b]
  set Ω' : ℝ → ℝ := fun x => -2 * neutralRadius x * neutralOmega x with hΩ'
  have hΩ'c : Continuous Ω' := by
    rw [hΩ']
    exact (continuous_const.mul continuous_neutralRadius).mul continuous_neutralOmega
  have hΩ'pos : ∀ x, 0 < |Ω' x| := by
    intro x
    apply abs_pos.mpr
    have h1 := neutralRadius_pos x
    have h2 : 0 < neutralOmega x := Real.exp_pos _
    rw [hΩ']
    exact (mul_neg_of_neg_of_pos (by linarith) h2).ne
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (ha.trans hb).le)
    (hΩ'c.abs.continuousOn (s := Icc a b))
  set m := |Ω' x₀| with hm
  have hm0 : 0 < m := hΩ'pos x₀
  have h1 : ∀ t ∈ Icc a b, m * |t - s| ≤ |neutralOmega t - gaussianCriticalSpeed| := by
    intro t ht
    have h := mul_abs_sub_le_abs_sub_of_deriv (F := neutralOmega) (F' := Ω')
      (fun x => hasDerivAt_neutralOmega x) (fun x hx => hmin hx) s hsI t ht
    rwa [neutralOmega_critical_eq] at h
  -- Lipschitz bound for W g
  have hf : ContDiff ℝ 1 (fun t => Wlog t * g t) :=
    (contDiff_infty.mp Wlog_smooth 1).mul hg
  obtain ⟨L, hL, hLip⟩ := exists_lipschitz_Icc hf a b
  have h2 : ∀ t ∈ Icc a b, |Wlog t * g t - Wlog s * g s| ≤ L * |t - s| :=
    fun t ht => hLip s hsI t ht
  -- Taylor bound for Ω
  obtain ⟨K, hK, hTay⟩ := exists_taylor_two_Icc neutralOmega_smooth a b
  have h3 : ∀ t ∈ Icc a b,
      |(neutralOmega t - gaussianCriticalSpeed) - d * (t - s)| ≤ K * (t - s) ^ 2 := by
    intro t ht
    have h := hTay s hsI t ht
    rwa [neutralOmega_critical_eq] at h
  have hmain := tendsto_integral_cauchy_cone (Φ := fun t => neutralOmega t - gaussianCriticalSpeed)
    (f := fun t => Wlog t * g t) ha hb hκ hd0 hm0 hL hK
    (continuous_neutralOmega.sub continuous_const) hf.continuous h1 h2 h3
  have hshift : Tendsto (fun c : ℂ => c - (gaussianCriticalSpeed : ℂ))
      (𝓝[criticalSpeedCone κ] (gaussianCriticalSpeed : ℂ)) (𝓝[approachCone κ] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h : Tendsto (fun c : ℂ => c - (gaussianCriticalSpeed : ℂ))
          (𝓝 (gaussianCriticalSpeed : ℂ))
          (𝓝 ((gaussianCriticalSpeed : ℂ) - (gaussianCriticalSpeed : ℂ))) :=
        tendsto_id.sub tendsto_const_nhds
      rw [sub_self] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with c hc
      exact hc
  have hcomp := hmain.comp hshift
  refine Tendsto.congr ?_ hcomp
  intro c
  simp only [Function.comp_apply]
  apply intervalIntegral.integral_congr
  intro t _
  simp only
  congr 1
  push_cast
  ring

end UnforcedLeray.Rayleigh.Evans
