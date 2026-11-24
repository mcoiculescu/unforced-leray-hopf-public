import UnforcedLeray.Analysis.Rayleigh.RealSpeed.WeakRegularityBasic
import UnforcedLeray.Analysis.Rayleigh.RealSpeed.QuotientRemoval
import UnforcedLeray.Analysis.Rayleigh.RealSpeed.WeakCriticalTrace
import UnforcedLeray.Analysis.Rayleigh.RealSpeed.WeakNeutralSpeed
import UnforcedLeray.Analysis.Rayleigh.RealSpeed.ComplexClassicalExclusion
import UnforcedLeray.Analysis.Rayleigh.WeakH2Representative

/-!
# No nonzero weak H² Gaussian Rayleigh mode on the whole line has a real speed

Wave 2 block 2H PLAN1b (INF18 O8 input). `paper/main.tex` lines 1088--1121
(§`sec:st18-1257`, "Exclusion of every real limiting speed", eqs. `st18-t00040`,
`st18-t00041`; blueprint units B0042--B0045).

*Provenance.* Copy, with namespace `UnforcedLeray.ComplexODEB` in place of
`UnforcedLeray.Rayleigh.RealSpeed`, of the uncompiled drafts



All hypotheses concern actual global L² classes, their weak derivatives, and the
undivided equation `(Ω - c)(F'' - 4F) - AF = 0` almost everywhere. At a real speed
`c ≠ a_*` the equation forces the critical trace to vanish (compiled
`WeakCriticalTrace`), the divided differences give a continuous second-derivative
source across the critical point (compiled `QuotientRemoval`), the Green reconstruction
upgrades the mode to `C²` (compiled `WeakRegularityBasic`), and the compiled classical
exclusion `classical_complex_real_mode_eq_zero` (ground-state factorization, eq.
`st18-t00040`, at every real speed, the endpoint speeds `0` and `1` included) applies. The
neutral speed `c = a_*` is the compiled `weak_critical_rayleigh_eq_zero`.
-/

set_option autoImplicit false

noncomputable section
open MeasureTheory Set Filter
namespace UnforcedLeray.ComplexODEB
open UnforcedLeray.Rayleigh UnforcedLeray.Rayleigh.RealSpeed
open Sturm NonUniqueEuler.Sob

/-- Literal cancellation of the undivided equation at a nonsingular point. -/
theorem second_eq_divided_source {c t : ℝ} {d F : ℂ}
    (ht : neutralOmega t ≠ c)
    (heq : ((neutralOmega t : ℂ) - (c : ℂ)) * (d - 4 * F) -
      (gaussianRayleighCoefficient t : ℂ) * F = 0) :
    d = (4 : ℝ) • F + (gaussianRayleighCoefficient t / (neutralOmega t - c)) • F := by
  have hd : (neutralOmega t : ℂ) - (c : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr ht
  have hq : (gaussianRayleighCoefficient t : ℂ) /
      ((neutralOmega t : ℂ) - (c : ℂ)) * F = d - 4 * F := by
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff hd).mpr
    linear_combination -heq
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_sub,
    Complex.ofReal_ofNat]
  rw [hq]
  ring

/-- The actual weak equation and actual L² data supply every nonneutral
critical trace. -/
theorem weak_rayleigh_trace_zero {u du ddu : ComplexL2}
    (v : C1L2Representative u du) {c : ℝ} (hc : c ≠ gaussianCriticalSpeed)
    (heq : ∀ᵐ t ∂volume,
      ((neutralOmega t : ℂ) - (c : ℂ)) * (ddu t - 4 * u t) -
        (gaussianRayleighCoefficient t : ℂ) * u t = 0) :
    ∀ a, neutralOmega a = c → v.value a = 0 := by
  intro a ha
  apply complex_weak_value_zero_at_critical ha hc v.continuous.continuousAt
    ((Lp.memLp ddu).sub ((Lp.memLp u).const_mul (4 : ℂ)))
  filter_upwards [heq, v.value_ae] with t ht huv
  simpa only [Pi.sub_apply, huv] using ht

/-- Actual H² modes at every nonneutral real speed are classical C² modes.
This theorem does not assume a pointwise equation at the critical point. -/
theorem weak_rayleigh_contDiff_two {u du ddu : ComplexL2}
    (v : C1L2Representative u du)
    (h2 : HasWeakDerivOn univ (derivList 2) (u : ℝ → ℂ) (ddu : ℝ → ℂ))
    {c : ℝ} (hc : c ≠ gaussianCriticalSpeed)
    (heq : ∀ᵐ t ∂volume,
      ((neutralOmega t : ℂ) - (c : ℂ)) * (ddu t - 4 * u t) -
        (gaussianRayleighCoefficient t : ℂ) * u t = 0) :
    ContDiff ℝ 2 v.value ∧ (ddu : ℝ → ℂ) =ᵐ[volume] deriv (deriv v.value) := by
  have htrace := weak_rayleigh_trace_zero v hc heq
  have hrep : ∀ᵐ t ∂volume,
      ((neutralOmega t : ℂ) - (c : ℂ)) * (ddu t - 4 * v.value t) -
        (gaussianRayleighCoefficient t : ℂ) * v.value t = 0 := by
    filter_upwards [heq, v.value_ae] with t ht hu
    simpa only [hu] using ht
  by_cases hz : ∃ a, neutralOmega a = c
  · obtain ⟨a, ha⟩ := hz
    have hs : Continuous (gaussianRemovedSecondSource v.value c a) :=
      gaussianRemovedSecondSource_continuous v.contDiff ha
    have hsAE : (ddu : ℝ → ℂ) =ᵐ[volume] gaussianRemovedSecondSource v.value c a := by
      filter_upwards [hrep, show ∀ᵐ t ∂volume, t ≠ a from
        (ae_iff.mpr (by simp))] with t ht hta
      rw [gaussianRemovedSecondSource_eq_div (htrace a ha) ha hta]
      exact second_eq_divided_source
        (fun he => hta (neutralOmega_injective (he.trans ha.symm))) ht
    obtain ⟨hreg, hder⟩ := c1_contDiff_two_of_continuous_second v h2 hs hsAE
    exact ⟨hreg, by simpa only [hder] using hsAE⟩
  · have hne : ∀ t, neutralOmega t ≠ c := fun t ht => hz ⟨t, ht⟩
    let s : ℝ → ℂ := fun t => (4 : ℝ) • v.value t +
      (gaussianRayleighCoefficient t / (neutralOmega t - c)) • v.value t
    have hs : Continuous s := by
      dsimp [s]
      exact ((continuous_const : Continuous fun _ : ℝ => (4 : ℝ)).smul v.continuous).add
        ((gaussianCoefficient_continuous.div
          (continuous_neutralOmega.sub continuous_const)
          (fun t => sub_ne_zero.mpr (hne t))).smul v.continuous)
    have hsAE : (ddu : ℝ → ℂ) =ᵐ[volume] s :=
      hrep.mono (fun t ht => second_eq_divided_source (hne t) ht)
    obtain ⟨hreg, hder⟩ := c1_contDiff_two_of_continuous_second v h2 hs hsAE
    exact ⟨hreg, by simpa only [hder] using hsAE⟩

/-- Once regularity is proved, continuity promotes the actual a.e. equation
 to an everywhere equation, including the real critical point. -/
theorem weak_rayleigh_equation_everywhere {u du ddu : ComplexL2}
    (v : C1L2Representative u du)
    (h2 : HasWeakDerivOn univ (derivList 2) (u : ℝ → ℂ) (ddu : ℝ → ℂ))
    {c : ℝ} (hc : c ≠ gaussianCriticalSpeed)
    (heq : ∀ᵐ t ∂volume,
      ((neutralOmega t : ℂ) - (c : ℂ)) * (ddu t - 4 * u t) -
        (gaussianRayleighCoefficient t : ℂ) * u t = 0) :
    ∀ t, ((neutralOmega t : ℂ) - (c : ℂ)) *
      (deriv (deriv v.value) t - 4 * v.value t) -
        (gaussianRayleighCoefficient t : ℂ) * v.value t = 0 := by
  obtain ⟨hreg, hdd⟩ := weak_rayleigh_contDiff_two v h2 hc heq
  have hcdd : Continuous (deriv (deriv v.value)) := by
    exact (hreg.deriv' : ContDiff ℝ 1 (deriv v.value)).continuous_deriv_one
  have hcontinuous : Continuous (fun t => ((neutralOmega t : ℂ) - (c : ℂ)) *
      (deriv (deriv v.value) t - 4 * v.value t) -
        (gaussianRayleighCoefficient t : ℂ) * v.value t) :=
    (((Complex.continuous_ofReal.comp continuous_neutralOmega).sub continuous_const).mul
      (hcdd.sub (continuous_const.mul v.continuous))).sub
        ((Complex.continuous_ofReal.comp gaussianCoefficient_continuous).mul v.continuous)
  have hzero : (fun t => ((neutralOmega t : ℂ) - (c : ℂ)) *
      (deriv (deriv v.value) t - 4 * v.value t) -
        (gaussianRayleighCoefficient t : ℂ) * v.value t) =ᵐ[volume] 0 := by
    filter_upwards [heq, v.value_ae, hdd] with t ht hu hd
    simpa only [hu, hd, Pi.zero_apply] using ht
  have hf := Measure.eq_of_ae_eq hzero hcontinuous continuous_const
  exact fun t => congrFun hf t

end UnforcedLeray.ComplexODEB

noncomputable section
open MeasureTheory Set Filter
namespace UnforcedLeray.ComplexODEB
open UnforcedLeray.Rayleigh UnforcedLeray.Rayleigh.RealSpeed
open Sturm NonUniqueEuler.Sob

/-- Full exclusion of every real speed from the actual weak H² Rayleigh
problem, including the neutral speed and the endpoint speeds zero and one. -/
theorem weak_real_rayleigh_eq_zero (u du ddu : ComplexL2)
    (h1 : HasWeakDerivOn univ (derivList 1) (u : ℝ → ℂ) (du : ℝ → ℂ))
    (h2 : HasWeakDerivOn univ (derivList 1) (du : ℝ → ℂ) (ddu : ℝ → ℂ))
    {c : ℝ}
    (heq : ∀ᵐ t ∂volume,
      ((neutralOmega t : ℂ) - (c : ℂ)) * (ddu t - 4 * u t) -
        (gaussianRayleighCoefficient t : ℂ) * u t = 0) : u = 0 := by
  by_cases hc : c = gaussianCriticalSpeed
  · subst c
    exact weak_critical_rayleigh_eq_zero u du ddu h1 h2 heq
  · let v := weakH2C1Representative u du ddu h1 h2
    have hsecond : HasWeakDerivOn univ (derivList 2)
        (u : ℝ → ℂ) (ddu : ℝ → ℂ) := h1.trans h2
    obtain ⟨hreg, hdd⟩ := weak_rayleigh_contDiff_two v hsecond hc heq
    have hzero : v.value = 0 :=
      classical_complex_real_mode_eq_zero hreg v.memLp v.deriv_memLp
        ((Lp.memLp ddu).ae_eq hdd)
        (weak_rayleigh_equation_everywhere v hsecond hc heq)
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [v.value_ae] with t ht
    simpa only [hzero, Pi.zero_apply] using ht

/-- The residual formulation produced by annular compactness has exactly the
same exclusion, without assuming a successive weak derivative separately. -/
theorem weak_real_rayleigh_residual_eq_zero (u du k : ComplexL2)
    (h1 : HasWeakDerivOn univ [1] (u : ℝ → ℂ) (du : ℝ → ℂ))
    (h2 : HasWeakDerivOn univ [1, 1] (u : ℝ → ℂ)
      ((k + (4 : ℂ) • u : ComplexL2) : ℝ → ℂ))
    {c : ℝ}
    (heq : ∀ᵐ t ∂volume,
      ((neutralOmega t : ℂ) - (c : ℂ)) * k t -
        (gaussianRayleighCoefficient t : ℂ) * u t = 0) : u = 0 := by
  apply weak_real_rayleigh_eq_zero u du (k + (4 : ℂ) • u) h1
    (hasWeakDerivOn_first_of_second h1 h2)
  filter_upwards [heq, Lp.coeFn_add k ((4 : ℂ) • u),
    Lp.coeFn_smul (4 : ℂ) u] with t ht hadd hsm
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hadd hsm
  rw [hadd, hsm, add_sub_cancel_right]
  exact ht

/-- A complex speed of a nonzero actual weak H² mode cannot lie on the real
axis. This matches the undivided residual of the extracted whole-line limit. -/
theorem weak_rayleigh_speed_im_ne_zero (u du k : ComplexL2) (hu : u ≠ 0)
    (h1 : HasWeakDerivOn univ [1] (u : ℝ → ℂ) (du : ℝ → ℂ))
    (h2 : HasWeakDerivOn univ [1, 1] (u : ℝ → ℂ)
      ((k + (4 : ℂ) • u : ComplexL2) : ℝ → ℂ))
    {c : ℂ}
    (heq : ∀ᵐ t ∂volume,
      ((neutralOmega t : ℂ) - c) * k t -
        (gaussianRayleighCoefficient t : ℂ) * u t = 0) : c.im ≠ 0 := by
  intro hc
  have hreal : (c.re : ℂ) = c := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using hc.symm
  apply hu
  apply weak_real_rayleigh_residual_eq_zero u du k h1 h2 (c := c.re)
  simpa only [hreal] using heq

end UnforcedLeray.ComplexODEB
