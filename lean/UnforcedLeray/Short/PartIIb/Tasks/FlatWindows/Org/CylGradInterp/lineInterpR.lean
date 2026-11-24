import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5
import NonUniqueEuler.P.Infra.ConvMinkowski.Minkowski

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace LIR

/-- Taylor formula with integral remainder along a line. -/
theorem taylor_int {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (t h : ℝ) :
    g (t + h) - g t - (h : ℂ) * deriv g t =
      ∫ u in (0:ℝ)..h, ((h - u : ℝ) : ℂ) * deriv (deriv g) (t + u) := by
  have hg2 : ContDiff ℝ (1 + 1) g := hg
  have hg1 : ContDiff ℝ 1 (deriv g) := hg2.deriv'
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hgd1 : Differentiable ℝ (deriv g) := hg1.differentiable (by norm_num)
  have hcont : Continuous (deriv (deriv g)) := hg1.continuous_deriv le_rfl
  have hD : ∀ u : ℝ, HasDerivAt (fun u : ℝ => ((h - u : ℝ) : ℂ) * deriv g (t + u) + g (t + u))
      (((h - u : ℝ) : ℂ) * deriv (deriv g) (t + u)) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => g (t + u)) (deriv g (t + u)) u :=
      HasDerivAt.comp_const_add t u (hgd (t + u)).hasDerivAt
    have h2 : HasDerivAt (fun u : ℝ => deriv g (t + u)) (deriv (deriv g) (t + u)) u :=
      HasDerivAt.comp_const_add t u (hgd1 (t + u)).hasDerivAt
    have h3 : HasDerivAt (fun u : ℝ => ((h - u : ℝ) : ℂ)) (-1 : ℂ) u := by
      have := ((hasDerivAt_id u).const_sub h).ofReal_comp
      simpa using this
    exact ((h3.mul h2).add h1).congr_deriv (by ring)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u : ℝ => ((h - u : ℝ) : ℂ) * deriv g (t + u) + g (t + u))
    (f' := fun u : ℝ => ((h - u : ℝ) : ℂ) * deriv (deriv g) (t + u))
    (a := 0) (b := h) (fun u _ => hD u)
    (by
      apply Continuous.intervalIntegrable
      exact (Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).mul
        (hcont.comp (continuous_const.add continuous_id)))
  rw [hftc]
  simp only [sub_self, sub_zero, add_zero]
  push_cast
  ring


/-- Minkowski step: the `L^p` norm of `t ↦ ∫_0^h (h-u) f(t+u) du` is at most `h² ‖f‖_p`. -/
theorem integral_eLpNorm_le {f : ℝ → ℂ} (hf : Continuous f) {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp : p ≠ ⊤) {h : ℝ} (hh : 0 < h) :
    eLpNorm (fun t => ∫ u in (0:ℝ)..h, ((h - u : ℝ) : ℂ) * f (t + u)) p volume ≤
      ENNReal.ofReal h * eLpNorm f p volume * ENNReal.ofReal h := by
  simp_rw [intervalIntegral.integral_of_le hh.le]
  have hF : AEStronglyMeasurable
      (Function.uncurry fun (t u : ℝ) => ((h - u : ℝ) : ℂ) * f (t + u))
      (volume.prod (volume.restrict (Ioc 0 h))) := by
    apply Continuous.aestronglyMeasurable
    exact (Complex.continuous_ofReal.comp (continuous_const.sub continuous_snd)).mul
      (hf.comp (continuous_fst.add continuous_snd))
  refine (NonUniqueEuler.Conv.eLpNorm_integral_le hF hp1 hp).trans ?_
  calc ∫⁻ u, eLpNorm (fun t => ((h - u : ℝ) : ℂ) * f (t + u)) p volume
        ∂(volume.restrict (Ioc 0 h))
      ≤ ∫⁻ _u, ENNReal.ofReal h * eLpNorm f p volume ∂(volume.restrict (Ioc 0 h)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
        have hshift : eLpNorm (fun t => f (t + u)) p volume = eLpNorm f p volume :=
          eLpNorm_comp_measurePreserving hf.aestronglyMeasurable
            (measurePreserving_add_right volume u)
        have hsm : (fun t => ((h - u : ℝ) : ℂ) * f (t + u)) =
            ((h - u : ℝ) : ℂ) • (fun t => f (t + u)) := rfl
        have hn : ‖((h - u : ℝ) : ℂ)‖ₑ ≤ ENNReal.ofReal h := by
          rw [← ofReal_norm]
          apply ENNReal.ofReal_le_ofReal
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hu.2])]
          linarith [hu.1]
        rw [hsm, eLpNorm_const_smul, hshift]
        exact mul_le_mul_of_nonneg_right hn (by positivity)
    _ = ENNReal.ofReal h * eLpNorm f p volume * ENNReal.ofReal h := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]

end LIR

theorem lineInterpR_proof : UnforcedLeray.Short.IIb.LineInterpR := by
  intro r hr
  refine ⟨2, two_pos, fun g hg _ _ lam hlam => ?_⟩
  have hg2 : ContDiff ℝ (1 + 1) g := hg
  have hg1 : ContDiff ℝ 1 (deriv g) := hg2.deriv'
  have hgc : Continuous g := hg.continuous
  have hgd1c : Continuous (deriv g) := hg1.continuous
  have hfc : Continuous (deriv (deriv g)) := hg1.continuous_deriv le_rfl
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr.le
  have hp : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpt : deriv g = fun t => ((lam⁻¹ : ℝ) : ℂ) * (g (t + lam) - g t -
      ∫ u in (0:ℝ)..lam, ((lam - u : ℝ) : ℂ) * deriv (deriv g) (t + u)) := by
    funext t
    rw [← LIR.taylor_int hg t lam]
    have hl : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
    push_cast
    field_simp
    ring
  have hIc : Continuous (fun t => ∫ u in (0:ℝ)..lam,
      ((lam - u : ℝ) : ℂ) * deriv (deriv g) (t + u)) := by
    have e : (fun t => ∫ u in (0:ℝ)..lam, ((lam - u : ℝ) : ℂ) * deriv (deriv g) (t + u)) =
        fun t => g (t + lam) - g t - (lam : ℂ) * deriv g t :=
      funext fun t => (LIR.taylor_int hg t lam).symm
    rw [e]
    exact ((hgc.comp (continuous_add_const lam)).sub hgc).sub (continuous_const.mul hgd1c)
  have e1 := congrArg (fun φ => eLpNorm φ (ENNReal.ofReal r) volume) hpt
  rw [e1]
  have hnorm : ‖((lam⁻¹ : ℝ) : ℂ)‖ₑ = ENNReal.ofReal lam⁻¹ := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hlam.le)]
  have hsm : ∀ F : ℝ → ℂ, eLpNorm (fun t => ((lam⁻¹ : ℝ) : ℂ) * F t) (ENNReal.ofReal r) volume
      = ENNReal.ofReal lam⁻¹ * eLpNorm F (ENNReal.ofReal r) volume := by
    intro F
    rw [show (fun t => ((lam⁻¹ : ℝ) : ℂ) * F t) = ((lam⁻¹ : ℝ) : ℂ) • F from rfl,
      eLpNorm_const_smul, hnorm]
  rw [hsm]
  have hA : eLpNorm (fun t => g (t + lam)) (ENNReal.ofReal r) volume =
      eLpNorm g (ENNReal.ofReal r) volume :=
    eLpNorm_comp_measurePreserving hgc.aestronglyMeasurable (measurePreserving_add_right volume lam)
  have hI := LIR.integral_eLpNorm_le hfc hp1 hp hlam
  have hAA : AEStronglyMeasurable (fun t => g (t + lam) - g t) volume :=
    ((hgc.comp (continuous_add_const lam)).sub hgc).aestronglyMeasurable
  have hII : AEStronglyMeasurable (fun t => ∫ u in (0:ℝ)..lam,
      ((lam - u : ℝ) : ℂ) * deriv (deriv g) (t + u)) volume := hIc.aestronglyMeasurable
  have hEst : eLpNorm (fun t => g (t + lam) - g t - ∫ u in (0:ℝ)..lam,
      ((lam - u : ℝ) : ℂ) * deriv (deriv g) (t + u)) (ENNReal.ofReal r) volume ≤
      eLpNorm g (ENNReal.ofReal r) volume + eLpNorm g (ENNReal.ofReal r) volume +
        ENNReal.ofReal lam * eLpNorm (deriv (deriv g)) (ENNReal.ofReal r) volume *
          ENNReal.ofReal lam := by
    refine (eLpNorm_sub_le hAA hII hp1).trans ?_
    refine add_le_add ?_ hI
    refine (eLpNorm_sub_le (hgc.comp (continuous_add_const lam)).aestronglyMeasurable
      hgc.aestronglyMeasurable hp1).trans ?_
    show eLpNorm (fun t => g (t + lam)) (ENNReal.ofReal r) volume +
      eLpNorm g (ENNReal.ofReal r) volume ≤ _
    rw [hA]
  have hab : ENNReal.ofReal lam⁻¹ * ENNReal.ofReal lam = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hlam.le), inv_mul_cancel₀ hlam.ne',
      ENNReal.ofReal_one]
  refine (mul_le_mul_of_nonneg_left hEst (by positivity)).trans ?_
  have h2 : ENNReal.ofReal 2 = 2 := by norm_num
  rw [h2]
  calc ENNReal.ofReal lam⁻¹ * (eLpNorm g (ENNReal.ofReal r) volume +
          eLpNorm g (ENNReal.ofReal r) volume +
          ENNReal.ofReal lam * eLpNorm (deriv (deriv g)) (ENNReal.ofReal r) volume *
            ENNReal.ofReal lam)
      = 2 * (ENNReal.ofReal lam⁻¹ * eLpNorm g (ENNReal.ofReal r) volume) +
          (ENNReal.ofReal lam⁻¹ * ENNReal.ofReal lam) *
            (ENNReal.ofReal lam * eLpNorm (deriv (deriv g)) (ENNReal.ofReal r) volume) := by ring
    _ = 2 * (ENNReal.ofReal lam⁻¹ * eLpNorm g (ENNReal.ofReal r) volume) +
          ENNReal.ofReal lam * eLpNorm (deriv (deriv g)) (ENNReal.ofReal r) volume := by
        rw [hab, one_mul]
    _ ≤ 2 * (ENNReal.ofReal lam⁻¹ * eLpNorm g (ENNReal.ofReal r) volume) +
          2 * (ENNReal.ofReal lam * eLpNorm (deriv (deriv g)) (ENNReal.ofReal r) volume) := by
        have hb : (0:ℝ≥0∞) ≤ ENNReal.ofReal lam * eLpNorm (deriv (deriv g)) (ENNReal.ofReal r) volume := by
          positivity
        exact add_le_add le_rfl (le_mul_of_one_le_left hb one_le_two)
    _ = 2 * (ENNReal.ofReal lam⁻¹ * eLpNorm g (ENNReal.ofReal r) volume +
          ENNReal.ofReal lam * eLpNorm (deriv (deriv g)) (ENNReal.ofReal r) volume) := by ring

end UnforcedLeray.Short.IIb
