import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5
import NonUniqueEuler.P.Infra.ConvMinkowski.Minkowski

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace LIP

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



/-- Lebesgue integrals of a `c`-periodic function over `Ioc A (A + c)` are translation invariant. -/
theorem lintegral_shift_Ioc {φ : ℝ → ℝ≥0∞} {c : ℝ} (hc : 0 < c) (hφ : Function.Periodic φ c)
    (A s : ℝ) : ∫⁻ x in Ioc A (A + c), φ (x + s) = ∫⁻ x in Ioc A (A + c), φ x := by
  have hpre : (fun x : ℝ => x + s) ⁻¹' Ioc (A + s) (A + s + c) = Ioc A (A + c) := by
    ext x
    simp only [mem_preimage, mem_Ioc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have h1 : ∫⁻ x in Ioc A (A + c), φ (x + s) = ∫⁻ y in Ioc (A + s) (A + s + c), φ y := by
    rw [← hpre]
    exact (measurePreserving_add_right volume s).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.addRight s).measurableEmbedding φ _
  have h2 : ∫⁻ y in Ioc (A + s) (A + s + c), φ y = ∫⁻ y in Ioc A (A + c), φ y := by
    refine (isAddFundamentalDomain_Ioc hc (A + s)).setLIntegral_eq
      (isAddFundamentalDomain_Ioc hc A) φ ?_
    intro g x
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 g.2
    have hg : (g : ℝ) = n • c := hn.symm
    show φ ((g : ℝ) + x) = φ x
    rw [add_comm, hg]
    exact hφ.zsmul n x
  exact h1.trans h2

/-- Translation invariance of the `L^p` norm of a `c`-periodic function on a period cell. -/
theorem eLpNorm_shift_Ioc {F : ℝ → ℂ} {c : ℝ} (hc : 0 < c) (hF : Function.Periodic F c)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp1 : p ≠ ⊤) (A s : ℝ) :
    eLpNorm (fun t => F (t + s)) p (volume.restrict (Ioc A (A + c))) =
      eLpNorm F p (volume.restrict (Ioc A (A + c))) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp1,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp1]
  congr 1
  have hφ : Function.Periodic (fun x => ‖F x‖ₑ ^ p.toReal) c := by
    intro x
    show ‖F (x + c)‖ₑ ^ p.toReal = ‖F x‖ₑ ^ p.toReal
    rw [hF x]
  exact lintegral_shift_Ioc hc hφ A s

/-- Minkowski step on a translation-invariant measure: `‖∫_0^h (h-u) f(·+u) du‖_{L^p(μ)} ≤ h² ‖f‖`. -/
theorem integral_eLpNorm_le' {f : ℝ → ℂ} (hf : Continuous f) {μ : Measure ℝ} [SigmaFinite μ]
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    (hshift : ∀ s : ℝ, eLpNorm (fun t => f (t + s)) p μ = eLpNorm f p μ)
    {h : ℝ} (hh : 0 < h) :
    eLpNorm (fun t => ∫ u in (0:ℝ)..h, ((h - u : ℝ) : ℂ) * f (t + u)) p μ ≤
      ENNReal.ofReal h * eLpNorm f p μ * ENNReal.ofReal h := by
  simp_rw [intervalIntegral.integral_of_le hh.le]
  have hF : AEStronglyMeasurable
      (Function.uncurry fun (t u : ℝ) => ((h - u : ℝ) : ℂ) * f (t + u))
      (μ.prod (volume.restrict (Ioc 0 h))) := by
    apply Continuous.aestronglyMeasurable
    exact (Complex.continuous_ofReal.comp (continuous_const.sub continuous_snd)).mul
      (hf.comp (continuous_fst.add continuous_snd))
  refine (NonUniqueEuler.Conv.eLpNorm_integral_le hF hp1 hp).trans ?_
  calc ∫⁻ u, eLpNorm (fun t => ((h - u : ℝ) : ℂ) * f (t + u)) p μ
        ∂(volume.restrict (Ioc 0 h))
      ≤ ∫⁻ _u, ENNReal.ofReal h * eLpNorm f p μ ∂(volume.restrict (Ioc 0 h)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
        have hsm : (fun t => ((h - u : ℝ) : ℂ) * f (t + u)) =
            ((h - u : ℝ) : ℂ) • (fun t => f (t + u)) := rfl
        have hn : ‖((h - u : ℝ) : ℂ)‖ₑ ≤ ENNReal.ofReal h := by
          rw [← ofReal_norm]
          apply ENNReal.ofReal_le_ofReal
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hu.2])]
          linarith [hu.1]
        rw [hsm, eLpNorm_const_smul, hshift u]
        exact mul_le_mul_of_nonneg_right hn (by positivity)
    _ = ENNReal.ofReal h * eLpNorm f p μ * ENNReal.ofReal h := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]

end LIP

theorem lineInterpPer_proof : UnforcedLeray.Short.IIb.LineInterpPer := by
  intro r hr
  refine ⟨2, two_pos, fun c hc g hg hper lam hlam => ?_⟩
  have hper' : Function.Periodic g c := hper
  have hg2 : ContDiff ℝ (1 + 1) g := hg
  have hg1 : ContDiff ℝ 1 (deriv g) := hg2.deriv'
  have hgc : Continuous g := hg.continuous
  have hgd1c : Continuous (deriv g) := hg1.continuous
  have hfc : Continuous (deriv (deriv g)) := hg1.continuous_deriv le_rfl
  have hd1per : Function.Periodic (deriv g) c := fun t => by
    have e : (fun x => g (x + c)) = g := funext hper
    have := deriv_comp_add_const (f := g) (a := c) (x := t)
    rw [e] at this
    exact this.symm
  have hd2per : Function.Periodic (deriv (deriv g)) c := fun t => by
    have e : (fun x => deriv g (x + c)) = deriv g := funext hd1per
    have := deriv_comp_add_const (f := deriv g) (a := c) (x := t)
    rw [e] at this
    exact this.symm
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr.le
  have hp : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hpt : deriv g = fun t => ((lam⁻¹ : ℝ) : ℂ) * (g (t + lam) - g t -
      ∫ u in (0:ℝ)..lam, ((lam - u : ℝ) : ℂ) * deriv (deriv g) (t + u)) := by
    funext t
    rw [← LIP.taylor_int hg t lam]
    have hl : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
    push_cast
    field_simp
    ring
  have hIc : Continuous (fun t => ∫ u in (0:ℝ)..lam,
      ((lam - u : ℝ) : ℂ) * deriv (deriv g) (t + u)) := by
    have e : (fun t => ∫ u in (0:ℝ)..lam, ((lam - u : ℝ) : ℂ) * deriv (deriv g) (t + u)) =
        fun t => g (t + lam) - g t - (lam : ℂ) * deriv g t :=
      funext fun t => (LIP.taylor_int hg t lam).symm
    rw [e]
    exact ((hgc.comp (continuous_add_const lam)).sub hgc).sub (continuous_const.mul hgd1c)
  set μ : Measure ℝ := volume.restrict (Ico (-c / 2) (c / 2)) with hμ
  have e1 := congrArg (fun φ => eLpNorm φ (ENNReal.ofReal r) μ) hpt
  rw [e1]
  have hnorm : ‖((lam⁻¹ : ℝ) : ℂ)‖ₑ = ENNReal.ofReal lam⁻¹ := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hlam.le)]
  have hsm : ∀ F : ℝ → ℂ, eLpNorm (fun t => ((lam⁻¹ : ℝ) : ℂ) * F t) (ENNReal.ofReal r) μ
      = ENNReal.ofReal lam⁻¹ * eLpNorm F (ENNReal.ofReal r) μ := by
    intro F
    rw [show (fun t => ((lam⁻¹ : ℝ) : ℂ) * F t) = ((lam⁻¹ : ℝ) : ℂ) • F from rfl,
      eLpNorm_const_smul, hnorm]
  rw [hsm]
  have hcell : μ = volume.restrict (Ioc (-c / 2) (-c / 2 + c)) := by
    have hb : -c / 2 + c = c / 2 := by ring
    rw [hμ, Measure.restrict_congr_set Ico_ae_eq_Ioc, hb]
  have hA : eLpNorm (fun t => g (t + lam)) (ENNReal.ofReal r) μ =
      eLpNorm g (ENNReal.ofReal r) μ := by
    rw [hcell]
    exact LIP.eLpNorm_shift_Ioc hc hper' hp0 hp (-c / 2) lam
  have hshiftF : ∀ s : ℝ, eLpNorm (fun t => deriv (deriv g) (t + s)) (ENNReal.ofReal r) μ =
      eLpNorm (deriv (deriv g)) (ENNReal.ofReal r) μ := by
    intro s
    rw [hcell]
    exact LIP.eLpNorm_shift_Ioc hc hd2per hp0 hp (-c / 2) s
  have hI := LIP.integral_eLpNorm_le' hfc hp1 hp hshiftF hlam
  have hAA : AEStronglyMeasurable (fun t => g (t + lam) - g t) μ :=
    ((hgc.comp (continuous_add_const lam)).sub hgc).aestronglyMeasurable
  have hII : AEStronglyMeasurable (fun t => ∫ u in (0:ℝ)..lam,
      ((lam - u : ℝ) : ℂ) * deriv (deriv g) (t + u)) μ := hIc.aestronglyMeasurable
  have hEst : eLpNorm (fun t => g (t + lam) - g t - ∫ u in (0:ℝ)..lam,
      ((lam - u : ℝ) : ℂ) * deriv (deriv g) (t + u)) (ENNReal.ofReal r) μ ≤
      eLpNorm g (ENNReal.ofReal r) μ + eLpNorm g (ENNReal.ofReal r) μ +
        ENNReal.ofReal lam * eLpNorm (deriv (deriv g)) (ENNReal.ofReal r) μ *
          ENNReal.ofReal lam := by
    refine (eLpNorm_sub_le hAA hII hp1).trans ?_
    refine add_le_add ?_ hI
    refine (eLpNorm_sub_le (hgc.comp (continuous_add_const lam)).aestronglyMeasurable
      hgc.aestronglyMeasurable hp1).trans ?_
    show eLpNorm (fun t => g (t + lam)) (ENNReal.ofReal r) μ +
      eLpNorm g (ENNReal.ofReal r) μ ≤ _
    rw [hA]
  have hab : ENNReal.ofReal lam⁻¹ * ENNReal.ofReal lam = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hlam.le), inv_mul_cancel₀ hlam.ne',
      ENNReal.ofReal_one]
  refine (mul_le_mul_of_nonneg_left hEst (by positivity)).trans ?_
  have h2 : ENNReal.ofReal 2 = 2 := by norm_num
  rw [h2]
  calc ENNReal.ofReal lam⁻¹ * (eLpNorm g (ENNReal.ofReal r) μ +
          eLpNorm g (ENNReal.ofReal r) μ +
          ENNReal.ofReal lam * eLpNorm (deriv (deriv g)) (ENNReal.ofReal r) μ *
            ENNReal.ofReal lam)
      = 2 * (ENNReal.ofReal lam⁻¹ * eLpNorm g (ENNReal.ofReal r) μ) +
          (ENNReal.ofReal lam⁻¹ * ENNReal.ofReal lam) *
            (ENNReal.ofReal lam * eLpNorm (deriv (deriv g)) (ENNReal.ofReal r) μ) := by ring
    _ = 2 * (ENNReal.ofReal lam⁻¹ * eLpNorm g (ENNReal.ofReal r) μ) +
          ENNReal.ofReal lam * eLpNorm (deriv (deriv g)) (ENNReal.ofReal r) μ := by
        rw [hab, one_mul]
    _ ≤ 2 * (ENNReal.ofReal lam⁻¹ * eLpNorm g (ENNReal.ofReal r) μ) +
          2 * (ENNReal.ofReal lam * eLpNorm (deriv (deriv g)) (ENNReal.ofReal r) μ) := by
        have hb : (0:ℝ≥0∞) ≤ ENNReal.ofReal lam * eLpNorm (deriv (deriv g)) (ENNReal.ofReal r) μ := by
          positivity
        exact add_le_add le_rfl (le_mul_of_one_le_left hb one_le_two)
    _ = 2 * (ENNReal.ofReal lam⁻¹ * eLpNorm g (ENNReal.ofReal r) μ +
          ENNReal.ofReal lam * eLpNorm (deriv (deriv g)) (ENNReal.ofReal r) μ) := by ring

end UnforcedLeray.Short.IIb
