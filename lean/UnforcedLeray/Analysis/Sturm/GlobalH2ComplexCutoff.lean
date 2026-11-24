import UnforcedLeray.Analysis.Sturm.GlobalH1CutoffErrors
import UnforcedLeray.Analysis.Sturm.GlobalH2Cutoff
import UnforcedLeray.Analysis.Sturm.ComplexL2Convergence
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-!
# Actual compact approximation of complex classical H² functions

The same real bump multiplies the actual complex function. Continuous real
linear projections commute with its first and second derivatives. Thus the
checked real cutoff errors give the actual complex squared-L² errors by
`‖z‖² = re(z)² + im(z)²`. No complex approximation principle is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace UnforcedLeray.Sturm.GlobalH2ComplexCutoff
open GaussianCompactTrial GlobalH1Cutoff

/-- The actual complex-valued compact cutoff. -/
def approximationC (v : ℝ → ℂ) (n : ℕ) (t : ℝ) : ℂ := cutoff n t • v t

theorem approximationC_contDiff_two {v : ℝ → ℂ} (hv : ContDiff ℝ 2 v) (n : ℕ) :
    ContDiff ℝ 2 (approximationC v n) :=
  (bump.contDiff.comp (contDiff_id.div_const (scale n))).smul hv

theorem approximationC_contDiff_infty {v : ℝ → ℂ} (hv : ContDiff ℝ ∞ v) (n : ℕ) :
    ContDiff ℝ ∞ (approximationC v n) :=
  (bump.contDiff.comp (contDiff_id.div_const (scale n))).smul hv

theorem approximationC_hasCompactSupport (v : ℝ → ℂ) (n : ℕ) :
    HasCompactSupport (approximationC v n) := by
  have hc : HasCompactSupport (cutoff n) := by
    have he : GlobalH1Cutoff.approximation (fun _ => 1) n = cutoff n := by
      funext t
      exact mul_one (cutoff n t)
    rw [← he]
    exact approximation_hasCompactSupport (fun _ => 1) n
  exact hc.smul_right

theorem approximationC_memLp_two {v : ℝ → ℂ} (hv : ContDiff ℝ 2 v) (n : ℕ) :
    MemLp (approximationC v n) 2 volume :=
  (approximationC_contDiff_two hv n).continuous.memLp_of_hasCompactSupport
    (approximationC_hasCompactSupport v n)

theorem deriv_approximationC_memLp_two {v : ℝ → ℂ} (hv : ContDiff ℝ 2 v) (n : ℕ) :
    MemLp (deriv (approximationC v n)) 2 volume :=
  ((approximationC_contDiff_two hv n).of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).continuous_deriv_one.memLp_of_hasCompactSupport
    (approximationC_hasCompactSupport v n).deriv

theorem second_deriv_approximationC_memLp_two {v : ℝ → ℂ}
    (hv : ContDiff ℝ 2 v) (n : ℕ) :
    MemLp (deriv (deriv (approximationC v n))) 2 volume := by
  have hd : ContDiff ℝ 1 (deriv (approximationC v n)) :=
    (approximationC_contDiff_two hv n).deriv'
  exact hd.continuous_deriv_one.memLp_of_hasCompactSupport
    (approximationC_hasCompactSupport v n).deriv.deriv

/-- Actual differentiation commutes with every continuous real scalar projection. -/
theorem deriv_projection {v : ℝ → ℂ} (hv : Differentiable ℝ v) (L : ℂ →L[ℝ] ℝ) :
    deriv (fun t => L (v t)) = fun t => L (deriv v t) := by
  funext t
  exact (L.hasFDerivAt.comp_hasDerivAt t (hv t).hasDerivAt).deriv

theorem second_deriv_projection {v : ℝ → ℂ} (hv : ContDiff ℝ 2 v)
    (L : ℂ →L[ℝ] ℝ) :
    deriv (deriv (fun t => L (v t))) = fun t => L (deriv (deriv v) t) := by
  rw [deriv_projection (hv.differentiable (by norm_num)) L]
  exact deriv_projection hv.differentiable_deriv_two L

theorem approximationC_projection (v : ℝ → ℂ) (L : ℂ →L[ℝ] ℝ) (n : ℕ) :
    (fun t => L (approximationC v n t)) = GlobalH1Cutoff.approximation (fun t => L (v t)) n := by
  funext t
  simp only [approximationC, GlobalH1Cutoff.approximation, map_smul, smul_eq_mul]

theorem deriv_approximationC_projection {v : ℝ → ℂ} (hv : ContDiff ℝ 2 v)
    (L : ℂ →L[ℝ] ℝ) (n : ℕ) :
    (fun t => L (deriv (approximationC v n) t)) =
      deriv (GlobalH1Cutoff.approximation (fun t => L (v t)) n) := by
  rw [← deriv_projection ((approximationC_contDiff_two hv n).differentiable (by norm_num)) L]
  rw [approximationC_projection]

theorem second_deriv_approximationC_projection {v : ℝ → ℂ} (hv : ContDiff ℝ 2 v)
    (L : ℂ →L[ℝ] ℝ) (n : ℕ) :
    (fun t => L (deriv (deriv (approximationC v n)) t)) =
      deriv (deriv (GlobalH1Cutoff.approximation (fun t => L (v t)) n)) := by
  rw [← second_deriv_projection (approximationC_contDiff_two hv n) L]
  rw [approximationC_projection]

/-- The complex square norm is the sum of the two real square errors. -/
theorem integral_norm_sub_sq {f g : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) :
    (∫ t, ‖f t - g t‖ ^ 2) =
      (∫ t, ((f t).re - (g t).re) ^ 2) +
      (∫ t, ((f t).im - (g t).im) ^ 2) := by
  have he : ∀ t, ‖f t - g t‖ ^ 2 =
      ((f t).re - (g t).re) ^ 2 + ((f t).im - (g t).im) ^ 2 := by
    intro t
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, pow_two]
  simp_rw [he]
  exact integral_add (hf.re.sub hg.re).integrable_sq (hf.im.sub hg.im).integrable_sq

/-- Componentwise square-error convergence implies actual complex square-error convergence. -/
theorem integral_error_tendsto_of_re_im {F : ℕ → ℝ → ℂ} {f : ℝ → ℂ}
    (hF : ∀ n, MemLp (F n) 2 volume) (hf : MemLp f 2 volume)
    (hr : Tendsto (fun n => ∫ t, ((F n t).re - (f t).re) ^ 2) atTop (𝓝 (0 : ℝ)))
    (hi : Tendsto (fun n => ∫ t, ((F n t).im - (f t).im) ^ 2) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n => ∫ t, ‖F n t - f t‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
  simpa only [integral_norm_sub_sq (hF _) hf, zero_add] using hr.add hi

/-- Actual complex cutoff values converge strongly in squared L² norm. -/
theorem integral_value_error_tendsto_zero {v : ℝ → ℂ} (hv : ContDiff ℝ 2 v)
    (hv2 : MemLp v 2 volume) :
    Tendsto (fun n => ∫ t, ‖approximationC v n t - v t‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
  apply integral_error_tendsto_of_re_im (approximationC_memLp_two hv) hv2
  · have hr := GlobalH1CutoffErrors.integral_value_error_tendsto_zero
      ((Complex.reCLM.contDiff.comp hv).of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)) hv2.re
    simpa only [approximationC, GlobalH1Cutoff.approximation, Complex.smul_re, smul_eq_mul,
      Function.comp_def, Complex.reCLM_apply] using hr
  · have hi := GlobalH1CutoffErrors.integral_value_error_tendsto_zero
      ((Complex.imCLM.contDiff.comp hv).of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)) hv2.im
    simpa only [approximationC, GlobalH1Cutoff.approximation, Complex.smul_im, smul_eq_mul,
      Function.comp_def, Complex.imCLM_apply] using hi

/-- Actual first complex derivatives converge strongly in squared L² norm. -/
theorem integral_deriv_error_tendsto_zero {v : ℝ → ℂ} (hv : ContDiff ℝ 2 v)
    (hv2 : MemLp v 2 volume) (hdv2 : MemLp (deriv v) 2 volume) :
    Tendsto (fun n => ∫ t, ‖deriv (approximationC v n) t - deriv v t‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
  apply integral_error_tendsto_of_re_im (deriv_approximationC_memLp_two hv) hdv2
  · have hd : deriv (fun t => (v t).re) = fun t => (deriv v t).re :=
      deriv_projection (hv.differentiable (by norm_num)) Complex.reCLM
    have hmem : MemLp (deriv (fun t => (v t).re)) 2 volume := by rw [hd]; exact hdv2.re
    have hr := GlobalH1CutoffErrors.integral_deriv_error_tendsto_zero
      ((Complex.reCLM.contDiff.comp hv).of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)) hv2.re hmem
    have he (n : ℕ) (t : ℝ) : (deriv (approximationC v n) t).re =
        deriv (GlobalH1Cutoff.approximation (fun t => (v t).re) n) t :=
      congrFun (deriv_approximationC_projection hv Complex.reCLM n) t
    have hp (t : ℝ) : (deriv v t).re = deriv (fun t => (v t).re) t := (congrFun hd t).symm
    simpa only [he, hp, Function.comp_def, Complex.reCLM_apply] using hr
  · have hd : deriv (fun t => (v t).im) = fun t => (deriv v t).im :=
      deriv_projection (hv.differentiable (by norm_num)) Complex.imCLM
    have hmem : MemLp (deriv (fun t => (v t).im)) 2 volume := by rw [hd]; exact hdv2.im
    have hi := GlobalH1CutoffErrors.integral_deriv_error_tendsto_zero
      ((Complex.imCLM.contDiff.comp hv).of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)) hv2.im hmem
    have he (n : ℕ) (t : ℝ) : (deriv (approximationC v n) t).im =
        deriv (GlobalH1Cutoff.approximation (fun t => (v t).im) n) t :=
      congrFun (deriv_approximationC_projection hv Complex.imCLM n) t
    have hp (t : ℝ) : (deriv v t).im = deriv (fun t => (v t).im) t := (congrFun hd t).symm
    simpa only [he, hp, Function.comp_def, Complex.imCLM_apply] using hi

/-- Actual second complex derivatives converge strongly in squared L² norm. -/
theorem integral_second_error_tendsto_zero {v : ℝ → ℂ} (hv : ContDiff ℝ 2 v)
    (hv2 : MemLp v 2 volume) (hdv2 : MemLp (deriv v) 2 volume)
    (hddv2 : MemLp (deriv (deriv v)) 2 volume) :
    Tendsto (fun n => ∫ t, ‖deriv (deriv (approximationC v n)) t - deriv (deriv v) t‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
  apply integral_error_tendsto_of_re_im (second_deriv_approximationC_memLp_two hv) hddv2
  · have hd : deriv (fun t => (v t).re) = fun t => (deriv v t).re :=
      deriv_projection (hv.differentiable (by norm_num)) Complex.reCLM
    have hdd : deriv (deriv (fun t => (v t).re)) = fun t => (deriv (deriv v) t).re :=
      second_deriv_projection hv Complex.reCLM
    have hmem : MemLp (deriv (fun t => (v t).re)) 2 volume := by rw [hd]; exact hdv2.re
    have hmm : MemLp (deriv (deriv (fun t => (v t).re))) 2 volume := by rw [hdd]; exact hddv2.re
    have hr := GlobalH2Cutoff.integral_second_error_tendsto_zero
      (Complex.reCLM.contDiff.comp hv) hv2.re hmem hmm
    have he (n : ℕ) (t : ℝ) : (deriv (deriv (approximationC v n)) t).re =
        deriv (deriv (GlobalH1Cutoff.approximation (fun t => (v t).re) n)) t :=
      congrFun (second_deriv_approximationC_projection hv Complex.reCLM n) t
    have hp (t : ℝ) : (deriv (deriv v) t).re = deriv (deriv (fun t => (v t).re)) t := (congrFun hdd t).symm
    simpa only [he, hp, Function.comp_def, Complex.reCLM_apply] using hr
  · have hd : deriv (fun t => (v t).im) = fun t => (deriv v t).im :=
      deriv_projection (hv.differentiable (by norm_num)) Complex.imCLM
    have hdd : deriv (deriv (fun t => (v t).im)) = fun t => (deriv (deriv v) t).im :=
      second_deriv_projection hv Complex.imCLM
    have hmem : MemLp (deriv (fun t => (v t).im)) 2 volume := by rw [hd]; exact hdv2.im
    have hmm : MemLp (deriv (deriv (fun t => (v t).im))) 2 volume := by rw [hdd]; exact hddv2.im
    have hi := GlobalH2Cutoff.integral_second_error_tendsto_zero
      (Complex.imCLM.contDiff.comp hv) hv2.im hmem hmm
    have he (n : ℕ) (t : ℝ) : (deriv (deriv (approximationC v n)) t).im =
        deriv (deriv (GlobalH1Cutoff.approximation (fun t => (v t).im) n)) t :=
      congrFun (second_deriv_approximationC_projection hv Complex.imCLM n) t
    have hp (t : ℝ) : (deriv (deriv v) t).im = deriv (deriv (fun t => (v t).im)) t := (congrFun hdd t).symm
    simpa only [he, hp, Function.comp_def, Complex.imCLM_apply] using hi

/-- Strong convergence of the actual cutoff classes in complex L². -/
theorem value_toLp_tendsto {v : ℝ → ℂ} (hv : ContDiff ℝ 2 v)
    (hv2 : MemLp v 2 volume) :
    Tendsto (fun n => (approximationC_memLp_two hv n).toLp (approximationC v n))
      atTop (𝓝 (hv2.toLp v)) :=
  ComplexL2Convergence.toLp_tendsto_of_integral_error hv2
    (approximationC_memLp_two hv) (integral_value_error_tendsto_zero hv hv2)

/-- Strong convergence of first derivative classes in complex L². -/
theorem deriv_toLp_tendsto {v : ℝ → ℂ} (hv : ContDiff ℝ 2 v)
    (hv2 : MemLp v 2 volume) (hdv2 : MemLp (deriv v) 2 volume) :
    Tendsto (fun n => (deriv_approximationC_memLp_two hv n).toLp (deriv (approximationC v n)))
      atTop (𝓝 (hdv2.toLp (deriv v))) :=
  ComplexL2Convergence.toLp_tendsto_of_integral_error hdv2
    (deriv_approximationC_memLp_two hv) (integral_deriv_error_tendsto_zero hv hv2 hdv2)

/-- Strong convergence of second derivative classes in complex L². -/
theorem second_deriv_toLp_tendsto {v : ℝ → ℂ} (hv : ContDiff ℝ 2 v)
    (hv2 : MemLp v 2 volume) (hdv2 : MemLp (deriv v) 2 volume)
    (hddv2 : MemLp (deriv (deriv v)) 2 volume) :
    Tendsto (fun n => (second_deriv_approximationC_memLp_two hv n).toLp
      (deriv (deriv (approximationC v n)))) atTop (𝓝 (hddv2.toLp (deriv (deriv v)))) :=
  ComplexL2Convergence.toLp_tendsto_of_integral_error hddv2
    (second_deriv_approximationC_memLp_two hv)
    (integral_second_error_tendsto_zero hv hv2 hdv2 hddv2)

end UnforcedLeray.Sturm.GlobalH2ComplexCutoff
