import UnforcedLeray.Analysis.Rayleigh.ResidualEstimate
import NonUniqueEuler.Defs.Infra.SobolevOneD
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Genuine H¹ zero extension of Dirichlet annular modes

The zero extension of the first derivative is a weak derivative of the zero
extension of the field. This is proved by the actual interval integration by
parts; the two Dirichlet boundary values cancel the possible jumps. Only H¹
regularity is claimed: zero extension of the first derivative may have jumps.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace UnforcedLeray.Rayleigh

/-- Extension by zero of the actual function on its annular log interval. -/
def zeroExtension (l r : ℝ) (F : ℝ → ℂ) : ℝ → ℂ :=
  (Ioc l r).indicator F

lemma zeroExtension_mul (l r : ℝ) (F G : ℝ → ℂ) :
    (fun t => zeroExtension l r F t * G t) =
      (Ioc l r).indicator (fun t => F t * G t) := by
  funext t
  by_cases ht : t ∈ Ioc l r <;> simp [zeroExtension, ht]

lemma zeroExtension_memLp {F : ℝ → ℂ} (hF : Continuous F) (l r : ℝ) :
    MemLp (zeroExtension l r F) 2 volume := by
  rw [zeroExtension, memLp_indicator_iff_restrict measurableSet_Ioc]
  exact (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mpr
    (hF.norm.pow 2).integrableOn_Ioc

lemma zeroExtension_mul_integrable {F G : ℝ → ℂ} (hF : Continuous F)
    (hG : Continuous G) (l r : ℝ) :
    Integrable (fun t => zeroExtension l r F t * G t) := by
  rw [zeroExtension_mul, integrable_indicator_iff measurableSet_Ioc]
  exact (hF.mul hG).integrableOn_Ioc

lemma integral_zeroExtension_mul (l r : ℝ) (F G : ℝ → ℂ) :
    (∫ t, zeroExtension l r F t * G t) = ∫ t in Ioc l r, F t * G t := by
  rw [zeroExtension_mul, integral_indicator measurableSet_Ioc]

/-- Exact mass correspondence between the zero extension and the interval. -/
theorem integral_norm_sq_zeroExtension (l r : ℝ) (F : ℝ → ℂ) :
    (∫ t, ‖zeroExtension l r F t‖ ^ 2) = ∫ t in Ioc l r, ‖F t‖ ^ 2 := by
  have he : (fun t => ‖zeroExtension l r F t‖ ^ 2) =
      (Ioc l r).indicator (fun t => ‖F t‖ ^ 2) := by
    funext t
    by_cases ht : t ∈ Ioc l r <;> simp [zeroExtension, ht]
  rw [he, integral_indicator measurableSet_Ioc]

/-- Actual global weak pairing, even for arbitrary C¹ tests, because the
extended field has bounded support and its two boundary traces vanish. -/
theorem zeroExtension_weak_pairing {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F)
    {l r : ℝ} (hlr : l ≤ r) (hl : F l = 0) (hr : F r = 0)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) :
    (∫ t, zeroExtension l r F t * deriv φ t) =
      -(∫ t, zeroExtension l r (deriv F) t * φ t) := by
  have hd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := F) (v := φ) (u' := deriv F) (v' := deriv φ)
    (fun x _ => (hd x).hasDerivAt)
    (fun x _ => (hφd x).hasDerivAt)
    ((hF.continuous_deriv (by norm_num)).intervalIntegrable l r)
    (hφ.continuous_deriv_one.intervalIntegrable l r)
  simp only [hl, hr, zero_mul, sub_self, zero_sub,
    intervalIntegral.integral_of_le hlr] at hi
  simpa only [integral_zeroExtension_mul] using hi

/-- Both sides of the weak pairing are genuine convergent integrals. -/
theorem zeroExtension_test_integrable {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F)
    (l r : ℝ) {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) :
    Integrable (fun t => zeroExtension l r F t * deriv φ t) ∧
    Integrable (fun t => zeroExtension l r (deriv F) t * φ t) := by
  exact ⟨zeroExtension_mul_integrable hF.continuous hφ.continuous_deriv_one l r,
    zeroExtension_mul_integrable (hF.continuous_deriv (by norm_num)) hφ.continuous l r⟩

/-- Identification with the standard reusable one-dimensional weak derivative predicate. -/
theorem zeroExtension_hasWeakDeriv {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F)
    {l r : ℝ} (hlr : l ≤ r) (hl : F l = 0) (hr : F r = 0) :
    NonUniqueEuler.Sob.HasWeakDerivOn univ [1]
      (zeroExtension l r F) (zeroExtension l r (deriv F)) := by
  intro φ hφ
  have hi := zeroExtension_weak_pairing hF hlr hl hr (hφ.smooth.of_le (by simp))
  simpa only [NonUniqueEuler.Sob.iterDirDeriv, List.foldr_cons, List.foldr_nil,
    NonUniqueEuler.Sob.dirDeriv, deriv, List.length_cons, List.length_nil,
    zero_add, pow_one, neg_one_mul] using hi

/-- The actual extension belongs to H¹, with its explicit derivative witness. -/
theorem zeroExtension_memH1 {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F)
    {l r : ℝ} (hlr : l ≤ r) (hl : F l = 0) (hr : F r = 0) :
    NonUniqueEuler.Sob.MemH1On 1 univ (zeroExtension l r F) := by
  have hf := zeroExtension_memLp hF.continuous l r
  have hg := zeroExtension_memLp (hF.continuous_deriv (by norm_num)) l r
  refine ⟨by simpa using hf, ?_⟩
  intro j hj
  interval_cases j
  · refine ⟨zeroExtension l r F, by simpa using hf, ?_⟩
    intro φ hφ
    simp [NonUniqueEuler.Sob.derivList, NonUniqueEuler.Sob.iterDirDeriv]
  · refine ⟨zeroExtension l r (deriv F), by simpa using hg, ?_⟩
    simpa only [NonUniqueEuler.Sob.derivList, List.replicate_succ, List.replicate_zero]
      using zeroExtension_hasWeakDeriv hF hlr hl hr

namespace ShiftedAnnularMode
variable {q : ℝ → ℝ} {z : ℂ} {F : ℝ → ℂ} {l r : ℝ}
  (h : ShiftedAnnularMode q z F l r)
include h

/-- The normalized annular mode has a genuine global H¹ extension. -/
theorem zeroExtension_global_H1 :
    NonUniqueEuler.Sob.MemH1On 1 univ (zeroExtension l r F) :=
  zeroExtension_memH1 h.regularity h.ordered h.left_endpoint h.right_endpoint

omit h in
theorem normalized_zeroExtension_mass
    (hmass : (∫ t in Ioc l r, ‖F t‖ ^ 2) = 1) :
    (∫ t, ‖zeroExtension l r F t‖ ^ 2) = 1 := by
  rw [integral_norm_sq_zeroExtension, hmass]

/-- The actual zero-extended derivative has squared norm at most four. -/
theorem normalized_zeroExtension_derivative_bound
    (hmass : (∫ t in Ioc l r, ‖F t‖ ^ 2) = 1) :
    (∫ t, ‖zeroExtension l r (deriv F) t‖ ^ 2) ≤ 4 := by
  rw [integral_norm_sq_zeroExtension]
  have hE := (h.normalized_energy_bounds hmass).2
  have hf : IntegrableOn (fun t => ‖F t‖ ^ 2) (Ioc l r) :=
    (h.regularity.continuous.norm.pow 2).integrableOn_Ioc
  have hg : IntegrableOn (fun t => ‖deriv F t‖ ^ 2) (Ioc l r) :=
    ((h.regularity.continuous_deriv (by norm_num)).norm.pow 2).integrableOn_Ioc
  unfold intervalEnergy intervalEnergyDensity at hE
  rw [integral_add hg (hf.const_mul 4), integral_const_mul, hmass] at hE
  linarith

/-- The full square-sum H¹ norm of these explicit witnesses is uniformly at most five. -/
theorem normalized_zeroExtension_H1_bound
    (hmass : (∫ t in Ioc l r, ‖F t‖ ^ 2) = 1) :
    (∫ t, ‖zeroExtension l r F t‖ ^ 2) +
      (∫ t, ‖zeroExtension l r (deriv F) t‖ ^ 2) ≤ 5 := by
  rw [normalized_zeroExtension_mass hmass]
  have hd := h.normalized_zeroExtension_derivative_bound hmass
  linarith

end ShiftedAnnularMode
end UnforcedLeray.Rayleigh
