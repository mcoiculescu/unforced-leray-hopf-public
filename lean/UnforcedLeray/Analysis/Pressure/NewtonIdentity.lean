import UnforcedLeray.Analysis.Pressure.NewtonKernel
import UnforcedLeray.Analysis.Heat.KernelEvolution
import UnforcedLeray.Analysis.Heat.Derivatives
import UnforcedLeray.Analysis.Pressure.HeatTest
import UnforcedLeray.Analysis.Pressure.KernelCommutation
import UnforcedLeray.TestFunctions
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The normalized Newton potential on R³

The inverse-time Gamma calculation is adapted from OpenAI's
NavierStokesAndEuler, NavierStokes/R3/HeatKernelTimeBound.lean, commit
f9e8bc5b38b6e212696e8a30e3e91517af887bbd (Apache-2.0).
This module identifies the actual normalized heat potential and its derivative.
Absolute space-time integrability and the heat equation then prove the
distributional identities `-ΔN = δ₀` and `-Δ(∂ᵢN) = ∂ᵢδ₀`, expressed
as equalities against every smooth compactly supported scalar test.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal
namespace UnforcedLeray.PressureAnalysis
private theorem inverseTimeGamma_transform (a p s : ℝ) (hs : 0 < s) :
    (|(-1 : ℝ)| * s ^ ((-1 : ℝ) - 1)) •
        ((s ^ (-1 : ℝ)) ^ (p - 1) * Real.exp (-(a * s ^ (-1 : ℝ)))) =
      s ^ (-(p + 1)) * Real.exp (-a / s) := by
  norm_num only [abs_neg, abs_one, one_mul, smul_eq_mul]
  rw [← Real.rpow_mul hs.le, ← mul_assoc, ← Real.rpow_add hs]
  congr 1
  · congr 1
    ring
  · rw [Real.rpow_neg_one]
    simp only [div_eq_mul_inv, neg_mul]

/-- The inverse-time Gaussian power is integrable for every positive shape
parameter and positive spatial scale. -/
theorem integrableOn_inverseTimeGamma {a p : ℝ} (ha : 0 < a) (hp : 0 < p) :
    IntegrableOn (fun s : ℝ => s ^ (-(p + 1)) * Real.exp (-a / s)) (Ioi 0) := by
  have hg : IntegrableOn (fun t : ℝ => t ^ (p - 1) * Real.exp (-(a * t)))
      (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := p - 1) (b := a) (by linarith) (by norm_num) ha)
  have h := (integrableOn_Ioi_comp_rpow_iff
    (fun t : ℝ => t ^ (p - 1) * Real.exp (-(a * t)))
    (p := (-1 : ℝ)) (by norm_num)).mpr hg
  exact h.congr_fun (fun s hs => inverseTimeGamma_transform a p s hs) measurableSet_Ioi

/-- Reciprocal substitution evaluates the inverse-time Gamma integral. -/
theorem integral_inverseTimeGamma {a p : ℝ} (ha : 0 < a) (hp : 0 < p) :
    (∫ s : ℝ in Ioi 0, s ^ (-(p + 1)) * Real.exp (-a / s)) =
      a ^ (-p) * Real.Gamma p := by
  calc
    (∫ s : ℝ in Ioi 0, s ^ (-(p + 1)) * Real.exp (-a / s)) =
        ∫ s : ℝ in Ioi 0, (|(-1 : ℝ)| * s ^ ((-1 : ℝ) - 1)) •
          ((s ^ (-1 : ℝ)) ^ (p - 1) * Real.exp (-(a * s ^ (-1 : ℝ)))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      exact (inverseTimeGamma_transform a p s hs).symm
    _ = ∫ t : ℝ in Ioi 0, t ^ (p - 1) * Real.exp (-(a * t)) :=
      integral_comp_rpow_Ioi (fun t : ℝ => t ^ (p - 1) * Real.exp (-(a * t)))
        (by norm_num : (-1 : ℝ) ≠ 0)
    _ = (1 / a) ^ p * Real.Gamma p :=
      Real.integral_rpow_mul_exp_neg_mul_Ioi hp ha
    _ = a ^ (-p) * Real.Gamma p := by
      rw [one_div, Real.inv_rpow ha.le, Real.rpow_neg ha.le]

private theorem square_quarter_rpow (r p : ℝ) (hr : 0 < r) :
    (r ^ 2 / 4) ^ (-p) = 4 ^ p * r ^ (-2 * p) := by
  rw [Real.div_rpow (sq_nonneg r) (by norm_num : (0 : ℝ) ≤ 4),
    ← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), div_inv_eq_mul]
  convert! mul_comm (r ^ ((2 : ℝ) * -p)) (4 ^ p) using 1
  congr 1
  ring_nf

/-- The scale occurring in the heat kernel gives the expected homogeneous
power after integration in time. -/
theorem integral_inverseTimeGamma_square_scale {r p : ℝ} (hr : 0 < r) (hp : 0 < p) :
    (∫ s : ℝ in Ioi 0, s ^ (-(p + 1)) * Real.exp (-(r ^ 2 / 4) / s)) =
      4 ^ p * r ^ (-2 * p) * Real.Gamma p := by
  rw [integral_inverseTimeGamma (by positivity) hp, square_quarter_rpow r p hr]


private theorem heat_kernel_inverseTime_formula {t : ℝ} (ht : 0 < t) (x : Space) :
    Heat.kernel t x = (4 * Real.pi) ^ (-(3:ℝ)/2) *
      (t ^ (-((1/2:ℝ)+1)) * Real.exp (-(‖x‖^2 / 4) / t)) := by
  rw [Heat.kernel_formula, Real.mul_rpow (by positivity : 0 ≤ 4 * Real.pi) ht.le]
  have he : -(4*t)⁻¹ * ‖x‖^2 = -(‖x‖^2/4)/t := by field_simp
  rw [he]
  norm_num
  ring

theorem heatKernel_integrable_time {x : Space} (hx : x ≠ 0) :
    IntegrableOn (fun t : ℝ => Heat.kernel t x) (Ioi 0) := by
  have ha : 0 < ‖x‖^2 / 4 := by positivity
  have h : IntegrableOn (fun t : ℝ => (4 * Real.pi) ^ (-(3:ℝ)/2) *
      (t ^ (-((1/2:ℝ)+1)) * Real.exp (-(‖x‖^2/4)/t))) (Ioi 0) :=
    (integrableOn_inverseTimeGamma ha (by norm_num : (0:ℝ)<1/2)).const_mul _
  exact h.congr_fun (fun t ht => (heat_kernel_inverseTime_formula ht x).symm) measurableSet_Ioi

theorem integral_heatKernel_time {x : Space} (hx : x ≠ 0) :
    (∫ t : ℝ in Ioi 0, Heat.kernel t x) = 1 / (4 * Real.pi * ‖x‖) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have he : (∫ t : ℝ in Ioi 0, Heat.kernel t x) =
      (4 * Real.pi) ^ (-(3:ℝ)/2) *
        (∫ t : ℝ in Ioi 0, t ^ (-((1/2:ℝ)+1)) * Real.exp (-(‖x‖^2 / 4) / t)) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => heat_kernel_inverseTime_formula ht x)
  rw [he, integral_inverseTimeGamma_square_scale hr (by norm_num : (0:ℝ)<1/2),
    Real.Gamma_one_half_eq]
  have h4 : (4:ℝ) ^ (1/2:ℝ) = 2 := by rw [← Real.sqrt_eq_rpow]; norm_num
  have hc : (4 * Real.pi) ^ (-(3:ℝ)/2) * (2 * Real.sqrt Real.pi) =
      (4 * Real.pi)⁻¹ := by
    have hs : 2 * Real.sqrt Real.pi = Real.sqrt (4 * Real.pi) := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
      norm_num
    rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity : 0 < 4 * Real.pi)]
    norm_num [Real.rpow_neg_one]
  rw [h4]
  have hexp : -(2:ℝ) * (1/2) = -1 := by norm_num
  rw [hexp, Real.rpow_neg_one]
  calc
    _ = ((4 * Real.pi) ^ (-(3:ℝ)/2) * (2 * Real.sqrt Real.pi)) * ‖x‖⁻¹ := by ring
    _ = _ := by rw [hc]; simp [div_eq_mul_inv, mul_inv_rev, mul_comm]



def newtonPotential (x : Space) : ℝ := 1 / (4 * Real.pi * ‖x‖)

theorem newtonPotential_nonneg (x : Space) : 0 ≤ newtonPotential x := by
  unfold newtonPotential
  positivity

theorem newtonPotential_measurable : Measurable newtonPotential := by
  unfold newtonPotential
  fun_prop

theorem newtonPotential_locallyIntegrable : LocallyIntegrable newtonPotential volume := by
  apply locallyIntegrable_of_norm_le_rpow (C := (4 * Real.pi)⁻¹) (α := 1)
    (by simp [Space]) (by norm_num [Space])
  · filter_upwards with x
    rw [Real.norm_of_nonneg (newtonPotential_nonneg x)]
    simp [newtonPotential, Real.rpow_neg_one, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  · exact newtonPotential_measurable.aestronglyMeasurable

theorem integrable_newtonPotential_mul {φ : Space → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => newtonPotential x * φ x) volume :=
  newtonPotential_locallyIntegrable.integrable_smul_right_of_hasCompactSupport hφ hc

lemma norm_sq_rpow_neg_half (x : Space) :
    (‖x‖ ^ 2) ^ (-(1 : ℝ)/2) = ‖x‖⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg x)]
  norm_num [Real.rpow_neg_one]

lemma norm_sq_rpow_neg_three_halves (x : Space) :
    (‖x‖ ^ 2) ^ (-(1 : ℝ)/2 - 1) = (‖x‖^3)⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg x)]
  norm_num

theorem fderiv_newtonPotential_apply {x : Space} (hx : x ≠ 0) (v : Space) :
    fderiv ℝ newtonPotential x v = - inner ℝ x v / (4 * Real.pi * ‖x‖^3) := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.rpow_const
    (p := -(1 : ℝ)/2) (Or.inl (pow_ne_zero 2 hn))).const_mul ((4 * Real.pi)⁻¹)
  have he : (fun y : Space => (4 * Real.pi)⁻¹ * ((‖y‖ ^ 2) ^ (-(1 : ℝ)/2))) =
      newtonPotential := by
    funext y
    rw [norm_sq_rpow_neg_half]
    simp [newtonPotential, div_eq_mul_inv, mul_comm]
  rw [he] at h
  rw [h.fderiv]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply,
    norm_sq_rpow_neg_three_halves]
  field_simp
  ring

/-- The classical derivative of the Newton potential is the exact pressure kernel. -/
theorem fderiv_newtonPotential_coordinate {x : Space} (hx : x ≠ 0) (i : Fin 3) :
    fderiv ℝ newtonPotential x (coordinateVector i) = newtonGradientKernel i x := by
  rw [fderiv_newtonPotential_apply hx]
  simp [newtonGradientKernel, coordinateVector, EuclideanSpace.inner_single_right]


/-- Joint measurability of the actual heat kernel. -/
theorem heatKernel_joint_measurable : Measurable (fun z : Space × ℝ => Heat.kernel z.2 z.1) := by
  unfold Heat.kernel Heat.Gaussian.kernel Heat.Gaussian.normalization
  fun_prop

/-- The heat potential paired with any continuous compactly supported scalar
function is absolutely integrable in space and positive time. -/
theorem heatKernel_test_prod_integrable {φ : Space → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun z : Space × ℝ => Heat.kernel z.2 z.1 * φ z.1)
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hm : AEStronglyMeasurable
      (fun z : Space × ℝ => Heat.kernel z.2 z.1 * φ z.1)
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) :=
    (heatKernel_joint_measurable.mul (hφ.measurable.comp measurable_fst)).aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [(volume : Measure Space).ae_ne 0] with x hx
    exact (heatKernel_integrable_time hx).mul_const (φ x)
  · have hi := integrable_newtonPotential_mul hφ.norm hc.norm
    apply hi.congr
    filter_upwards [(volume : Measure Space).ae_ne 0] with x hx
    have he : (∫ t in Ioi (0 : ℝ), ‖Heat.kernel t x * φ x‖) =
        newtonPotential x * ‖φ x‖ := by
      calc
        _ = ∫ t in Ioi (0 : ℝ), Heat.kernel t x * ‖φ x‖ := by
          apply integral_congr_ae
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
          rw [norm_mul, Real.norm_of_nonneg (Heat.kernel_nonneg ht x)]
        _ = newtonPotential x * ‖φ x‖ := by
          rw [integral_mul_const, integral_heatKernel_time hx]
          rfl
    exact he.symm

/-- The compact-test heat pairing is integrable in positive time. -/
theorem heatKernel_test_integrable_time {φ : Space → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    IntegrableOn (fun t => ∫ x : Space, Heat.kernel t x * φ x) (Ioi (0 : ℝ)) :=
  (heatKernel_test_prod_integrable hφ hc).integral_prod_right

/-- Fubini identifies the actual heat potential pairing with the Newton pairing. -/
theorem integral_heatKernel_test {φ : Space → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    (∫ t in Ioi (0 : ℝ), ∫ x : Space, Heat.kernel t x * φ x) =
      ∫ x : Space, newtonPotential x * φ x := by
  rw [← integral_integral_swap (heatKernel_test_prod_integrable hφ hc)]
  apply integral_congr_ae
  filter_upwards [(volume : Measure Space).ae_ne 0] with x hx
  rw [integral_mul_const, integral_heatKernel_time hx]
  rfl

/-- Exact coordinate derivative of the standard viscosity-one kernel. -/
theorem fderiv_heatKernel_coordinate_formula (t : ℝ) (x : Space) (i : Fin 3) :
    fderiv ℝ (Heat.kernel t) x (coordinateVector i) =
      (-(x i) / (2*t)) * Heat.kernel t x := by
  change fderiv ℝ (Heat.Gaussian.kernel (4*t)) x (coordinateVector i) = _
  rw [Heat.Gaussian.kernel_fderiv, Heat.Gaussian.firstKernel]
  have hi : inner ℝ x (coordinateVector i) = x i := by
    simp [coordinateVector, EuclideanSpace.inner_single_right]
  rw [hi]
  change (-2 * (4*t)⁻¹ * x i) * Heat.kernel t x = _
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem fderiv_heatKernel_inverseTime_formula {t : ℝ} (ht : 0 < t)
    (x : Space) (i : Fin 3) :
    fderiv ℝ (Heat.kernel t) x (coordinateVector i) =
      (-(x i)/2) * (4 * Real.pi) ^ (-(3:ℝ)/2) *
        (t ^ (-((3/2:ℝ)+1)) * Real.exp (-(‖x‖^2 / 4) / t)) := by
  rw [fderiv_heatKernel_coordinate_formula, heat_kernel_inverseTime_formula ht x]
  have hp : t⁻¹ * t ^ (-((1/2:ℝ)+1)) = t ^ (-((3/2:ℝ)+1)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add ht]
    norm_num
  calc
    _ = (-(x i)/2) * (4 * Real.pi) ^ (-(3:ℝ)/2) *
        ((t⁻¹ * t ^ (-((1/2:ℝ)+1))) * Real.exp (-(‖x‖^2 / 4) / t)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [hp]

theorem fderiv_heatKernel_integrable_time {x : Space} (hx : x ≠ 0) (i : Fin 3) :
    IntegrableOn (fun t : ℝ => fderiv ℝ (Heat.kernel t) x (coordinateVector i)) (Ioi 0) := by
  have ha : 0 < ‖x‖^2 / 4 := by positivity
  have h : IntegrableOn (fun t : ℝ => (-(x i)/2) * (4 * Real.pi) ^ (-(3:ℝ)/2) *
      (t ^ (-((3/2:ℝ)+1)) * Real.exp (-(‖x‖^2/4)/t))) (Ioi 0) :=
    (integrableOn_inverseTimeGamma ha (by norm_num : (0:ℝ)<3/2)).const_mul _
  exact h.congr_fun (fun t ht => (fderiv_heatKernel_inverseTime_formula ht x i).symm)
    measurableSet_Ioi

theorem integral_fderiv_heatKernel_time {x : Space} (hx : x ≠ 0) (i : Fin 3) :
    (∫ t : ℝ in Ioi 0, fderiv ℝ (Heat.kernel t) x (coordinateVector i)) =
      -(x i) / (4 * Real.pi * ‖x‖^3) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have he : (∫ t : ℝ in Ioi 0, fderiv ℝ (Heat.kernel t) x (coordinateVector i)) =
      (-(x i)/2) * (4 * Real.pi) ^ (-(3:ℝ)/2) *
        (∫ t : ℝ in Ioi 0, t ^ (-((3/2:ℝ)+1)) * Real.exp (-(‖x‖^2 / 4) / t)) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => fderiv_heatKernel_inverseTime_formula ht x i)
  rw [he, integral_inverseTimeGamma_square_scale hr (by norm_num : (0:ℝ)<3/2)]
  have hg : Real.Gamma (3/2) = Real.sqrt Real.pi / 2 := by
    have h := Real.Gamma_nat_add_one_add_half 0
    norm_num at h
    exact h
  have h4 : (4:ℝ) ^ (3/2:ℝ) = 8 := by
    rw [show (3/2:ℝ) = (1/2)*3 by norm_num, Real.rpow_mul (by norm_num : (0:ℝ)≤4),
      ← Real.sqrt_eq_rpow]
    norm_num
  have hc : (4 * Real.pi) ^ (-(3:ℝ)/2) * (2 * Real.sqrt Real.pi) =
      (4 * Real.pi)⁻¹ := by
    have hs : 2 * Real.sqrt Real.pi = Real.sqrt (4 * Real.pi) := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
      norm_num
    rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity : 0 < 4 * Real.pi)]
    norm_num [Real.rpow_neg_one]
  rw [hg, h4]
  have hexp : -(2:ℝ) * (3/2) = -3 := by norm_num
  rw [hexp, Real.rpow_neg hr.le]
  norm_num only [Real.rpow_ofNat]
  calc
    _ = -(x i) * ((4 * Real.pi) ^ (-(3:ℝ)/2) * (2 * Real.sqrt Real.pi)) * (‖x‖^3)⁻¹ := by ring
    _ = _ := by rw [hc]; simp [div_eq_mul_inv, mul_inv_rev]; ring

theorem integral_norm_fderiv_heatKernel_time {x : Space} (hx : x ≠ 0) (i : Fin 3) :
    (∫ t : ℝ in Ioi 0, ‖fderiv ℝ (Heat.kernel t) x (coordinateVector i)‖) =
      ‖-(x i) / (4 * Real.pi * ‖x‖^3)‖ := by
  by_cases hi : 0 ≤ x i
  · have hsign (t : ℝ) (ht : t ∈ Ioi (0:ℝ)) :
        fderiv ℝ (Heat.kernel t) x (coordinateVector i) ≤ 0 := by
      rw [fderiv_heatKernel_coordinate_formula]
      exact mul_nonpos_of_nonpos_of_nonneg
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hi) (mul_nonneg (by norm_num) (le_of_lt ht)))
        (Heat.kernel_nonneg ht x)
    have hk : -(x i) / (4 * Real.pi * ‖x‖^3) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hi) (by positivity)
    calc
      _ = ∫ t : ℝ in Ioi 0, - fderiv ℝ (Heat.kernel t) x (coordinateVector i) :=
        setIntegral_congr_fun measurableSet_Ioi (fun t ht => Real.norm_of_nonpos (hsign t ht))
      _ = _ := by rw [integral_neg, integral_fderiv_heatKernel_time hx i, Real.norm_of_nonpos hk]
  · have hsign (t : ℝ) (ht : t ∈ Ioi (0:ℝ)) :
        0 ≤ fderiv ℝ (Heat.kernel t) x (coordinateVector i) := by
      rw [fderiv_heatKernel_coordinate_formula]
      exact mul_nonneg (div_nonneg (by linarith) (mul_nonneg (by norm_num) (le_of_lt ht))) (Heat.kernel_nonneg ht x)
    have hk : 0 ≤ -(x i) / (4 * Real.pi * ‖x‖^3) :=
      div_nonneg (by linarith) (by positivity)
    calc
      _ = ∫ t : ℝ in Ioi 0, fderiv ℝ (Heat.kernel t) x (coordinateVector i) :=
        setIntegral_congr_fun measurableSet_Ioi (fun t ht => Real.norm_of_nonneg (hsign t ht))
      _ = _ := by rw [integral_fderiv_heatKernel_time hx i, Real.norm_of_nonneg hk]



/-- The coordinate derivative of the heat kernel is jointly measurable. -/
theorem fderiv_heatKernel_joint_measurable (i : Fin 3) :
    Measurable (fun z : Space × ℝ =>
      fderiv ℝ (Heat.kernel z.2) z.1 (coordinateVector i)) := by
  simp_rw [fderiv_heatKernel_coordinate_formula]
  have hm : Measurable (fun z : Space × ℝ => -(z.1 i) / (2 * z.2)) := by fun_prop
  exact hm.mul heatKernel_joint_measurable

/-- Absolute space-time integrability justifies transferring the first
spatial derivative through the time integral, including the singular origin. -/
theorem fderiv_heatKernel_test_prod_integrable (i : Fin 3) {φ : Space → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun z : Space × ℝ =>
      fderiv ℝ (Heat.kernel z.2) z.1 (coordinateVector i) * φ z.1)
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hm : AEStronglyMeasurable
      (fun z : Space × ℝ =>
        fderiv ℝ (Heat.kernel z.2) z.1 (coordinateVector i) * φ z.1)
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) :=
    ((fderiv_heatKernel_joint_measurable i).mul
      (hφ.measurable.comp measurable_fst)).aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [(volume : Measure Space).ae_ne 0] with x hx
    exact (fderiv_heatKernel_integrable_time hx i).mul_const (φ x)
  · have hi := (newtonGradientKernel_integrable_mul_test i hφ hc).norm
    apply hi.congr
    filter_upwards [(volume : Measure Space).ae_ne 0] with x hx
    simp only [norm_mul]
    rw [integral_mul_const, integral_norm_fderiv_heatKernel_time hx i]
    rfl

/-- Fubini identifies the actual first-derivative heat potential with the
normalized Newton gradient kernel in every continuous compact test pairing. -/
theorem integral_fderiv_heatKernel_test (i : Fin 3) {φ : Space → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    (∫ t in Ioi (0 : ℝ), ∫ x : Space,
      fderiv ℝ (Heat.kernel t) x (coordinateVector i) * φ x) =
      ∫ x : Space, newtonGradientKernel i x * φ x := by
  rw [← integral_integral_swap (fderiv_heatKernel_test_prod_integrable i hφ hc)]
  apply integral_congr_ae
  filter_upwards [(volume : Measure Space).ae_ne 0] with x hx
  rw [integral_mul_const, integral_fderiv_heatKernel_time hx i]
  rfl

/-- The literal normalized kernel is the distributional derivative of the
literal Newton potential; there is no unproved identity among the hypotheses. -/
theorem newtonGradientKernel_test (i : Fin 3) {φ : Space → ℝ}
    (hφ : IsSpatialTest φ) :
    (∫ x : Space, newtonGradientKernel i x * φ x) =
      -(∫ x : Space, newtonPotential x * spatialTestDerivative i φ x) := by
  rw [← integral_fderiv_heatKernel_test i hφ.continuous hφ.compact]
  calc
    _ = ∫ t in Ioi (0 : ℝ), -(∫ x : Space,
        Heat.kernel t x * spatialTestDerivative i φ x) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact integral_partial_mul_test (Heat.Gaussian.kernel_smooth (4*t)) hφ i
    _ = _ := by
      rw [integral_neg, integral_heatKernel_test (hφ.derivative i).continuous
        (hφ.derivative i).compact]


/-- The normalized Newton potential is a genuine fundamental solution:
its distributional negative Laplacian is the Dirac mass at the origin. -/
theorem newtonPotential_laplacian_test {φ : Space → ℝ} (hφ : IsSpatialTest φ) :
    (∫ x : Space, newtonPotential x * Heat.laplacian φ x) = -φ 0 := by
  have hΔ := scalarTest_laplacian hφ
  rw [← integral_heatKernel_test hΔ.continuous hΔ.compact]
  exact integral_heatTestPairing_laplacian_eq hφ
    (heatKernel_test_integrable_time hΔ.continuous hΔ.compact)

/-- The actual Newton gradient kernel satisfies the differentiated fundamental
solution identity on every smooth compact test. -/
theorem newtonGradientKernel_laplacian_test (i : Fin 3) {φ : Space → ℝ}
    (hφ : IsSpatialTest φ) :
    (∫ x : Space, newtonGradientKernel i x * Heat.laplacian φ x) =
      spatialTestDerivative i φ 0 := by
  rw [newtonGradientKernel_test i (scalarTest_laplacian hφ)]
  have he : spatialTestDerivative i (Heat.laplacian φ) =
      Heat.laplacian (spatialTestDerivative i φ) :=
    funext (fun x => (Heat.laplacian_spatialTestDerivative hφ i x).symm)
  rw [he, newtonPotential_laplacian_test (hφ.derivative i), neg_neg]

end UnforcedLeray.PressureAnalysis
