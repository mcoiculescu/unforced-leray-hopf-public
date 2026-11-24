import UnforcedLeray.Analysis.Sturm.OneDRegularity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Classical second derivatives for continuous L² Green data

The signed-kernel convolution is differentiated through its actual half-line
integral. The moving endpoint is handled by the fundamental theorem of
calculus; the infinite tail is integrable by the L² exponential-kernel bound.
This gives a classical C² representative and the actual differential equation.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace UnforcedLeray.Sturm
open NonUniqueEuler.Sob.EnergyAux

/-- A continuous function with integrable left tails has the expected endpoint derivative. -/
theorem hasDerivAt_integral_Iic_of_continuous {g : ℝ → ℂ} (hg : Continuous g)
    (hi : ∀ x : ℝ, IntegrableOn g (Iic x)) (x : ℝ) :
    HasDerivAt (fun z => ∫ y in Iic z, g y) (g x) x := by
  have heq : (fun z => ∫ y in Iic z, g y) =
      fun z => (∫ y in Iic (0 : ℝ), g y) + ∫ y in (0 : ℝ)..z, g y := by
    funext z
    have h := intervalIntegral.integral_Iic_sub_Iic (hi 0) (hi z)
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  rw [heq]
  exact (hg.integral_hasStrictDerivAt 0 x).hasDerivAt.const_add _

/-- The exponentially weighted input has an integrable tail at every finite endpoint. -/
theorem integrableOn_exp_mul_left_of_memLp {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (x : ℝ) :
    IntegrableOn (fun y => (Real.exp (L * y) : ℂ) * f y) (Iic x) := by
  have h : IntegrableOn (fun y => (Real.exp (L * x) : ℂ) *
      ((k0 L (x - y) : ℂ) * f y)) (Iic x) :=
    ((integrable_k0_mul_of_memLp hL hf x).integrableOn
      (s := Iic x)).const_mul (Real.exp (L * x) : ℂ)
  refine h.congr_fun (fun y hy => ?_) measurableSet_Iic
  have he : Real.exp (L * x) * k0 L (x - y) = Real.exp (L * y) := by
    unfold k0
    rw [abs_of_nonneg (sub_nonneg.mpr hy), ← Real.exp_add]
    congr 1
    ring
  dsimp only
  rw [← mul_assoc, ← Complex.ofReal_mul, he]

/-- The contribution of the left half-line to the actual Green convolution. -/
def leftGreen (L : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Real.exp (-L * x) : ℂ) * ∫ y in Iic x, (Real.exp (L * y) : ℂ) * f y

theorem leftGreen_eq_kernel_integral (L : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    leftGreen L f x = ∫ y in Iic x, (k0 L (x - y) : ℂ) * f y := by
  unfold leftGreen
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Iic
  intro y hy
  have he : Real.exp (-L * x) * Real.exp (L * y) = k0 L (x - y) := by
    unfold k0
    rw [abs_of_nonneg (sub_nonneg.mpr hy), ← Real.exp_add]
    congr 1
    ring
  dsimp only
  rw [← mul_assoc, ← Complex.ofReal_mul, he]

/-- Splitting the signed kernel at its jump gives an actual half-line formula. -/
theorem psi1_eq_twice_leftGreen_sub_psi0 {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (x : ℝ) :
    psi1 L f x = 2 * leftGreen L f x - psi0 L f x := by
  have h0 := integral_add_compl (s := Iic x) measurableSet_Iic (integrable_k0_mul_of_memLp hL hf x)
  have h1 := integral_add_compl (s := Iic x) measurableSet_Iic (integrable_k1_mul_of_memLp hL hf x)
  simp only [compl_Iic] at h0 h1
  have hleft : (∫ y in Iic x, (k1 L (x - y) : ℂ) * f y) =
      ∫ y in Iic x, (k0 L (x - y) : ℂ) * f y := by
    apply setIntegral_congr_ae measurableSet_Iic
    filter_upwards [ae_ne_pt x] with y hy
    intro hymem
    have hxy : 0 < x - y := by
      have hlt : y < x := lt_of_le_of_ne hymem hy
      exact sub_pos.mpr hlt
    rw [k1_of_pos hxy, k0_of_pos hxy]
  have hright : (∫ y in Ioi x, (k1 L (x - y) : ℂ) * f y) =
      -(∫ y in Ioi x, (k0 L (x - y) : ℂ) * f y) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    have hxy : x - y ≤ 0 := sub_nonpos.mpr hy.le
    dsimp only
    rw [k1_of_nonpos hxy, k0_of_nonpos hxy]
    push_cast
    ring
  unfold psi1 psi0
  rw [← h1, ← h0, hleft, hright, leftGreen_eq_kernel_integral]
  ring

/-- The moving endpoint contributes exactly the datum to the left Green component. -/
theorem hasDerivAt_leftGreen {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hc : Continuous f) (x : ℝ) :
    HasDerivAt (leftGreen L f) (f x - (L : ℂ) * leftGreen L f x) x := by
  have hweight : Continuous (fun y => (Real.exp (L * y) : ℂ) * f y) := by fun_prop
  have hA := hasDerivAt_integral_Iic_of_continuous hweight
    (integrableOn_exp_mul_left_of_memLp hL hf) x
  have he := (((hasDerivAt_id x).const_mul (-L)).exp).ofReal_comp
  have hm := he.mul hA
  refine hm.congr_deriv ?_
  have hex : (Real.exp (-L * x) : ℂ) * (Real.exp (L * x) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    have hh : -L * x + L * x = 0 := by ring
    rw [hh, Real.exp_zero, Complex.ofReal_one]
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, id_eq, mul_one]
  calc
    (Real.exp (-L * x) : ℂ) * -(L : ℂ) *
          (∫ y in Iic x, (Real.exp (L * y) : ℂ) * f y) +
        (Real.exp (-L * x) : ℂ) * ((Real.exp (L * x) : ℂ) * f x) =
      ((Real.exp (-L * x) : ℂ) * (Real.exp (L * x) : ℂ)) * f x -
        (L : ℂ) * leftGreen L f x := by unfold leftGreen; ring
    _ = f x - (L : ℂ) * leftGreen L f x := by rw [hex, one_mul]

/-- The actual signed-kernel convolution has the derivative including its jump term. -/
theorem hasDerivAt_psi1_of_memLp_continuous {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hc : Continuous f) (x : ℝ) :
    HasDerivAt (psi1 L f) (2 * f x - (L : ℂ) * psi0 L f x) x := by
  have heq : psi1 L f = fun z => 2 * leftGreen L f z - psi0 L f z :=
    funext (psi1_eq_twice_leftGreen_sub_psi0 hL hf)
  rw [heq]
  have h := ((hasDerivAt_leftGreen hL hf hc x).const_mul (2 : ℂ)).sub
    (hasDerivAt_psi0_of_memLp hL hf x)
  refine h.congr_deriv ?_
  rw [psi1_eq_twice_leftGreen_sub_psi0 hL hf x]
  ring

/-- Classical second derivative of the actual resolvent for continuous L² data. -/
theorem hasDerivAt_freeResolventDeriv_of_memLp_continuous {L : ℝ} (hL : 0 < L)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) (hc : Continuous f) (x : ℝ) :
    HasDerivAt (freeResolventDeriv L f)
      ((L : ℂ) ^ 2 * freeResolvent L f x - f x) x := by
  have h := (hasDerivAt_psi1_of_memLp_continuous hL hf hc x).const_mul (-(1 / 2 : ℂ))
  refine h.congr_deriv ?_
  unfold freeResolvent
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  push_cast
  field_simp
  ring

theorem deriv_freeResolventDeriv_of_memLp_continuous {L : ℝ} (hL : 0 < L)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) (hc : Continuous f) :
    deriv (freeResolventDeriv L f) = fun x => (L : ℂ) ^ 2 * freeResolvent L f x - f x := by
  funext x
  exact (hasDerivAt_freeResolventDeriv_of_memLp_continuous hL hf hc x).deriv

/-- The actual free Green representative is C² whenever the L² source is continuous. -/
theorem contDiff_two_freeResolvent_of_memLp_continuous {L : ℝ} (hL : 0 < L)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) (hc : Continuous f) :
    ContDiff ℝ 2 (freeResolvent L f) := by
  have hder : ContDiff ℝ 1 (freeResolventDeriv L f) := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun x => (hasDerivAt_freeResolventDeriv_of_memLp_continuous hL hf hc x).differentiableAt, ?_⟩
    rw [deriv_freeResolventDeriv_of_memLp_continuous hL hf hc]
    exact (((continuous_psi0_of_memLp hL hf).const_mul _).const_mul _).sub hc
  rw [show (2 : ℕ∞ω) = 1 + 1 by rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x => (hasDerivAt_freeResolvent_of_memLp hL hf x).differentiableAt, ?_, ?_⟩
  · intro h
    norm_num at h
  · rw [deriv_freeResolvent_of_memLp hL hf]
    exact hder

end UnforcedLeray.Sturm
