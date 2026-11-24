import UnforcedLeray.Lib.ComplexODE.NeutralSolution
import UnforcedLeray.Lib.ComplexODE.Sturm
import UnforcedLeray.Analysis.Sturm.NeutralProfile
import NonUniqueEuler.P.Infra.ODE.Param

/-!
# The real neutral solution (INF18 O1, part 1)

Wave 1 block 1H part 3, scoping note

(blueprint unit B0034, `paper/main.tex` lines 1001--1011).

The completed neutral equation `F'' = (β² - W) F` (eq. st18-t00032 in logarithmic radius) has a
real coefficient, so the normalized solution `neutralNormalizedF β a` is real
(`neutralNormalized_conj`). This module names its real part `neutralU β a` and its derivative
`neutralU' β a`, transfers the equation, the initial data, nondegeneracy of zeros and joint
continuity in `(t, β)`, and records the sign of the explicit neutral profile
`h_*(t) = e^t (Ω(t) - a_*)` (`paper/main.tex` lines 925--931, eq. st18-t00028).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Rayleigh.Evans

open NonUniqueEuler.LinODE Sturm GaussianPotential

/-- The real part of the normalized neutral solution, `F(a) = 0`, `F'(a) = 1`. -/
def neutralU (β a t : ℝ) : ℝ := (neutralNormalizedF β a t).re

/-- The real part of the derivative of the normalized neutral solution. -/
def neutralU' (β a t : ℝ) : ℝ := (neutralNormalizedDerivative β a t).re

theorem hasDerivAt_re_of_hasDerivAt {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => (f s).re) f'.re t := by
  have h1 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h
  rw [Complex.reCLM_apply] at h1
  exact h1

theorem neutralNormalizedF_eq_ofReal (β a t : ℝ) :
    neutralNormalizedF β a t = (neutralU β a t : ℂ) :=
  neutralNormalizedF_eq_ofReal_re β a t

theorem neutralNormalizedDerivative_eq_ofReal (β a t : ℝ) :
    neutralNormalizedDerivative β a t = (neutralU' β a t : ℂ) :=
  (Complex.conj_eq_iff_re.mp ((neutralNormalized_conj β a).2 t)).symm

theorem hasDerivAt_neutralU (β a t : ℝ) :
    HasDerivAt (neutralU β a) (neutralU' β a t) t :=
  hasDerivAt_re_of_hasDerivAt (hasDerivAt_neutralNormalizedF β a t)

theorem hasDerivAt_neutralU' (β a t : ℝ) :
    HasDerivAt (neutralU' β a) ((β ^ 2 - Wlog t) * neutralU β a t) t := by
  have h := hasDerivAt_re_of_hasDerivAt (hasDerivAt_neutralNormalizedDerivative β a t)
  have hV : neutralPotential β t = ((β ^ 2 - Wlog t : ℝ) : ℂ) := by
    simp [neutralPotential]
  rw [hV, Complex.re_ofReal_mul] at h
  exact h

@[simp] theorem neutralU_initial (β a : ℝ) : neutralU β a a = 0 := by
  simp [neutralU]

@[simp] theorem neutralU'_initial (β a : ℝ) : neutralU' β a a = 1 := by
  simp [neutralU']

theorem continuous_neutralU (β a : ℝ) : Continuous (neutralU β a) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_neutralU β a t).continuousAt

theorem continuous_neutralU' (β a : ℝ) : Continuous (neutralU' β a) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_neutralU' β a t).continuousAt

theorem neutralU_contDiff (β a : ℝ) : ContDiff ℝ ∞ (neutralU β a) :=
  Complex.reCLM.contDiff.comp (neutralNormalizedF_smooth β a)

theorem deriv_neutralU (β a : ℝ) : deriv (neutralU β a) = neutralU' β a :=
  funext fun t => (hasDerivAt_neutralU β a t).deriv

theorem deriv_deriv_neutralU (β a t : ℝ) :
    deriv (deriv (neutralU β a)) t = (β ^ 2 - Wlog t) * neutralU β a t := by
  rw [deriv_neutralU]
  exact (hasDerivAt_neutralU' β a t).deriv

/-- A zero of the neutral solution is simple. -/
theorem neutralU'_ne_zero_of_eq_zero {β a t : ℝ} (ht : neutralU β a t = 0) :
    neutralU' β a t ≠ 0 := by
  intro h'
  apply neutralNormalizedDerivative_ne_zero_of_value_zero β a t
  · rw [neutralNormalizedF_eq_ofReal, ht, Complex.ofReal_zero]
  · rw [neutralNormalizedDerivative_eq_ofReal, h', Complex.ofReal_zero]

theorem neutralEvansFunction_eq_zero_iff (β a b : ℝ) :
    neutralEvansFunction β a b = 0 ↔ neutralU β a b = 0 := by
  rw [neutralEvansFunction, neutralNormalizedF_eq_ofReal, Complex.ofReal_eq_zero]

theorem neutralNormalizedF_ne_zero_iff (β a t : ℝ) :
    neutralNormalizedF β a t ≠ 0 ↔ neutralU β a t ≠ 0 := by
  rw [neutralNormalizedF_eq_ofReal, Ne, Complex.ofReal_eq_zero]

/-- The normalized neutral pair is jointly continuous in `(t, β)`
(vendored `NonUniqueEuler.LinODE.continuousOn_sol`). -/
theorem continuous_neutralNormalizedPair_joint (a : ℝ) :
    Continuous (fun q : ℝ × ℝ => neutralNormalizedPair q.2 a q.1) := by
  have hV : ContinuousOn (Function.uncurry (fun (t β : ℝ) => neutralPotential β t))
      (univ ×ˢ univ) := by
    apply Continuous.continuousOn
    unfold neutralPotential
    exact ((Complex.continuous_ofReal.comp continuous_snd).pow 2).sub
      (Complex.continuous_ofReal.comp (continuous_Wlog.comp continuous_fst))
  have h := continuousOn_sol (V := fun (t β : ℝ) => neutralPotential β t) hV a
    (y₀ := fun _ => ((0 : ℂ), (1 : ℂ))) continuousOn_const
  rw [univ_prod_univ] at h
  exact continuousOn_univ.mp h

theorem continuous_neutralU_joint (a : ℝ) :
    Continuous (fun q : ℝ × ℝ => neutralU q.2 a q.1) :=
  Complex.continuous_re.comp
    (continuous_fst.comp (continuous_neutralNormalizedPair_joint a))

theorem continuous_neutralU'_joint (a : ℝ) :
    Continuous (fun q : ℝ × ℝ => neutralU' q.2 a q.1) :=
  Complex.continuous_re.comp
    (continuous_snd.comp (continuous_neutralNormalizedPair_joint a))

/-! ### Sign of the explicit neutral profile `h_*` -/

theorem neutralProfile_pos_of_lt {t : ℝ} (ht : t < neutralCriticalTime) :
    0 < neutralProfile t := by
  unfold neutralProfile
  apply mul_pos (Real.exp_pos t)
  rw [sub_pos]
  unfold neutralOmega
  apply Real.exp_lt_exp.mpr
  have h8 : Real.exp (2 * t) < 8 := by
    have h2 : 2 * t < Real.log 8 := by unfold neutralCriticalTime at ht; linarith
    calc Real.exp (2 * t) < Real.exp (Real.log 8) := Real.exp_lt_exp.mpr h2
      _ = 8 := Real.exp_log (by norm_num)
  unfold neutralRadius
  linarith

theorem neutralProfile_neg_of_gt {t : ℝ} (ht : neutralCriticalTime < t) :
    neutralProfile t < 0 := by
  unfold neutralProfile
  apply mul_neg_of_pos_of_neg (Real.exp_pos t)
  rw [sub_neg]
  unfold neutralOmega
  apply Real.exp_lt_exp.mpr
  have h8 : 8 < Real.exp (2 * t) := by
    have h2 : Real.log 8 < 2 * t := by unfold neutralCriticalTime at ht; linarith
    calc (8 : ℝ) = Real.exp (Real.log 8) := (Real.exp_log (by norm_num)).symm
      _ < Real.exp (2 * t) := Real.exp_lt_exp.mpr h2
  unfold neutralRadius
  linarith

theorem hasDerivAt_neutralProfile' (t : ℝ) :
    HasDerivAt (deriv neutralProfile) ((1 - Wlog t) * neutralProfile t) t := by
  have h := hasDerivAt_deriv_neutralProfile t
  rw [← deriv_deriv_neutralProfile, neutralProfile_ode] at h
  exact h

theorem neutralCriticalTime_pos : 0 < neutralCriticalTime := by
  unfold neutralCriticalTime
  have : 0 < Real.log 8 := Real.log_pos (by norm_num)
  linarith

theorem neutralCriticalTime_lt_two : neutralCriticalTime < 2 := by
  unfold neutralCriticalTime
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have h2 : Real.log 2 < 1 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
    linarith
  rw [h8]
  linarith

end UnforcedLeray.Rayleigh.Evans
