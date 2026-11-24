import UnforcedLeray.Analysis.Sturm.QuadraticForm
import UnforcedLeray.GaussianLogTrial

/-!
# A negative variational bottom for the actual Gaussian Sturm form

The admissible pairs below satisfy the usual weak derivative identity on ℝ,
with both components in L². The Gaussian trial supplies an actual member of
this domain. Its Rayleigh value makes the infimum strictly negative for n=2.
No attainment of the infimum, eigenfunction, or spectral theorem is assumed.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace UnforcedLeray.Sturm
open GaussianLogTrial

/-- A scalar weak H¹ derivative pair on the whole real line. -/
def IsH1Pair (f g : ℝ → ℝ) : Prop :=
  MemLp f 2 volume ∧ MemLp g 2 volume ∧
    ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ t : ℝ, f t * deriv ψ t) = - ∫ t : ℝ, g t * ψ t

theorem logTrial_isH1Pair : IsH1Pair logTrial (deriv logTrial) :=
  logTrial_h1_admissible

theorem quadraticForm_logTrial :
    quadraticForm 2 logTrial (deriv logTrial) =
      48 - 32 * GaussianTrial.actualTrialIntegral := by
  simpa only [quadraticForm, logEnergyIntegrand, show (2 : ℝ) ^ 2 = 4 by norm_num]
    using integral_log_energy

theorem quadraticForm_logTrial_neg :
    quadraticForm 2 logTrial (deriv logTrial) < 0 := by
  simpa only [quadraticForm, logEnergyIntegrand, show (2 : ℝ) ^ 2 = 4 by norm_num]
    using log_trial_strictly_negative

/-- The ordinary Rayleigh quotient for the concrete differential form. -/
def rayleighValue (n : ℝ) (f g : ℝ → ℝ) : ℝ :=
  quadraticForm n f g / (∫ t : ℝ, f t ^ 2)

/-- Rayleigh values over nonzero, genuine weak H¹ pairs. -/
def rayleighValues (n : ℝ) : Set ℝ :=
  {q | ∃ f g : ℝ → ℝ, IsH1Pair f g ∧ (0 < ∫ t : ℝ, f t ^ 2) ∧
    q = rayleighValue n f g}

/-- The actual variational infimum; no minimizing vector is built into it. -/
def variationalBottom (n : ℝ) : ℝ := sInf (rayleighValues n)

theorem rayleighValue_lower_bound {f g : ℝ → ℝ} (h : IsH1Pair f g)
    (hmass : 0 < ∫ t : ℝ, f t ^ 2) (n : ℝ) :
    n ^ 2 - 8 ≤ rayleighValue n f g := by
  apply (le_div_iff₀ hmass).mpr
  have hb := quadraticForm_lower_bound h.1 h.2.1 n
  have hg : 0 ≤ ∫ t : ℝ, g t ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  linarith

theorem bddBelow_rayleighValues (n : ℝ) : BddBelow (rayleighValues n) := by
  refine ⟨n ^ 2 - 8, ?_⟩
  rintro q ⟨f, g, h, hmass, rfl⟩
  exact rayleighValue_lower_bound h hmass n

theorem logTrial_rayleigh_mem (n : ℝ) :
    rayleighValue n logTrial (deriv logTrial) ∈ rayleighValues n := by
  refine ⟨logTrial, deriv logTrial, logTrial_isH1Pair, ?_, rfl⟩
  rw [integral_logTrial_square]
  norm_num

theorem rayleighValues_nonempty (n : ℝ) : (rayleighValues n).Nonempty :=
  ⟨_, logTrial_rayleigh_mem n⟩

theorem variationalBottom_lower_bound (n : ℝ) : n ^ 2 - 8 ≤ variationalBottom n := by
  apply le_csInf (rayleighValues_nonempty n)
  rintro q ⟨f, g, h, hmass, rfl⟩
  exact rayleighValue_lower_bound h hmass n

theorem variationalBottom_le_logTrial (n : ℝ) :
    variationalBottom n ≤ rayleighValue n logTrial (deriv logTrial) :=
  csInf_le (bddBelow_rayleighValues n) (logTrial_rayleigh_mem n)

/-- The mode-two Gaussian form has a strictly negative variational bottom. -/
theorem variationalBottom_two_neg : variationalBottom 2 < 0 := by
  apply lt_of_le_of_lt (variationalBottom_le_logTrial 2)
  unfold rayleighValue
  rw [integral_logTrial_square]
  exact div_neg_of_neg_of_pos quadraticForm_logTrial_neg (by norm_num)

theorem variationalBottom_two_bounds : -4 ≤ variationalBottom 2 ∧ variationalBottom 2 < 0 :=
  ⟨by have h := variationalBottom_lower_bound 2; norm_num at h ⊢; exact h,
    variationalBottom_two_neg⟩

/-- All angular modes at least three have a positive variational bottom. -/
theorem variationalBottom_pos {n : ℝ} (hn : 3 ≤ n) : 0 < variationalBottom n := by
  have hb := variationalBottom_lower_bound n
  nlinarith

end UnforcedLeray.Sturm
