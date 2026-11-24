import UnforcedLeray.Analysis.Sturm.NeutralProfile
import UnforcedLeray.Analysis.Sturm.NeutralFactorizationBasic

/-!
# Positivity away from the Gaussian neutral zero

The exact h* calculation is inserted into the proved ground-state identity.
The Gaussian potential and all trial integrals are concrete; no factorization
or positivity premise is introduced.
-/

noncomputable section
open MeasureTheory Set
namespace UnforcedLeray.Sturm
open GaussianPotential

/-- The ground-state square has a finite integral for every compact C¹ trial
whose support avoids the unique Gaussian neutral zero. -/
theorem neutral_groundState_factorization {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (ha : neutralCriticalTime ∉ tsupport f) :
    Integrable (groundStateSquare neutralProfile f) ∧
      quadraticForm 1 f (deriv f) = ∫ t, groundStateSquare neutralProfile f t := by
  have hf2 : MemLp f 2 volume := hf.continuous.memLp_of_hasCompactSupport hfc
  have hdf2 : MemLp (deriv f) 2 volume :=
    hf.continuous_deriv_one.memLp_of_hasCompactSupport hfc.deriv
  have hzero : ∀ t ∈ tsupport f, neutralProfile t ≠ 0 := by
    intro t ht
    apply neutralProfile_ne_zero
    intro he
    exact ha (he ▸ ht)
  have hform : Integrable (fun t => deriv f t ^ 2 + (1 - Wlog t) * f t ^ 2) := by
    simpa only [one_pow] using integrable_form hf2 hdf2 1
  simpa only [quadraticForm, one_pow] using
    groundState_factorization neutralProfile_smooth hf hfc hzero
      (fun t _ => neutralProfile_ode t) hform

/-- Actual Gaussian form positivity away from the critical zero. -/
theorem neutral_form_nonneg_away {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (ha : neutralCriticalTime ∉ tsupport f) :
    0 ≤ quadraticForm 1 f (deriv f) := by
  rw [(neutral_groundState_factorization hf hfc ha).2]
  exact integral_nonneg (fun _ => sq_nonneg _)

/-- A uniform bound used in the explicit cutoff limits. -/
theorem neutral_form_potential_bound (t : ℝ) : |1 - Wlog t| ≤ 9 := by
  have hW := norm_Wlog_le_eight t
  rw [Real.norm_eq_abs] at hW
  calc
    |1 - Wlog t| ≤ |(1 : ℝ)| + |Wlog t| := abs_sub _ _
    _ ≤ 9 := by norm_num at *; linarith

end UnforcedLeray.Sturm
