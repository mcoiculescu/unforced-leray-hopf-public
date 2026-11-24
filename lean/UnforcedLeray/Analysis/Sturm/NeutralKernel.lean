import UnforcedLeray.Analysis.Sturm.NeutralKernelAlgebra
import UnforcedLeray.Analysis.Sturm.NeutralEigenIdentity
import UnforcedLeray.Analysis.Sturm.NeutralCoercivity
import UnforcedLeray.Analysis.Sturm.VariationalBottom
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# No neutral mode at angular index two

The explicit negative Gaussian trial and the explicit neutral-profile
factorization rule out a nonzero classical H¹ solution of the actual neutral
ODE. Neither existence of a negative eigenfunction nor a spectral-index
statement is assumed. The second-derivative L² condition is derived from the
ODE and the bounded Gaussian potential.

This theorem is stated on actual C² representatives. Identifying an arbitrary
weak H² kernel element with such a representative is a separate regularity
step, not an unspoken hypothesis discharge.
-/

noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace UnforcedLeray.Sturm
open GaussianPotential GaussianLogTrial

private theorem logTrial_contDiff_one : ContDiff ℝ 1 logTrial :=
  contDiff_one_iff_deriv.mpr
    ⟨fun t => (hasDerivAt_logTrial t).differentiableAt, continuous_deriv_logTrial⟩

/-- An actual C² H¹ solution of `−g''+(4−Wlog)g=0` vanishes identically. -/
theorem gaussian_neutral_mode_two_eq_zero {g : ℝ → ℝ}
    (hgc : ContDiff ℝ 2 g) (hg : MemLp g 2 volume)
    (hdg : MemLp (deriv g) 2 volume)
    (heq : ∀ t, -deriv (deriv g) t + (4 - Wlog t) * g t = 0) : g = 0 := by
  have heig : ∀ t, -deriv (deriv g) t + ((2 : ℝ) ^ 2 - Wlog t) * g t =
      (0 : ℝ) * g t := by
    intro t
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num, zero_mul] using heq t
  have hddg : MemLp (deriv (deriv g)) 2 volume := sturm_eigen_second_memLp hg heig
  have hgzero : quadraticForm 2 g (deriv g) = 0 := by
    simpa using sturm_eigen_energy hgc hg hdg hddg heig
  have hcross : (∫ t, deriv logTrial t * deriv g t +
      ((2 : ℝ) ^ 2 - Wlog t) * (logTrial t * g t)) = 0 := by
    change sturmBilinearForm 2 logTrial (deriv logTrial) g (deriv g) = 0
    rw [sturmBilinear_symm]
    simpa using sturm_eigen_bilinear hgc logTrial_contDiff_one hg hdg hddg
      logTrial_memLp_two deriv_logTrial_memLp_two heig
  have hcoerc : ∀ F : ℝ → ℝ, ContDiff ℝ 1 F → MemLp F 2 volume →
      MemLp (deriv F) 2 volume → F neutralCriticalTime = 0 →
      3 * (∫ t, F t ^ 2) ≤ quadraticForm 2 F (deriv F) := by
    intro F hFc hF hFd hFa
    simpa only [show (2 : ℝ) ^ 2 - 1 = 3 by norm_num] using
      quadraticForm_trace_zero_coercive hFc hF hFd hFa (2 : ℝ)
  have hz : g =ᵐ[volume] 0 := neutral_zero_of_trace_coercivity
    (by norm_num : (0 : ℝ) < 3) hcoerc
    logTrial_contDiff_one (hgc.of_le (by norm_num))
    logTrial_memLp_two deriv_logTrial_memLp_two hg hdg
    quadraticForm_logTrial_neg hgzero hcross
  exact MeasureTheory.Measure.eq_of_ae_eq hz hgc.continuous continuous_zero

end UnforcedLeray.Sturm
