import UnforcedLeray.Analysis.Rayleigh.EnergyEstimates
import UnforcedLeray.Analysis.Rayleigh.PotentialTail

/-!
# Uniform local mass for normalized unstable annular modes

Decay of the actual potential and the derived energy inequality force a fixed
positive amount of every normalized mode into one fixed compact interval.
This conclusion is uniform over annular endpoints and upper-half-plane speeds;
no lower bound on the imaginary part of the speed is needed.
-/
noncomputable section
open MeasureTheory Set
namespace UnforcedLeray.Rayleigh
open GaussianPotential Sturm

theorem exists_uniform_local_mass :
    ∃ R : ℝ, 0 < R ∧ ∀ (q : ℝ → ℝ) (z : ℂ) (F : ℝ → ℂ) (l r : ℝ),
      ShiftedAnnularMode q z F l r →
      (∫ t in Ioc l r, ‖F t‖ ^ 2) = 1 →
      (3 / 8 : ℝ) ≤ ∫ t in Icc (-R) R ∩ Ioc l r, ‖F t‖ ^ 2 := by
  obtain ⟨R, hR, htail⟩ := exists_potential_tail_bound (show (0 : ℝ) < 1 by norm_num)
  refine ⟨R, hR, ?_⟩
  intro q z F l r h hmass
  have hFn : IntegrableOn (fun t => ‖F t‖ ^ 2) (Ioc l r) :=
    (h.regularity.continuous.norm.pow 2).integrableOn_Ioc
  have hIn := hFn.indicator (measurableSet_Icc (a := -R) (b := R))
  have hp : ∀ t : ℝ, Wlog t * ‖F t‖ ^ 2 ≤
      ‖F t‖ ^ 2 + 8 * (Icc (-R) R).indicator (fun x => ‖F x‖ ^ 2) t := by
    intro t
    by_cases ht : t ∈ Icc (-R) R
    · rw [indicator_of_mem ht]
      have hw := mul_le_mul_of_nonneg_right (Wlog_le_eight t) (sq_nonneg ‖F t‖)
      nlinarith [sq_nonneg ‖F t‖]
    · rw [indicator_of_notMem ht, mul_zero, add_zero]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (htail t ht) (sq_nonneg ‖F t‖)
  have hi := integral_mono
    (integrableOn_Wlog_mul (l := l) (r := r) (h.regularity.continuous.norm.pow 2))
    (hFn.fun_add (hIn.const_mul 8)) hp
  rw [integral_add hFn (hIn.const_mul 8), integral_const_mul, hmass,
    integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc] at hi
  have he := (h.normalized_energy_bounds hmass).1.trans h.energy_le_potential
  simp only [Pi.pow_apply] at hi
  linarith

end UnforcedLeray.Rayleigh
