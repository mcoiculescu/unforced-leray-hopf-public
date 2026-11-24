import UnforcedLeray.Analysis.Rayleigh.Decay
import UnforcedLeray.Analysis.Rayleigh.IntervalHolder

/-!
# Decay from actual classical H¹ and H² data

The fundamental theorem of calculus and the genuine derivative square integral
supply a global square-root modulus. The finite-mass decay theorem then applies
to the function and, for classical H² data, also to its first derivative.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace UnforcedLeray.Rayleigh

/-- The actual full-line derivative mass controls the global modulus. -/
theorem sqrt_bound_of_contDiff_one_memLp_deriv {f : ℝ → ℂ}
    (hf : ContDiff ℝ 1 f) (hdf : MemLp (deriv f) 2 volume) :
    ∀ s t, ‖f s - f t‖ ≤
      Real.sqrt (∫ x, ‖deriv f x‖ ^ 2) * Real.sqrt |s - t| := by
  have hi : Integrable (fun x => ‖deriv f x‖ ^ 2) :=
    hdf.integrable_norm_pow (by norm_num)
  have aux (a b : ℝ) (hab : a ≤ b) :
      ‖f b - f a‖ ≤ Real.sqrt (∫ x, ‖deriv f x‖ ^ 2) * Real.sqrt |b - a| := by
    have hm : (∫ x in Ioc a b, ‖deriv f x‖ ^ 2) ≤ ∫ x, ‖deriv f x‖ ^ 2 :=
      setIntegral_le_integral hi (Eventually.of_forall fun _ => sq_nonneg _)
    have hs := Real.sqrt_le_sqrt hm
    calc
      ‖f b - f a‖ ≤ Real.sqrt (b - a) *
          Real.sqrt (∫ x in Ioc a b, ‖deriv f x‖ ^ 2) :=
        norm_sub_le_sqrt_derivative_mass hf hab
      _ ≤ Real.sqrt (b - a) * Real.sqrt (∫ x, ‖deriv f x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
      _ = _ := by rw [abs_of_nonneg (sub_nonneg.mpr hab), mul_comm]
  intro s t
  rcases le_total s t with hst | hts
  · simpa only [norm_sub_rev, abs_sub_comm] using aux s t hst
  · exact aux t s hts

/-- A classical C¹ representative with genuine H¹ integrability vanishes at both ends. -/
theorem tendsto_zero_of_contDiff_one_memLp {f : ℝ → ℂ}
    (hreg : ContDiff ℝ 1 f) (hf : MemLp f 2 volume)
    (hdf : MemLp (deriv f) 2 volume) :
    Tendsto f atTop (𝓝 0) ∧ Tendsto f atBot (𝓝 0) :=
  tendsto_zero_of_sqrt_bound_memLp _ (sqrt_bound_of_contDiff_one_memLp_deriv hreg hdf) hf

/-- The first derivative of classical H² data has genuine decay at both ends. -/
theorem tendsto_deriv_zero_of_contDiff_two_memLp {f : ℝ → ℂ}
    (hreg : ContDiff ℝ 2 f) (hdf : MemLp (deriv f) 2 volume)
    (hddf : MemLp (deriv (deriv f)) 2 volume) :
    Tendsto (deriv f) atTop (𝓝 0) ∧ Tendsto (deriv f) atBot (𝓝 0) :=
  tendsto_zero_of_contDiff_one_memLp (contDiff_deriv_of_two hreg) hdf hddf

end UnforcedLeray.Rayleigh
