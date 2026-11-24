import UnforcedLeray.Analysis.Heat.GaussianScaling
import UnforcedLeray.Analysis.Heat.ConvolutionOrbit
import UnforcedLeray.Analysis.Heat.Semigroup

/-!
# The actual strongly continuous L² heat semigroup on R³

At positive times this is the literal Gaussian convolution operator. At zero
it is the identity, as justified by the strong initial limit. For convenience
it is extended constantly by the identity to negative times; the semigroup
law is asserted only for nonnegative times.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace UnforcedLeray.Heat

open Classical in
/-- The viscosity-one heat semigroup on actual whole-space vector L². -/
def heatOperator (t : ℝ) : L2Space →L[ℝ] L2Space :=
  if ht : 0 < t then convolutionOperator (kernel t) (kernel_integrable ht)
  else ContinuousLinearMap.id ℝ L2Space

theorem heatOperator_pos {t : ℝ} (ht : 0 < t) :
    heatOperator t = convolutionOperator (kernel t) (kernel_integrable ht) := by
  simp only [heatOperator, dite_eq_left ht]

theorem heatOperator_nonpos {t : ℝ} (ht : t ≤ 0) :
    heatOperator t = ContinuousLinearMap.id ℝ L2Space := by
  simp only [heatOperator, dite_eq_right (not_lt.mpr ht)]

@[simp] theorem heatOperator_zero : heatOperator 0 = ContinuousLinearMap.id ℝ L2Space :=
  heatOperator_nonpos le_rfl

/-- Identification with the normalized Gaussian translation integral uses exact
Fubini pairings and the actual three-dimensional Haar change of variables. -/
theorem heatOperator_eq_orbitAverage (t : ℝ) (u : L2Space) :
    heatOperator t u = orbitAverage (Real.sqrt (4*t)) u := by
  by_cases ht : 0 < t
  · rw [heatOperator_pos ht,
      convolutionOperator_eq_integral_translationOrbit (kernel t) (kernel_integrable ht) u,
      orbitAverage_eq_heatKernel ht u]
  · have ht0 : t ≤ 0 := le_of_not_gt ht
    rw [heatOperator_nonpos ht0]
    have hs : Real.sqrt (4*t) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
    simp only [hs, orbitAverage_zero, ContinuousLinearMap.id_apply]

theorem heatOperator_eq_orbitAverageCLM (t : ℝ) :
    heatOperator t = orbitAverageCLM (Real.sqrt (4*t)) := by
  apply ContinuousLinearMap.ext
  intro u
  exact heatOperator_eq_orbitAverage t u

/-- Uniform contraction, including the identity at zero. -/
theorem heatOperator_norm_le (t : ℝ) : ‖heatOperator t‖ ≤ 1 := by
  rw [heatOperator_eq_orbitAverageCLM]
  exact orbitAverageCLM_norm_le _

theorem heatOperator_apply_norm_le (t : ℝ) (u : L2Space) :
    ‖heatOperator t u‖ ≤ ‖u‖ := by
  rw [heatOperator_eq_orbitAverage]
  exact orbitAverage_norm_le _ _

/-- Strong continuity, proved in L² rather than pointwise or weak convergence. -/
theorem heatOperator_strongly_continuous (u : L2Space) :
    Continuous (fun t : ℝ => heatOperator t u) := by
  simp_rw [heatOperator_eq_orbitAverage]
  exact (orbitAverage_continuous u).comp (by fun_prop)

/-- The actual strong initial trace in whole-space L². -/
theorem heatOperator_tendsto_zero (u : L2Space) :
    Tendsto (fun t : ℝ => heatOperator t u) (𝓝[Set.Ici 0] 0) (𝓝 u) := by
  have h := (heatOperator_strongly_continuous u).continuousAt.tendsto (x := (0 : ℝ))
  simpa only [heatOperator_zero, ContinuousLinearMap.id_apply] using
    h.mono_left nhdsWithin_le_nhds

/-- The convolution semigroup law, now including all zero-time cases. -/
theorem heatOperator_add_time {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    heatOperator (s+t) = (heatOperator s).comp (heatOperator t) := by
  rcases eq_or_lt_of_le hs with hs0 | hspos
  · subst s
    simp only [zero_add, heatOperator_zero, ContinuousLinearMap.id_comp]
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · subst t
    simp only [add_zero, heatOperator_zero, ContinuousLinearMap.comp_id]
  rw [heatOperator_pos (add_pos hspos htpos), heatOperator_pos hspos, heatOperator_pos htpos]
  exact convolutionOperator_heat_add_time hspos htpos

/-- At every positive time the quotient is represented by the literal heat integral. -/
theorem heatOperator_rep {t : ℝ} (ht : 0 < t) (u : L2Space) :
    (heatOperator t u : SpatialField) =ᵐ[volume] average t (u : SpatialField) := by
  rw [heatOperator_pos ht]
  exact convolutionToL2_rep (kernel t) (kernel_integrable ht) u

end UnforcedLeray.Heat
