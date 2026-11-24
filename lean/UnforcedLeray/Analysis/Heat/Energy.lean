import UnforcedLeray.Analysis.Heat.StrongDerivative
import UnforcedLeray.Analysis.Heat.IntegrationByParts
import UnforcedLeray.Analysis.Heat.SobolevContinuity
import UnforcedLeray.Analysis.Heat.Flow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Actual all-time heat energy equality for arbitrary L² data

The dissipation is the sum of the squared norms of the genuine weak spatial
first derivatives. Strong L² differentiation of the actual kernel and weak
integration by parts give the positive-time energy derivative. Applying the
fundamental theorem's automatic integrability result to the nonnegative
derivative of minus half the squared norm proves finite dissipation at zero.
Thus no H¹ assumption on the datum, assumed energy estimate, or unproved
endpoint integrability is used.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace UnforcedLeray.Heat

def heatDissipation (F : L2Space) (t : ℝ) : ℝ :=
  ∑ i : Fin 3, ‖(heatH2Path F t).first i‖ ^ 2

theorem heatDissipation_nonneg (F : L2Space) (t : ℝ) : 0 ≤ heatDissipation F t :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- The genuine derivative of kinetic energy at every positive time. -/
theorem heatEnergy_hasDerivAt (F : L2Space) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ‖heatOperator s F‖ ^ 2) (-2 * heatDissipation F t) t := by
  have hd := (heatOperator_hasDerivAt_laplace ht F).norm_sq
  have hi : inner ℝ (heatOperator t F) (SobolevGraph.H2.laplace (heatH2Path F t)) =
      -heatDissipation F t := by
    rw [real_inner_comm, ← heatH2Path_value F ht]
    exact SobolevGraph.H2.laplace_inner_self _
  rw [hi] at hd
  simpa only [mul_neg, neg_mul] using hd

/-- An increasing primitive whose derivative is exactly the dissipation. -/
def energyPrimitive (F : L2Space) (t : ℝ) : ℝ := -(‖heatOperator t F‖ ^ 2) / 2

theorem energyPrimitive_continuous (F : L2Space) : Continuous (energyPrimitive F) :=
  ((heatOperator_strongly_continuous F).norm.pow 2).neg.div_const 2

theorem energyPrimitive_hasDerivAt (F : L2Space) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (energyPrimitive F) (heatDissipation F t) t := by
  change HasDerivAt (fun s : ℝ => -(‖heatOperator s F‖ ^ 2) / 2)
    (heatDissipation F t) t
  exact ((heatEnergy_hasDerivAt F ht).neg.div_const (2 : ℝ)).congr_deriv (by ring)

/-- Finite dissipation is derived from the nonnegative energy derivative,
including intervals starting at zero for arbitrary L² initial data. -/
theorem heatDissipation_integrableOn_Ioc (F : L2Space) {a b : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (heatDissipation F) (Ioc a b) :=
  intervalIntegral.integrableOn_deriv_of_nonneg (energyPrimitive_continuous F).continuousOn
    (fun _ ht => energyPrimitive_hasDerivAt F (ha.trans_lt ht.1))
    (fun t _ => heatDissipation_nonneg F t)

theorem heatDissipation_integrableOn (F : L2Space) {a b : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (heatDissipation F) (Ioo a b) :=
  (heatDissipation_integrableOn_Ioc F ha).mono_set Ioo_subset_Ioc_self

/-- Exact energy equality for every pair of nonnegative ordered times, including zero. -/
theorem heat_energy_equality (F : L2Space) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖heatOperator b F‖ ^ 2 + 2 * (∫ t in Ioo a b, heatDissipation F t) =
      ‖heatOperator a F‖ ^ 2 := by
  have hint : IntervalIntegrable (heatDissipation F) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      (heatDissipation_integrableOn_Ioc F ha)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (energyPrimitive_continuous F).continuousOn
    (fun t ht => energyPrimitive_hasDerivAt F (ha.trans_lt ht.1)) hint
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo] at hFTC
  unfold energyPrimitive at hFTC
  linarith

/-- The exact total dissipation identity from the original L² datum. -/
theorem heat_energy_equality_zero (F : L2Space) {T : ℝ} (hT : 0 ≤ T) :
    ‖heatOperator T F‖ ^ 2 + 2 * (∫ t in Ioo (0 : ℝ) T, heatDissipation F t) = ‖F‖ ^ 2 := by
  simpa only [heatOperator_zero, ContinuousLinearMap.id_apply] using
    heat_energy_equality F (a := 0) le_rfl hT

theorem heat_total_dissipation_le (F : L2Space) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in Ioo (0 : ℝ) T, heatDissipation F t) ≤ ‖F‖ ^ 2 / 2 := by
  have he := heat_energy_equality_zero F hT
  nlinarith [sq_nonneg ‖heatOperator T F‖]

/-- The ordinary H¹ graph norm of the heat value contains exactly energy plus dissipation. -/
theorem heatH1Path_norm_sq (F : L2Space) {t : ℝ} (ht : 0 < t) :
    ‖heatH1Path F t‖ ^ 2 = ‖heatOperator t F‖ ^ 2 + heatDissipation F t := by
  rw [heatH1Path_pos F ht, SobolevGraph.H1.norm_sq,
    heatToH1_value, ← heatOperator_pos ht]
  congr 1
  unfold heatDissipation
  apply Finset.sum_congr rfl
  intro i _
  rw [heatToH1_derivative, heatH2Path_pos F ht, heatToH2_first]

/-- Actual integrability of the full H¹ square norm, with no input H¹ hypothesis. -/
theorem heat_H1_integrable (F : L2Space) (T : ℝ) :
    IntegrableOn (fun t => ‖heatOperator t F‖ ^ 2 + heatDissipation F t) (Ioo (0 : ℝ) T) := by
  have he : IntegrableOn (fun t => ‖heatOperator t F‖ ^ 2) (Icc (0 : ℝ) T) :=
    ((heatOperator_strongly_continuous F).norm.pow 2).continuousOn.integrableOn_Icc
  exact (he.mono_set Ioo_subset_Icc_self).fun_add
    (heatDissipation_integrableOn F (a := 0) le_rfl)

/-- Genuine Bochner L²(0,T;H¹) membership of the actual heat trajectory. -/
theorem heatH1Path_memLp (F : L2Space) (T : ℝ) :
    MemLp (heatH1Path F) 2 (volume.restrict (Ioo (0 : ℝ) T)) := by
  have hm : AEStronglyMeasurable (heatH1Path F) (volume.restrict (Ioo (0 : ℝ) T)) :=
    ((heatH1Path_continuousOn F).mono
    (show Ioo (0 : ℝ) T ⊆ Ioi 0 from fun _ ht => ht.1)).aestronglyMeasurable measurableSet_Ioo
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply (heat_H1_integrable F T).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact (heatH1Path_norm_sq F ht.1).symm

/-- A genuine first weak derivative representative for the raw heat flow. -/
def flowGradient (f : SpatialField) : FirstDerivatives :=
  fun t i => ((heatH2Path (toL2 f) t).first i : SpatialField)

theorem flowGradient_memLp (f : SpatialField) (t : ℝ) (i : Fin 3) :
    MemLp (flowGradient f t i) 2 volume := Lp.memLp _

theorem dissipation_flowGradient (f : SpatialField) (t : ℝ) :
    dissipation (flowGradient f) t = heatDissipation (toL2 f) t := by
  simp only [dissipation, heatDissipation, flowGradient, l2Norm, Lp.norm_def]

/-- The chosen gradient is proved to be the actual weak derivative of the raw flow. -/
theorem flowGradient_weak {f : SpatialField} (hf : MemLp f 2 volume)
    {t : ℝ} (ht : 0 < t) (i : Fin 3) :
    HasWeakSpatialDerivative i (flow f t) (flowGradient f t i) := by
  have hv : ((heatH2Path (toL2 f) t).value : SpatialField) =ᵐ[volume] flow f t := by
    rw [heatH2Path_value (toL2 f) ht, ← toL2_flow hf t]
    exact coeFn_toL2 (flow_memLp hf t)
  exact ((heatH2Path (toL2 f) t).hasWeakFirst i).congr hv (EventuallyEq.rfl)

/-- Actual ordered second weak derivative representatives. -/
def flowSecond (f : SpatialField) : SecondDerivatives :=
  fun t i j => ((heatH2Path (toL2 f) t).second i j : SpatialField)

theorem flowSecond_memLp (f : SpatialField) (t : ℝ) (i j : Fin 3) :
    MemLp (flowSecond f t i j) 2 volume := Lp.memLp _

theorem flowSecond_weak (f : SpatialField) (t : ℝ) (i j : Fin 3) :
    HasWeakSpatialDerivative j (flowGradient f t i) (flowSecond f t i j) :=
  (heatH2Path (toL2 f) t).hasWeakSecond i j

theorem flow_finite_dissipation (f : SpatialField) (T : ℝ) :
    IntegrableOn (dissipation (flowGradient f)) (Ioo (0 : ℝ) T) := by
  have he : dissipation (flowGradient f) = heatDissipation (toL2 f) :=
    funext (dissipation_flowGradient f)
  rw [he]
  exact heatDissipation_integrableOn (toL2 f) (a := 0) (b := T) le_rfl

theorem flow_finite_H1_integral {f : SpatialField} (hf : MemLp f 2 volume) (T : ℝ) :
    IntegrableOn (fun t => l2Norm (flow f t) ^ 2 + dissipation (flowGradient f) t)
      (Ioo (0 : ℝ) T) := by
  apply (heat_H1_integrable (toL2 f) T).congr
  filter_upwards [] with t
  rw [dissipation_flowGradient, ← toL2_flow hf t, norm_toL2 (flow_memLp hf t)]

/-- The exact energy identity in the manuscript's raw-field and half-energy conventions. -/
theorem flow_energy_equality {f : SpatialField} (hf : MemLp f 2 volume)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (1 / 2 : ℝ) * l2Norm (flow f b) ^ 2 +
      (∫ t in Ioo a b, dissipation (flowGradient f) t) =
      (1 / 2 : ℝ) * l2Norm (flow f a) ^ 2 := by
  have he := heat_energy_equality (toL2 f) ha hab
  have hn (t : ℝ) : ‖heatOperator t (toL2 f)‖ = l2Norm (flow f t) := by
    rw [← toL2_flow hf t, norm_toL2 (flow_memLp hf t)]
  simp_rw [hn] at he
  simp_rw [dissipation_flowGradient]
  linarith

end UnforcedLeray.Heat
