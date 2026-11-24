import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegrableOn
import UnforcedLeray.Statement

/-!
# `PartIII-b:C/rep/5/1/2/4/1/3/1`: the spatial `L²` norm of the order-four gap kernel

Source `the November 2 reference manuscript` 5588-5591.  On `ℝ³` the squared
kernel integrates to `∫_{|x| ≥ D} |x|^{-8} dx = 4π/(5 D⁵)`, computed in polar coordinates
(`MeasureTheory.integral_fun_norm_addHaar`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Radial profile `r ↦ r^{-8}` on `[D, ∞)`, zero below `D`. -/
private def gapProf (D : ℝ) (r : ℝ) : ℝ :=
  (Ici D).indicator (fun r : ℝ => r ^ (-8 : ℝ)) r

private lemma gapProf_nonneg {D : ℝ} (hD : 0 < D) (r : ℝ) : 0 ≤ gapProf D r := by
  unfold gapProf
  apply Set.indicator_nonneg
  intro r hr
  exact Real.rpow_nonneg (le_trans hD.le (mem_Ici.1 hr)) _

private lemma gapProf_pointwise {D : ℝ} (x : UnforcedLeray.Space) :
    Set.indicator {x : UnforcedLeray.Space | D ≤ ‖x‖}
      (fun x : UnforcedLeray.Space => ENNReal.ofReal ((‖x‖ ^ 4)⁻¹) ^ (2 : ℝ)) x
      = ENNReal.ofReal (gapProf D ‖x‖) := by
  by_cases hx : D ≤ ‖x‖
  · have hx' : x ∈ {x : UnforcedLeray.Space | D ≤ ‖x‖} := hx
    rw [Set.indicator_of_mem hx', gapProf, Set.indicator_of_mem (mem_Ici.2 hx),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    congr 1
    rw [Real.rpow_two, inv_pow, ← pow_mul, show (-8 : ℝ) = -((8 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
  · have hx' : x ∉ {x : UnforcedLeray.Space | D ≤ ‖x‖} := hx
    have hn : ‖x‖ ∉ Ici D := fun h => hx (mem_Ici.1 h)
    rw [Set.indicator_of_notMem hx', gapProf, Set.indicator_of_notMem hn, ENNReal.ofReal_zero]

theorem gapKernel_sq_lintegral_le {D : ℝ} (hD : 0 < D) : ∫⁻ x in {x : UnforcedLeray.Space | D ≤ ‖x‖}, (ENNReal.ofReal ((‖x‖ ^ 4)⁻¹)) ^ (2 : ℝ) ≤ ENNReal.ofReal (4 * Real.pi / 5 * (D⁻¹) ^ 5) := by
  have hS : MeasurableSet {x : UnforcedLeray.Space | D ≤ ‖x‖} :=
    measurableSet_le measurable_const measurable_norm
  have h1 : ∫⁻ x in {x : UnforcedLeray.Space | D ≤ ‖x‖}, (ENNReal.ofReal ((‖x‖ ^ 4)⁻¹)) ^ (2 : ℝ)
      = ∫⁻ x : UnforcedLeray.Space, ENNReal.ofReal (gapProf D ‖x‖) := by
    rw [← lintegral_indicator hS]
    exact lintegral_congr (fun x => gapProf_pointwise x)
  -- the profile is integrable on the sphere-radial side
  have hIci : IntegrableOn (fun t : ℝ => t ^ (-6 : ℝ)) (Ici D) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_Ioi_rpow_of_lt (by norm_num) hD
  have hIntInd : Integrable ((Ici D).indicator (fun t : ℝ => t ^ (-6 : ℝ))) :=
    hIci.integrable_indicator measurableSet_Ici
  -- pointwise identity on `(0, ∞)` after the polar weight `y ^ (3 - 1)`
  have hprof : ∀ y ∈ Ioi (0 : ℝ),
      y ^ (3 - 1) • gapProf D y = (Ici D).indicator (fun t : ℝ => t ^ (-6 : ℝ)) y := by
    intro y hy
    have hy0 : 0 < y := hy
    by_cases hyD : D ≤ y
    · unfold gapProf
      rw [Set.indicator_of_mem (mem_Ici.2 hyD), Set.indicator_of_mem (mem_Ici.2 hyD), smul_eq_mul]
      rw [show (-6 : ℝ) = (-8 : ℝ) + 2 by norm_num, Real.rpow_add hy0, Real.rpow_two]
      norm_num
      ring
    · have hn : y ∉ Ici D := fun h => hyD (mem_Ici.1 h)
      unfold gapProf
      rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hn, smul_zero]
  have hIoi : IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ UnforcedLeray.Space - 1) •
      gapProf D y) (Ioi 0) := by
    rw [finrank_euclideanSpace_fin]
    refine IntegrableOn.congr_fun ?_ (fun y hy => (hprof y hy).symm) measurableSet_Ioi
    exact hIntInd.integrableOn
  have hint : Integrable (fun x : UnforcedLeray.Space => gapProf D ‖x‖) :=
    (integrable_fun_norm_addHaar volume).2 hIoi
  have hV : volume.real (Metric.ball (0 : UnforcedLeray.Space) 1) = Real.pi * 4 / 3 := by
    rw [Measure.real, EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal zero_le_one,
      ENNReal.toReal_ofReal (by positivity)]
    norm_num
  have hI : ∫ y in Ioi (0 : ℝ), y ^ (3 - 1) • gapProf D y = (D⁻¹) ^ 5 / 5 := by
    rw [setIntegral_congr_fun measurableSet_Ioi hprof, setIntegral_indicator measurableSet_Ici,
      Set.inter_eq_right.mpr (show Ici D ⊆ Ioi (0 : ℝ) from fun x (hx : x ∈ Ici D) => lt_of_lt_of_le hD hx),
      integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt (by norm_num) hD]
    rw [show (-6 : ℝ) + 1 = -((5 : ℕ) : ℝ) by norm_num, Real.rpow_neg hD.le,
      Real.rpow_natCast, inv_pow]
    ring
  have hval : ∫ x : UnforcedLeray.Space, gapProf D ‖x‖ = 4 * Real.pi / 5 * (D⁻¹) ^ 5 := by
    rw [integral_fun_norm_addHaar volume (gapProf D), hV, finrank_euclideanSpace_fin, hI]
    simp only [nsmul_eq_mul, smul_eq_mul]
    push_cast
    ring
  have hnn : 0 ≤ᵐ[volume] (fun x : UnforcedLeray.Space => gapProf D ‖x‖) :=
    Filter.Eventually.of_forall (fun x => gapProf_nonneg hD ‖x‖)
  have h2 : ∫⁻ x : UnforcedLeray.Space, ENNReal.ofReal (gapProf D ‖x‖)
      = ENNReal.ofReal (4 * Real.pi / 5 * (D⁻¹) ^ 5) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, hval]
  rw [h1, h2]

end UnforcedLeray.Short.PartIIIb.Concrete

end
