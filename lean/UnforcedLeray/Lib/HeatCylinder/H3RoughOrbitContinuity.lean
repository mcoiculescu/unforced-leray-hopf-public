import UnforcedLeray.Lib.HeatCylinder.H3SmoothDerivativeBridge
import UnforcedLeray.Lib.HeatCylinder.H3Density
import UnforcedLeray.Lib.HeatCylinder.OrbitBounds
import UnforcedLeray.Lib.HeatCylinder.SmoothCLM

/-!
# Positive-age continuity of the actual rough H³ Gaussian orbit

The smooth orbit is continuous in the full graph norm. Smooth density and the period-independent
local operator bound then extend this continuity to every actual TensorH3 input.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)

/-- The actual rough H³ heat-divergence orbit, set to zero at nonpositive ages. -/
noncomputable def actualHeatDivH3Orbit {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.TrainB.TensorH3 c) (θ : ℝ) :
    UnforcedLeray.TrainB.VectorH3 c :=
  if hθ : 0 < θ then actualHeatDivH3CLM hc hθ x else 0

/-- On a genuine smooth tensor class the rough realization is its actual smooth Gaussian output. -/
theorem actualHeatDivH3CLM_apply_ofCylSmooth {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → UnforcedLeray.TrainB.TensorVal}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T) :
    actualHeatDivH3CLM hc hθ
      (UnforcedLeray.Sob.W.ofCylSmooth
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
        (F := UnforcedLeray.TrainB.TensorVal) (k := 3) (p := 2) hc T hT) =
      heatDivH3 hc hθ
        (isCylSmooth_postcomp_clm hT
          UnforcedLeray.TrainB.tensorToPlaneCLE.toContinuousLinearMap) := by
  apply vectorH3NormalizedValue_injective hc
  rw [actualHeatDivH3CLM_apply,
    vectorH3NormalizedValue_actualHeatDivH3 hc hθ,
    vectorH3NormalizedValue_heatDivH3 hc hθ
      (isCylSmooth_postcomp_clm hT
        UnforcedLeray.TrainB.tensorToPlaneCLE.toContinuousLinearMap)]
  apply congrArg (heatDivVecL2CLM hc hθ)
  let S : Plane → Plane × Plane := fun z =>
    UnforcedLeray.TrainB.tensorToPlaneCLE (T z)
  have hS : UnforcedLeray.Sob.IsCylSmooth c S :=
    isCylSmooth_postcomp_clm hT
      UnforcedLeray.TrainB.tensorToPlaneCLE.toContinuousLinearMap
  have hmemS : MemLp S 2 (UnforcedLeray.B0284.cellMeasure c) :=
    memLp_tensor_iterD_cylSmooth_normalized hc hS []
  apply Lp.ext
  filter_upwards [tensorH3KernelInput_coe_ae_ofCylSmooth hc hT,
    hmemS.coeFn_toLp]
    with z hinput hsmooth
  exact hinput.trans hsmooth.symm

/-- Positive-age continuity of the actual Gaussian divergence operator on the full TensorH3
graph. -/
theorem continuousAt_actualHeatDivH3Orbit {c θ₀ : ℝ} (hc : 0 < c)
    (hθ₀ : 0 < θ₀) (x : UnforcedLeray.TrainB.TensorH3 c) :
    ContinuousAt (actualHeatDivH3Orbit hc x) θ₀ := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  let a : ℝ := θ₀ / 2
  have ha : 0 < a := by dsimp [a]; linarith
  let K : ℝ := (ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL :
      Plane →L[ℝ] Vec)‖ * ENNReal.ofReal (heatDivL2Coeff a)).toReal
  have hK : 0 ≤ K := by dsimp [K]; exact ENNReal.toReal_nonneg
  let δapp : ℝ := ε / (4 * (K + 1))
  have hδapp : 0 < δapp := by
    dsimp [δapp]
    exact div_pos hε (mul_pos (by norm_num) (by linarith))
  obtain ⟨y, T, hT, hyrep, hyLim⟩ := exists_smoothTensorH3_sequence hc x
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hyLim) δapp hδapp
  let n : ℕ := N
  have hclose : dist (y n) x < δapp := hN n (by simp [n])
  have hnormClose : ‖x - y n‖ < δapp := by
    simpa [dist_eq_norm, norm_sub_rev] using hclose
  let S : Plane → Plane × Plane := fun z =>
    UnforcedLeray.TrainB.tensorToPlaneCLE (T n z)
  have hS : UnforcedLeray.Sob.IsCylSmooth c S :=
    isCylSmooth_postcomp_clm (hT n)
      UnforcedLeray.TrainB.tensorToPlaneCLE.toContinuousLinearMap
  have hySmooth : y n = UnforcedLeray.Sob.W.ofCylSmooth
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
      (F := UnforcedLeray.TrainB.TensorVal) (k := 3) (p := 2) hc (T n) (hT n) := hyrep n
  have hcontSmooth := continuousAt_heatDivH3SmoothOrbit hc hθ₀ hS
  obtain ⟨δsmooth, hδsmooth, hsmall⟩ :=
    (Metric.continuousAt_iff.mp hcontSmooth) (ε / 2) (half_pos hε)
  have hparam : 0 < a := ha
  have hcoefSmall : 2 * K * δapp < ε / 2 := by
    dsimp [δapp]
    have hden : 0 < 4 * (K + 1) := by positivity
    field_simp
    nlinarith [hK, hε]
  have hδpos : 0 < min δsmooth (θ₀ / 2) := by
    apply lt_min hδsmooth
    linarith
  refine ⟨min δsmooth (θ₀ / 2), hδpos, ?_⟩
  intro θ hdist
  have hdistSmooth : dist θ θ₀ < δsmooth := lt_of_lt_of_le hdist (min_le_left _ _)
  have hdistHalf : dist θ θ₀ < θ₀ / 2 := lt_of_lt_of_le hdist (min_le_right _ _)
  have hθ : 0 < θ := by
    have := abs_lt.mp (by simpa [Real.dist_eq] using hdistHalf)
    linarith
  have hθa : a ≤ θ := by
    dsimp [a]
    have := abs_lt.mp (by simpa [Real.dist_eq] using hdistHalf)
    linarith
  have hAθ := UnforcedLeray.HeatCylinder.norm_actualHeatDivH3CLM_le_at_left
    hc ha hθ hθa (x - y n)
  have hAθ₀ := UnforcedLeray.HeatCylinder.norm_actualHeatDivH3CLM_le_at_left
    hc ha hθ₀ (by dsimp [a]; linarith) (x - y n)
  have hleft : dist (actualHeatDivH3CLM hc hθ x)
      (actualHeatDivH3CLM hc hθ (y n)) ≤ K * ‖x - y n‖ := by
    rw [dist_eq_norm, ← map_sub]
    exact hAθ
  have hright : dist (actualHeatDivH3CLM hc hθ₀ (y n))
      (actualHeatDivH3CLM hc hθ₀ x) ≤ K * ‖x - y n‖ := by
    rw [dist_eq_norm, ← map_sub]
    have hsub : y n - x = -(x - y n) := by abel
    rw [hsub, map_neg, norm_neg]
    exact hAθ₀
  have hmiddle : dist (actualHeatDivH3CLM hc hθ (y n))
      (actualHeatDivH3CLM hc hθ₀ (y n)) < ε / 2 := by
    rw [hyrep n]
    rw [actualHeatDivH3CLM_apply_ofCylSmooth hc hθ (hT n),
        actualHeatDivH3CLM_apply_ofCylSmooth hc hθ₀ (hT n)]
    simpa [S, heatDivH3SmoothOrbit, dif_pos hθ, dif_pos hθ₀] using hsmall hdistSmooth
  have htri := dist_triangle4
    (actualHeatDivH3CLM hc hθ x)
    (actualHeatDivH3CLM hc hθ (y n))
    (actualHeatDivH3CLM hc hθ₀ (y n))
    (actualHeatDivH3CLM hc hθ₀ x)
  have hbound : dist (actualHeatDivH3CLM hc hθ x)
      (actualHeatDivH3CLM hc hθ₀ x) < ε := by
    calc
      _ ≤ dist (actualHeatDivH3CLM hc hθ x)
            (actualHeatDivH3CLM hc hθ (y n)) +
          dist (actualHeatDivH3CLM hc hθ (y n))
            (actualHeatDivH3CLM hc hθ₀ (y n)) +
          dist (actualHeatDivH3CLM hc hθ₀ (y n))
            (actualHeatDivH3CLM hc hθ₀ x) := htri
      _ < ε := by
        have hclose' : K * ‖x - y n‖ ≤ K * δapp :=
          mul_le_mul_of_nonneg_left (le_of_lt hnormClose) hK
        nlinarith [hleft, hmiddle, hright, hclose', hcoefSmall, hε]
  simpa [actualHeatDivH3Orbit, dif_pos hθ, dif_pos hθ₀] using hbound

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.actualHeatDivH3CLM_apply_ofCylSmooth
#print axioms UnforcedLeray.HeatCylinder.continuousAt_actualHeatDivH3Orbit

