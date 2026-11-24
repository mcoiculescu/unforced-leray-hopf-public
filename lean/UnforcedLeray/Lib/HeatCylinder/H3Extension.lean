import UnforcedLeray.Lib.HeatCylinder.H3GraphBridge

/-!
# Cauchy actual heat outputs from arbitrary TensorH3 data

The smooth dense representatives of any row-tensor H³ class have Cauchy derivative energy in the
actual product-plane tensor carrier. The Gaussian heat-divergence outputs therefore converge in
the complete train vector H³ graph.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.TrainB (TensorVal)

/-- For each genuine TensorH3 input, choose its smooth dense representatives, convert those rows
to the actual product-plane kernel tensor, and obtain a Cauchy sequence of actual heatDiv outputs
in the train H³ graph. -/
theorem exists_cauchy_heatDivH3_sequence {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x : UnforcedLeray.TrainB.TensorH3 c) :
    ∃ T : ℕ → Plane → Plane × Plane,
      ∃ hT : ∀ n, UnforcedLeray.Sob.IsCylSmooth c (T n),
        CauchySeq (smoothHeatOutputSequence hc hθ hT) := by
  obtain ⟨y, T, hT, hyrep, hlim⟩ := exists_smoothTensorH3_sequence hc x
  let L : TensorVal →L[ℝ] (Plane × Plane) :=
    UnforcedLeray.TrainB.tensorToPlaneCLE.toContinuousLinearMap
  let S : ℕ → Plane → Plane × Plane := fun n z => L (T n z)
  have hS : ∀ n, UnforcedLeray.Sob.IsCylSmooth c (S n) := by
    intro n
    exact UnforcedLeray.HeatCylinder.isCylSmooth_postcomp_clm (hT n) L
  have hsub : ∀ m n, UnforcedLeray.Sob.IsCylSmooth c (fun z => S m z - S n z) := by
    intro m n
    exact UnforcedLeray.HeatCylinder.isCylSmooth_sub (hS m) (hS n)
  have hC : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      UnforcedLeray.HeatCylinder.heatTensorH3Distance c (S m) (S n) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hlim.cauchySeq) ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have hcontract := UnforcedLeray.HeatCylinder.heatTensorH3Distance_tensorToPlane_le
      (hT m) (hT n)
    have henergy : UnforcedLeray.HeatCylinder.cylinderDerivativeEnergyDistance c
        (T m) (T n) = dist (y m) (y n) := by
      rw [UnforcedLeray.HeatCylinder.cylinderDerivativeEnergyDistance_eq_norm_ofCylSmooth
        hc (hT m) (hT n)]
      rw [UnforcedLeray.HeatCylinder.ofCylSmooth_tensor_sub_eq hc (hT m) (hT n)]
      rw [hyrep m, hyrep n, dist_eq_norm]
    calc
      UnforcedLeray.HeatCylinder.heatTensorH3Distance c (S m) (S n) ≤
          UnforcedLeray.HeatCylinder.cylinderDerivativeEnergyDistance c (T m) (T n) := by
        simpa [S, L] using hcontract
      _ = dist (y m) (y n) := henergy
      _ < ε := hN m hm n hn
  refine ⟨S, hS, ?_⟩
  exact heatOutputSequence_cauchy_of_heatTensorH3Distance hc hθ hS hsub hC

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.exists_cauchy_heatDivH3_sequence
