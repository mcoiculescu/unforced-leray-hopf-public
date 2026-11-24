import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_1_1_6_Bridges
import UnforcedLeray.Lib.HeatCylinder.H3ActualLimit

/-!
# Bridge 2a: the normalized kernel input is periodic a.e.

Proves `TensorKernelInputPeriodicAE` (Bridges file, Bridge 2a). Source lines 261-288 of
`the November 2 reference manuscript`. The proof is the body of
`UnforcedLeray.HeatCylinder.tensorH3KernelInput_coe_ae_ofCylSmooth`
(`Lib/HeatCylinder/H3ActualLimit.lean:560`) with the value identity `hvalue` replaced by the
hypothesis `hval`. The private helpers `tensorH3ValueRep`, `h3Measure_eq_cell` and
`ae_tensorH3ValueRep_cell` are re-stated here under `kernel`-prefixed names.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB (TensorVal)
open UnforcedLeray.HeatCylinder

private lemma kernel_h3Measure_eq_cell (c : ℝ) :
    UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = UnforcedLeray.Cyl.cellμ c := by
  rw [UnforcedLeray.Cyl.wμ_ρwW]
  simp [UnforcedLeray.Cyl.wμ]

private noncomputable def kernelH3ValueRep {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.TrainB.TensorH3 c) : Plane → TensorVal :=
  AEStronglyMeasurable.mk
    (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 x)
    (Lp.aestronglyMeasurable _)

private theorem kernel_ae_h3ValueRep_cell {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.TrainB.TensorH3 c) :
    kernelH3ValueRep hc x =ᵐ[UnforcedLeray.Cyl.cellμ c]
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 x : Plane → TensorVal) := by
  let v := UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 x
  have hv : AEStronglyMeasurable (v : Plane → TensorVal)
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) := Lp.aestronglyMeasurable v
  have heq := hv.ae_eq_mk
  simpa only [kernelH3ValueRep, v, kernel_h3Measure_eq_cell] using heq.symm

/-- Bridge 2a, as the theorem `tensorKernelInputPeriodicAE`. -/
theorem tensorKernelInputPeriodicAE : TensorKernelInputPeriodicAE := by
  intro c hc X T hT hval
  -- Step 1: the periodic lift of the chosen representative is `T` a.e. on the centered cell.
  have hfield : tensorH3KernelRep hc X =ᵐ[UnforcedLeray.Cyl.cellμ c] T := by
    filter_upwards [kernel_ae_h3ValueRep_cell hc X,
      ae_restrict_mem (UnforcedLeray.Cyl.measurableSet_cell c), hval] with z hrep hzcell hv
    have hz : centeredPerLift hc (kernelH3ValueRep hc X) z =
        (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 X : Plane → TensorVal) z := by
      rw [centeredPerLift_eq_on_cell hc _ hzcell]
      exact hrep
    change UnforcedLeray.TrainB.tensorToPlaneCLE.toContinuousLinearMap
      (centeredPerLift hc (kernelH3ValueRep hc X) z) = T z
    rw [hz]
    simpa using hv
  -- Step 2: periodic fields equal a.e. on the centered cell agree a.e. on the normalized cell.
  have hrep := ae_eq_of_ae_centered_periodic hc
    (periodic_tensorH3KernelRep hc X) hT hfield
  -- Step 3: the kernel input is the lift a.e. on the normalized cell.
  have hclass := (memLp_tensorH3KernelRep_normalized hc X).coeFn_toLp
  have hclass' : (tensorH3KernelInput hc X : Plane → Plane × Plane) =ᵐ[
      UnforcedLeray.B0284.cellMeasure c] tensorH3KernelRep hc X := by
    simpa [tensorH3KernelInput] using hclass
  exact hclass'.trans hrep

end UnforcedLeray.Short.PartI
