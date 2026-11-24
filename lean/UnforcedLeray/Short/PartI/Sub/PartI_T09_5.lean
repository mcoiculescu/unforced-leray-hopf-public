import UnforcedLeray.Short.PartI.Sub.PartI_T09
import UnforcedLeray.Short.PartI.TrainClass
import UnforcedLeray.Units.B0169
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureOrth.Word

/-!
# Part I, task `PartI:T09/5`: reduction of `TrainErrInitial` to jet-energy right-continuity

Source of record: `the November 2 reference manuscript`, lines 261-288, 294, 341.

What is proved here, from existing Lean:
* `trainErr tr 0 = 0`, since `v(0)` is the datum `= Train.datum c = Vc ν c 0` (`B0140.IsTrain.initial`,
  `B0169.trainDatum_eq_datum`, `Train.Vc_zero`);
* every jet energy and the cell smoothness of the zero field;
* the weighted energy `E_N` is continuous within `[0, ∞)` at `0` once each jet energy is.

The one missing fact is the time-continuity of the jet energies of the error at age `0`, which is
the content of the BUC class (lines 270-288). It is isolated as the Prop `TrainJetEnergyRightCont`
and the main theorem `trainErrInitial_of` takes it as an explicit hypothesis. This file does NOT
prove `TrainErrInitial` unconditionally.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc width)

/-- The missing analytic input (BUC class, lines 270-288): for a BUC train, each jet energy of the
comparison error `e(s) = v(s) - V_c^p(s)` is right-continuous at age `0`. -/
def TrainJetEnergyRightCont : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → ∀ j : ℕ,
    ContinuousWithinAt (fun s => jetEnergy c j (trainErr tr s)) (Ici 0) 0

/-- A word derivative of the zero vector field vanishes. -/
theorem wordComp_zero_local (w : List Bool) (k : Fin 2) (z : Plane) :
    wordComp w (0 : Plane → Vec) k z = 0 := by
  unfold wordComp
  have h0 : (fun x : Plane => (0 : Plane → Vec) x k) = fun _ => (0 : ℝ) := by
    funext x; simp
  rw [h0, JetPressureWord.derivWord_zero]

theorem jetEnergy_zero_local (c : ℝ) (j : ℕ) : jetEnergy c j (0 : Plane → Vec) = 0 := by
  unfold jetEnergy jetPair
  simp [wordComp_zero_local]

theorem cellSmoothL2_zero_local (c : ℝ) : CellSmoothL2 c (0 : Plane → Vec) := by
  refine ⟨contDiff_zero_fun, fun _ => rfl, fun w k => ?_⟩
  have hf : wordComp w (0 : Plane → Vec) k = fun _ => 0 := funext fun z => wordComp_zero_local w k z
  rw [hf]
  exact ⟨aestronglyMeasurable_const, by simp⟩

/-- The comparison error at age `0` vanishes for every train of the BUC class. -/
theorem trainErr_zero_local {ν c : ℝ} (tr : B0140.TrainSol ν c) : trainErr tr 0 = 0 := by
  funext z
  show tr.v 0 z - Vc ν c 0 z = 0
  rw [tr.isTrain.initial, Train.Vc_zero, B0169.trainDatum_eq_datum, sub_self]

/-- **Reduction of `PartI:T09/5`**: `TrainErrInitial` follows from the time-continuity of the jet
energies at age `0` (`TrainJetEnergyRightCont`). -/
theorem trainErrInitial_proof_of (hcont : TrainJetEnergyRightCont) : TrainErrInitial := by
  intro ν c hν hc1 tr htr
  have hzero : trainErr tr 0 = 0 := trainErr_zero_local tr
  refine ⟨fun j => ?_, fun N δ => ?_, ?_⟩
  · rw [hzero]; exact jetEnergy_zero_local c j
  · have hterm : ∀ j ∈ Finset.range (N + 1),
        ContinuousWithinAt (fun s => (δ * width ν s) ^ j * jetEnergy c j (trainErr tr s))
          (Ici 0) 0 := by
      intro j _
      exact ContinuousWithinAt.mul
        (Continuous.continuousWithinAt (by unfold Train.width; fun_prop))
        (hcont ν c hν hc1 tr htr j)
    unfold ContinuousWithinAt weightedEnergy
    exact tendsto_finsetSum _ hterm
  · rw [hzero]; exact cellSmoothL2_zero_local c

end UnforcedLeray.Short.PartI
