import UnforcedLeray.Short.PartIIa.Sub.F08
import UnforcedLeray.Short.PartIIa.Tasks.F08aLerayCFreeComm
import UnforcedLeray.Lib.LerayC.Phase
import UnforcedLeray.Units.B0421.Phase
import UnforcedLeray.Units.B0421.FreeC

/-!
# Part II-a, task `PartII-a:F08/2`: the Leray projection commutes with `𝒯_ν(r)` on `Y_q`

Source `the November 2 reference manuscript` lines 1498-1500 (phase translation
commutes with Leray). Uses `lerayCFreeComm_proof` (task `PartII-a:F08/1`) to get the slice-wise
commutation of `𝐏` with `S_ν(r)`, then `lerayY_comm_slicewise` and `lerayY_phase`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- **`PartII-a:F08/2`** (source 1498-1500): the Leray projection commutes with the phase
operator `𝒯_ν(r)` on `Y_q`. -/
theorem lerayYPhaseTComm_proof : LerayYPhaseTComm := by
  intro q _ hq1 hq P _ ν r g
  have hN : ((lerayC q hq1 hq).restrictScalars ℝ).comp ((B0421.freeC hq ν r).restrictScalars ℝ) =
      ((B0421.freeC hq ν r).restrictScalars ℝ).comp ((lerayC q hq1 hq).restrictScalars ℝ) := by
    ext1 F
    exact congrArg (fun T : Lp CVec3 q (volume : Measure Space) →L[ℂ] _ => T F)
      (lerayCFreeComm_proof q hq1 hq ν r)
  have h := lerayY_comm_slicewise (P := P) hq1 hq _ hN
  have h2 := congrArg (fun T => T (DomAddAct.mk (-(r : AddCircle P)) +ᵥ g)) h
  have h3 := lerayY_phase (P := P) hq1 hq (-(r : AddCircle P)) g
  change lerayY P q hq1 hq ((B0421.freeC hq ν r).compLpL q AddCircle.haarAddCircle
      (DomAddAct.mk (-(r : AddCircle P)) +ᵥ g)) =
    (B0421.freeC hq ν r).compLpL q AddCircle.haarAddCircle
      (DomAddAct.mk (-(r : AddCircle P)) +ᵥ lerayY P q hq1 hq g)
  rw [← h3]
  exact h2

end UnforcedLeray.Short.PartIIa
