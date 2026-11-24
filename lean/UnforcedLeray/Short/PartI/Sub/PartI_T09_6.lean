import UnforcedLeray.Short.PartI.Sub.PartI_T09
import UnforcedLeray.Short.PartI.TrainClass
import UnforcedLeray.Short.PartI.Sub.PartI_T09.TrainErrInitial

/-!
# Part I, task `PartI:T09/6` (audit decomposition): `TrainErrGradSup` from two leaves

Source of record: `the November 2 reference manuscript`, lines 270-288 and 355.

Proved here, from existing Lean and `Sub/PartI_T09/TrainErrInitial.lean`:
* `gradErrSup tr 0 = 0`, since `trainErr tr 0 = 0` (the datum equals the periodized Gaussian);
* `TrainErrGradSup` follows from two explicit inputs, `TrainErrGradBdd` (the sup of the first
  partials of `e(s)` is finite for `s ≥ 0`) and `TrainErrGradCont` (`s ↦ ‖∇e(s)‖_∞` is continuous
  on `[0,∞)`). Neither is proved here: the first is a uniform bound of the BUC derivatives of `v`
  and of `V_c^p` (`Train.Vc_bounds`), the second needs uniform-in-`z` time-continuity of the first
  partials of `e`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc width)

/-- Finiteness of the sup of the first partials of `e(s)` for every `s ≥ 0` (BUC class). -/
def TrainErrGradBdd : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
    ∀ s : ℝ, 0 ≤ s → BddAbove {x : ℝ | ∃ (β : Bool) (k : Fin 2) (z : Plane),
      x = |wordComp [β] (trainErr tr s) k z|}

/-- Continuity of `s ↦ ‖∇e(s)‖_∞` on `[0,∞)` for BUC trains (line 355). -/
def TrainErrGradCont : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
    ContinuousOn (gradErrSup tr) (Ici 0)

/-- `‖∇e(0)‖_∞ = 0`, since `e(0) = 0`. -/
theorem gradErrSup_zero_local {ν c : ℝ} (tr : B0140.TrainSol ν c) : gradErrSup tr 0 = 0 := by
  unfold gradErrSup
  have hset : {x : ℝ | ∃ (β : Bool) (k : Fin 2) (z : Plane),
      x = |wordComp [β] (trainErr tr 0) k z|} = {0} := by
    rw [trainErr_zero_local tr]
    ext x
    constructor
    · rintro ⟨β, k, z, rfl⟩
      simp [wordComp_zero_local]
    · intro hx
      obtain rfl := Set.mem_singleton_iff.1 hx
      exact ⟨true, 0, 0, by simp [wordComp_zero_local]⟩
  rw [hset, csSup_singleton]

/-- **Reduction of `PartI:T09/6`**: `TrainErrGradSup` from the boundedness and continuity inputs. -/
theorem trainErrGradSup_of (hbdd : TrainErrGradBdd) (hcont : TrainErrGradCont) :
    TrainErrGradSup := by
  intro ν c hν hc1 tr htr
  exact ⟨fun s hs => hbdd ν c hν hc1 tr htr s hs, gradErrSup_zero_local tr,
    hcont ν c hν hc1 tr htr⟩

end UnforcedLeray.Short.PartI
