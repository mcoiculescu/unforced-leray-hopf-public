import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_1

/-!
# Part I, task `PartI:T08/4/1/1/1/2` (`VelJetLocalL2`): time-local `L²` bound for the train velocity

Source: `the November 2 reference manuscript` lines 261-288 and 326-329.

This file only splits the target into two leaves by the age condition on `width ν s`:

* `VelJetLocalWindow`: the time-local bound at ages with `width ν s < c²`;
* `VelJetLocalLate`: the same at ages with `c² ≤ width ν s`.

`velJetLocalL2_of` shows the target `VelJetLocalL2` follows from the two leaves. Neither leaf is
proved here. The existing leaf `TrainVelocityJetL2` (in `Sub/PartI_T08_2.lean`) gives only
pointwise `L²(cell)` membership at one age `s` with `width ν s ≤ c²`. It gives no bound that is
uniform for `r` near `s`, and nothing at late ages. The uniform bound needs the energy inequality
on a time window, with Gronwall on that window, which the library does not yet have.
So the target `velJetLocalL2_proof : VelJetLocalL2` is not proved in this file.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (width)

/-- Leaf: time-local `L²(cell)` bound on word derivatives of the train velocity at ages
`width ν s < c²`, uniform for `r` near `s`. -/
def VelJetLocalWindow : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
    ∀ s : ℝ, 0 < s → width ν s < c ^ 2 → ∀ (w : List Bool) (k : Fin 2),
      ∃ ε : ℝ, 0 < ε ∧ ∃ K : ℝ, ∀ r : ℝ, 0 < r → |r - s| < ε →
        MemLp (wordComp w (tr.v r) k) 2 (Cyl.cellμ c) ∧
        ∫ z in Cyl.cell c, (wordComp w (tr.v r) k z) ^ 2 ≤ K

/-- Leaf: the same time-local bound at the late ages `c² ≤ width ν s`. -/
def VelJetLocalLate : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
    ∀ s : ℝ, 0 < s → c ^ 2 ≤ width ν s → ∀ (w : List Bool) (k : Fin 2),
      ∃ ε : ℝ, 0 < ε ∧ ∃ K : ℝ, ∀ r : ℝ, 0 < r → |r - s| < ε →
        MemLp (wordComp w (tr.v r) k) 2 (Cyl.cellμ c) ∧
        ∫ z in Cyl.cell c, (wordComp w (tr.v r) k z) ^ 2 ≤ K

/-- Conditional form of the target: `VelJetLocalL2` from the two age leaves. -/
theorem velJetLocalL2_of (hW : VelJetLocalWindow) (hL : VelJetLocalLate) : VelJetLocalL2 := by
  intro ν c hν hc tr htr s hs w k
  by_cases hlt : width ν s < c ^ 2
  · exact hW ν c hν hc tr htr s hs hlt w k
  · exact hL ν c hν hc tr htr s hs (not_lt.mp hlt) w k

end UnforcedLeray.Short.PartI
