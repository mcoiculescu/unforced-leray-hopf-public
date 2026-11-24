import UnforcedLeray.Short.PartI.Sub.PartI_T08_2_2.EnergyIneq
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.EnergyIneq.ConsAppend
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ForcingIBP

/-!
# Part I, task `PartI:T08/2/2/2/4/2`: `DerivWordLapComm` (spatial words commute with the Laplacian)

Target: `theorem derivWordLapComm_proof : UnforcedLeray.Short.PartI.DerivWordLapComm`.

Source of record: `the November 2 reference manuscript`, lines 276-288; the leaf
statement is in `Sub/PartI_T08_2_2/EnergyIneq.lean`.

Route: `Train.lapS h = ∂_q∂_q h + ∂_η∂_η h = A + B` with `A = derivWord [t,t] h`, `B = derivWord [f,f] h`.
Word derivatives are additive on smooth fields (`ForcingIBP.derivWord_add_smooth`), and a
two-letter word commutes past any word `u` on smooth fields (`dwcaComm` applied twice).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

theorem derivWordLapComm_proof : UnforcedLeray.Short.PartI.DerivWordLapComm := by
  intro h hh u
  have hA : ContDiff ℝ ∞ (B0151.derivWord [true, true] h) :=
    B0151.contDiff_derivWord hh [true, true]
  have hB : ContDiff ℝ ∞ (B0151.derivWord [false, false] h) :=
    B0151.contDiff_derivWord hh [false, false]
  have hL : ∀ g : Plane → ℝ, Train.lapS g =
      fun z => B0151.derivWord [true, true] g z + B0151.derivWord [false, false] g z :=
    fun g => rfl
  have key : ∀ b c : Bool, B0151.derivWord [b, c] (B0151.derivWord u h) =
      B0151.derivWord u (B0151.derivWord [b, c] h) := by
    intro b c
    have e : ∀ g : Plane → ℝ, B0151.derivWord [b, c] g =
        B0151.derivWord [b] (B0151.derivWord [c] g) := fun g => by cases b <;> rfl
    rw [e, e, dwcaComm c u h hh, dwcaComm b u (B0151.derivWord [c] h) (B0151.contDiff_derivWord hh [c])]
  rw [hL h, hL (B0151.derivWord u h),
    ForcingIBP.derivWord_add_smooth u (B0151.derivWord [true, true] h)
      (B0151.derivWord [false, false] h) hA hB,
    key true true, key false false]

end UnforcedLeray.Short.PartI
