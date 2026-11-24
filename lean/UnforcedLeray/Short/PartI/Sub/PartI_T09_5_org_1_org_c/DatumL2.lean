import UnforcedLeray.Short.PartI.Sub.PartI_T09_5_org_1_org_c
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.DatumWordL2

/-!
# `PartI:T09/5/org/1/org/c/3`: the initial datum has square-integrable word derivatives on the cell

Source: `the November 2 reference manuscript`,
lines 270-278 (`v 0 = trainDatum c`, a periodised Gaussian velocity) and 294.

Route: `IsTrain.initial` identifies `tr.v 0` with `B0140.trainDatum c`.  The proved draft
`trainDatumWordL2_proof` (`TrainDatumWordL2`, `DatumWordL2.lean`) gives `MemLp` of every word
derivative component in `L^2(cell c)`; `memLp_two_iff_integrable_sq` turns this into integrability
of the square, and `Integrable.lintegral_lt_top` gives the finiteness of the lintegral.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- **`TrainDatumJetL2Finite`** (source lines 270-278, 294): every word derivative of the initial
datum is square integrable on the cell. -/
theorem trainDatumJetL2Finite_proof : TrainDatumJetL2Finite := by
  intro ν c hν hc tr htr w k
  have hc0 : 0 < c := by linarith
  have hmem : MemLp (wordComp w (B0140.trainDatum c) k) 2 (Cyl.cellμ c) :=
    trainDatumWordL2_proof c hc0 w k
  have hint : Integrable (fun z : Plane => (wordComp w (B0140.trainDatum c) k z) ^ 2)
      (Cyl.cellμ c) :=
    (memLp_two_iff_integrable_sq hmem.aestronglyMeasurable).1 hmem
  have hinit : tr.v 0 = B0140.trainDatum c := tr.isTrain.initial
  rw [hinit]
  exact hint.lintegral_lt_top

end UnforcedLeray.Short.PartI
