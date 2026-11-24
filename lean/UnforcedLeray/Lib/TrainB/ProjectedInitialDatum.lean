import UnforcedLeray.Lib.TrainB.InitialDatumP0H3

set_option autoImplicit false

noncomputable section

open MeasureTheory
open UnforcedLeray.Cyl

namespace UnforcedLeray.TrainB

/-- The actual Gaussian Train datum, represented in the H³ solenoidal range of the cylinder
Leray operator. -/
noncomputable def projectedInitialDatumH3 {c : ℝ} (hc : 0 < c) : VectorH3 c :=
  P0H3CLM hc (datumVecH3 hc)

theorem projectedInitialDatumH3_value {c : ℝ} (hc : 0 < c) :
    vecH3CellDerivCLM Sob.Idx.zero (projectedInitialDatumH3 hc) =
      (memLp_datum_word_derivative hc Sob.Idx.zero).toLp (Train.datum c) :=
  P0H3_datum_value_eq_datum hc

theorem projectedInitialDatumH3_solenoidal {c : ℝ} (hc : 0 < c) :
    vecH3CellDerivCLM Sob.Idx.zero (projectedInitialDatumH3 hc) ∈ Cyl.divFree c :=
  P0H3CLM_value_mem_divFree hc (datumVecH3 hc)

theorem projectedInitialDatumH3_norm_le {c : ℝ} (hc : 0 < c) :
    ‖projectedInitialDatumH3 hc‖ ≤ ‖datumVecH3 hc‖ :=
  P0H3CLM_apply_norm_le hc (datumVecH3 hc)

#print axioms UnforcedLeray.TrainB.projectedInitialDatumH3_value
#print axioms UnforcedLeray.TrainB.projectedInitialDatumH3_solenoidal
#print axioms UnforcedLeray.TrainB.projectedInitialDatumH3_norm_le

end UnforcedLeray.TrainB
