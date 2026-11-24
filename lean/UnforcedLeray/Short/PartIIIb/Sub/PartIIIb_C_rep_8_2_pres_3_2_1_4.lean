import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_org

/-!
# `exactPresDecay` (`PartIII-b:C/rep/8/2/pres/3/2/1/4`)

Source of record: `the November 2 reference manuscript`
117-118, 2607-2612, 2641-2642, 2525-2530, 5245-5257 (the full pressure is `p_U = Σ R_iR_j(U_iU_j)`).

The standing fact `ExactPresDecayAt (D.level n)` is the field `presL2` of
`SeqData.IsActualLevel` (`Concrete/ReturnInst.lean`), and `RepairStanding` carries the eventual
actuality `actual`.  The level `D.level n` has `pres := D.pres n`, so the field applies up to
definitional unfolding.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- **`ExactPresDecay` along the sequence** (source 117-118, 2641-2642, 5245-5257): the full
pressure of the exact background is in the `L²`-modulo-constants class at every phase with
`∇p ∈ L^{11/4}`, for all large `n`.  Taken from the actual range of the standing hypotheses. -/
theorem exactPresDecay (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.ExactPresDecay := by
  filter_upwards [hst.actual] with n h
  exact h.presL2

end UnforcedLeray.Short.PartIIIb.Concrete
