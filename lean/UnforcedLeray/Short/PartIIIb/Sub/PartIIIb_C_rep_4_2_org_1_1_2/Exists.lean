import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_4_2_org_1_1_2
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.StressPairAE

/-!
# `PartIII-b:C/rep/4/2/org/1/1/2/1`: `SepInvExists`

Source `the November 2 reference manuscript` 4145, 1556-1572.

`sepInvExists`: at the large levels and `z ∈ [-1, 1]` the weak stress inverse is the field `stress`
of the pinned operators `RegimePins` (`SeqData.RepairStanding.pins`, `Estimates.lean`); no global
existence statement (`PartIIa.NearStressMapExists`, `StressTransportExists`) is used.

`sepInvExists_of_inputs` (kept) is the earlier reduction through `StressTransportExists` and
`StressMapWeakSol`, with `stressPairAE` discharged unconditionally.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `SepInvExists` from the transport and stress-map inputs and the actuality of the levels. -/
theorem sepInvExists_of_inputs (dm dp : ℝ) (hST : StressTransportExists)
    (hW : NearInst.StressMapWeakSol)
    (hact : ∀ D : SeqData, D.RepairStanding dm dp → ∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n) :
    SepInvExists dm dp := by
  intro D hst
  exact seqStressInverse_of hST hW NearInst.stressPairAE D hst.dm_pos hst.omega_ne hst.sigma_pos
    hst.sigma_lt (by linarith [hst.mZ_gt]) hst.C0_pos (hact D hst)

/-- **Existence of the weak stress inverse along the sequence** (source 4145, 1556-1572): the
field `stress` of `RepairStanding.pins`. -/
theorem sepInvExists (dm dp : ℝ) : SepInvExists dm dp := fun D hst => by
  filter_upwards [hst.pins] with n hp z hz
  exact (hp z hz).stress

end UnforcedLeray.Short.PartIIIb.Concrete
