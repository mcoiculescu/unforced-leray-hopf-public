import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_11_2_dec
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Background.Levels
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Background.Seq
import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.CoeffMult
import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.SplitMult

/-!
# `PartIII-b:C/rep/11/2/1`: existence of the split multiplier at the levels of `RepairStanding`

Source `the November 2 reference manuscript` 2703-2713, 3876-3878.

Reduction, sorry-free: the split multiplier exists at the large levels (`seq_splitMult`,
`ReturnInst/Background/Seq.lean`) from `SplitMultLevels` (`splitMultLevels_of`,
`ReturnInst/Background/Levels.lean`), which needs the coefficient bounds `NearInst.SplitMultBound`
(`NearInst.splitMultBound_of`, from `IIIa.StressCoefficients`) and the multiplier construction
`NearInst.coeffMultExists` (unconditional).  The hypotheses of `seq_splitMult` are read off
`RepairStanding`.

Open leaf: `IIIa.StressCoefficients` is not a theorem.  It is `stressCoefficients_of`
(`PartIII-a/T23_StressExactSplit/T23_9.lean`), which takes `IIIa.RawCoeffLate` and
`IIIa.RawCoeffEarly` (both `def`s, `PartIII-a/StressInputs.lean:47,59`) and `IIIa.InletCoeffBounds`
(which is the theorem `IIIa.inletCoeffBounds`, `T23_StressExactSplit/T23_3.lean:17`).  The theorems
`rawCoeffLate_of` and `rawCoeffEarly_of` (`Sub/T23_1_org.lean`, `Sub/T23_2_org.lean`) still take
unproved velocity and completion leaves.

The unconditional `nearMUExists` does not use this route: at the large levels the split multiplier
is the field `split` of the pinned operators `RegimePins` (`SeqData.RepairStanding.pins`,
`Estimates.lean`; source 2706, 3877-3878), taken at `z = 0`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace SeqData

/-- The reduction of the split multiplier leaf to the stress coefficient bounds. -/
theorem nearMUExists_of_stress (hSC : UnforcedLeray.Short.IIIa.StressCoefficients)
    (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.NearMUExists := by
  have hS : NearInst.SplitMultBound := NearInst.splitMultBound_of hSC
  exact seq_splitMult (splitMultLevels_of NearInst.coeffMultExists hS) D hst.dm_pos hst.m0_pos
    (le_of_lt hst.m0_lt) hst.C0_pos hst.mZ_gt hst.planar.eigenpair hst.omega_ne hst.actual

/-- **The split multiplier exists at the levels of `RepairStanding`** (source 2703-2713,
3876-3878): the field `split` of `RepairStanding.pins`. -/
theorem nearMUExists (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.NearMUExists := by
  filter_upwards [hst.pins] with n hp
  exact (hp 0 ⟨by norm_num, by norm_num⟩).split

end SeqData

end UnforcedLeray.Short.PartIIIb.Concrete

end
