import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_1_1_2
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.CellPtHT
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.CellPtInvH
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.CellPtH
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_2.Linear
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_2.Bound

/-!
# `PartIII-b:C/rep/5/1/1/1/2/org`: the closed near pieces in one file

Source `the November 2 reference manuscript` 1675-1690 (the recentring `cellPt`
and the cell measures `H`, `H_T` of the near stress map) and 3427-3440 (the free causal pin: linear
in the source, bounded in energy).

The three recentring identities (`cellPtHT_eq`, `cellPtInvH_eq`, `cellPtH_eq`, now sharing
`Masked/Proofs/CellPtShared.lean`) and the two pin facts (`freeStressPinLinear_proof`,
`freeStressPinBound_proof`, now sharing one `FlatFreeGain` chain over `hh7/Props.lean`) are imported
together with the reduction `nearOpsExistCC_of`.

* `nearPinCellClosed` : the conjunction of the five facts (the energy bound of the pin takes the free
  solver `FreeCausalExistsUnique` as its argument, as `freeStressPinBound_proof` does).
* `nearOpsExistCC_of'` : `nearOpsExistCC_of` with these five facts discharged; the remaining
  hypotheses are `FreeCausalExistsUnique` (Part III-a; the closed `IIIa.freeCausalExistsUnique` in
  `PartIII-a/T18_FreeCausal.lean` cannot yet be imported next to `PartIII-a/ComposeCorollary.lean`:
  both define `IIIa.measurable_tnorm2`), `NearStressMapExists` (Part II-a), `FarKernelL2`,
  `FarKernelLinear` (Masked far kernel), `TrainFluctuationDecay`, `TrainMeanExpansion`,
  `TrainMeanEquations` (Part I) and `StressCoefficients` (Part III-a).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

/-- The recentring identities for `H_T`, `H` and the inverse recentring, and the linearity and
energy bound of the free stress pin (source 1675-1690, 3427-3440). -/
theorem nearPinCellClosed (hU : UnforcedLeray.Short.IIIa.FreeCausalExistsUnique) :
    (∀ c : ℝ, 0 < c → Masked.CellPtHT c) ∧ (∀ c : ℝ, 0 < c → Masked.CellPtInvH c) ∧
      (∀ c : ℝ, 0 < c → Masked.CellPtH c) ∧ FreeStressPinLinear ∧ FreeStressPinBound :=
  ⟨Masked.cellPtHT_eq, Masked.cellPtInvH_eq, Masked.cellPtH_eq, freeStressPinLinear_proof,
    freeStressPinBound_proof hU⟩

/-- `nearOpsExistCC_of` with the pin and the recentring identities discharged
(source 3427-3440, 3866-3914, 1675-1690). -/
theorem nearOpsExistCC_of' (hU : UnforcedLeray.Short.IIIa.FreeCausalExistsUnique)
    (hN : UnforcedLeray.Short.PartIIa.NearStressMapExists)
    (hL : Masked.FarKernelL2) (hA : Masked.FarKernelLinear)
    (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (hM : UnforcedLeray.Short.PartI.TrainMeanExpansion)
    (hE : UnforcedLeray.Short.PartI.TrainMeanEquations)
    (hSC : UnforcedLeray.Short.IIIa.StressCoefficients) : NearOpsExistC :=
  nearOpsExistCC_of hU hN (nearPinCellClosed hU).2.2.2.1 (nearPinCellClosed hU).2.2.2.2
    (nearPinCellClosed hU).1 (nearPinCellClosed hU).2.1 (nearPinCellClosed hU).2.2.1
    hL hA hF hM hE hSC

end UnforcedLeray.Short.PartIIIb.NearInst
