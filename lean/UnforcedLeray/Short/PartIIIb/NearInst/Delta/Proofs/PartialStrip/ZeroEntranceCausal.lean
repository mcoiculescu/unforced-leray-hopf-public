import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.ForwardUniq.Props
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.ForwardUniq.CoreWindow
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.ForwardUniq.SigmaDeriv
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.ForwardUniq.WeightFamily
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.ForwardUniq.OneWeight
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.ForwardUniq.ZeroEntranceSmall
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.ForwardUniq.IntervalZero
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.ForwardUniq.AeOfIntervals
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.ForwardUniq.SliceZero
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.ForwardUniq.SourceMeas
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.ForwardUniq.SourceTNorm
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.ForwardUniq.WindowR
import UnforcedLeray.Short.PartIIIa.FlatCausal
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.Inequalities.AgeSlice
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.Inequalities.GainLocF
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.FlatWeakFromDensity
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.CoreImpliesWeighted.EnergyLocInt

/-!
# `zeroEntranceCausal_of` (item `PartIII-b:C/near/delta/9/1`)

Source of record: `the November 2 reference manuscript` 3541-3545 (forward energy
uniqueness on an initial age interval, which also proves causality).

The proof is the assembly of the accepted leaves:
* `lionsMagenesCyl (IIIa.flatWeakFromDensity IIIa.divFreeCutoffDensity)` gives `IIIa.CoreAll`;
* `IIIa.energyLocIntegrable` gives `EnergyLocIntegrable`;
* `IIIa.ageSlice` feeds `fuZeroEntranceSlice_of`;
* `IIIa.gainLocF` is the local square integrability of the gain-free source;
* the ForwardUniq leaves supply the remaining `FU*` predicates, and
  `freeForwardUniquenessML_of` / `zeroEntranceCausal_of_forwardML` finish the argument.

The hypothesis `hU` is not used: the causal zero-entrance solution is controlled by the forward
energy identity rather than by uniqueness of `FreeCausalExistsUnique`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

theorem zeroEntranceCausal_of (hU : UnforcedLeray.Short.IIIa.FreeCausalExistsUnique) :
    UnforcedLeray.Short.PartIIIb.NearInst.Delta.ZeroEntranceCausal :=
  zeroEntranceCausal_of_forwardML
    (freeForwardUniquenessML_of
      (lionsMagenesCyl
        (UnforcedLeray.Short.IIIa.flatWeakFromDensity UnforcedLeray.Short.IIIa.divFreeCutoffDensity))
      UnforcedLeray.Short.IIIa.energyLocIntegrable fuWindowR fuCoreWindow
      (fuZeroEntranceSlice_of UnforcedLeray.Short.IIIa.ageSlice) fuIntervalZero fuAeOfIntervals
      fuSliceZero)
    fuSourceMeas fuSourceTNorm UnforcedLeray.Short.IIIa.gainLocF

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
