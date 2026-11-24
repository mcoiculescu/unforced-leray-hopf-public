import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.AdjWeakOf
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_6
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.TrainBdd
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.TerminalMem
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.Pairing
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.CoeffOf
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.TransportCoeff
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.VolterraWeak

/-!
# Part III-a, `PartIII-a:T21/2/7/1`: the weak reverse-time adjoint for the BUC train

Source of record: `the November 2 reference manuscript` (SP), line 3060 and lines
2819-2836 (Volterra construction), 3052-3058 (adjoint localized interaction), 270-288 (BUC train).

The proof is the conditional assembly `adjointWeakExistsBUC_of` (`Sub/T21_2_7/AdjWeakOf.lean`)
applied to the leaves: the train bounds `ladTrainBddAll`, the heat existence `adjHeatExists`,
the coefficient `adjCoeffExists_of` (transport and localized parts), the pairing `adjPairing`,
the Volterra weak form `volterraWeakForm` and the terminal membership `adjTerminalMem`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **The weak reverse-time adjoint for the BUC train** (`PartIII-a:T21/2/7/1`, SP 3060,
2819-2836, 3052-3058): the conditional assembly applied to the proved leaves. -/
theorem adjointWeakExistsBUC (m : ℝ) (hm : 8 < m) (hW : TrainWeightedJetPoly) :
    AdjointWeakExistsBUC m :=
  adjointWeakExistsBUC_of m (ladTrainBddAll m hW) (adjHeatExists m hm)
    (adjCoeffExists_of m (adjTransportCoeff m) (adjLocalizedCoeff m hm) adjPairing)
    adjPairing volterraWeakForm (adjTerminalMem m (by linarith))

end UnforcedLeray.Short.IIIa
