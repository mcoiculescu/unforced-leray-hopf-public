import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.StressMapWeakSol
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.CellPtChangeAll
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.TensorTestDense
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.TensorTestDivMem
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol1
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol2
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol3
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol5
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Sub.PartIIIb_C_near_pins_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4_2_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4_2_3_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_4
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.ChartDivPointwise
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.ChartStressIBP
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.VelPairAE
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.ChartDecomp
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterDict
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.PairFunctional
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.PairFunctionalDual
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.PairCLM
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.PairTransC
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.PairDilN
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.TransposeDeriv
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Scaling
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.PairHeatC

/-!
# `PartIII-b:C/rep/5/1/1/1/1`: `StressMapWeakSol` unconditionally

`stressMapWeakSol_of` (`Proofs/StressMapWeakSol.lean`, the four leaves of `PartIII-b:C/near/pins/5`)
needs `TepsWeakSol`, `ChartDivPair` and the masked tensor/cell hypotheses.  Each is supplied by a
closed theorem: `tepsWeakSol_of` from `pepsRealForm`, `pepsSolenoidal`, `pepsLerayInvisible`,
`repsVecEquation_of` and `repsVecSolenoidal`; `repsVecEquation_of` from `pairFunctional`,
`pairFunctionalDual` and `genAdjointPair_of` (`chartDecomp`, `outerDict`, `outerGen_of`);
`outerGen_of` from `outerPairCLM` and `outerTestDeriv_of` (`outerTransposePair_of`, `outerTransposeDeriv`,
`outerScaling`); `chartDivPair_of` from `chartDivPointwise`, `chartStressIBP`, `velPairAE`.
Source 3427-3440, 1645-1679.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb

theorem stressMapWeakSolC : NearInst.StressMapWeakSol := by
  have hOuterTD : NearInst.OuterTestDeriv :=
    NearInst.outerTestDeriv_of
      (NearInst.outerTransposePair_of NearInst.outerPairTransC NearInst.outerPairDilN
        NearInst.outerPairHeatC)
      NearInst.outerTransposeDeriv NearInst.outerScaling
  have hOuterGen : NearInst.OuterGen := NearInst.outerGen_of NearInst.outerPairCLM hOuterTD
  have hGenAdj : NearInst.GenAdjointPair :=
    NearInst.genAdjointPair_of NearInst.chartDecomp NearInst.outerDict hOuterGen
  have hRepsEq : NearInst.RepsVecEquation :=
    NearInst.repsVecEquation_of NearInst.pairFunctional NearInst.pairFunctionalDual hGenAdj
  have hTeps : NearInst.TepsWeakSol :=
    NearInst.tepsWeakSol_of NearInst.pepsRealForm NearInst.pepsSolenoidal
      NearInst.pepsLerayInvisible hRepsEq NearInst.repsVecSolenoidal
  have hChartDiv : NearInst.ChartDivPair :=
    NearInst.chartDivPair_of NearInst.chartDivPointwise NearInst.chartStressIBP NearInst.velPairAE
  exact NearInst.stressMapWeakSol_of hTeps hChartDiv NearInst.Masked.tensorTestDense
    NearInst.Masked.tensorTestDivMem
    (fun c hc => NearInst.Masked.cpcHT_eq c hc)
    (fun c hc => NearInst.Masked.cpcH_eq c hc)
    (fun c hc => NearInst.Masked.cpcInvH_eq c hc)

end UnforcedLeray.Short.PartIIIb
