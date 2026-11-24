import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_2_4
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.FullOutLip.MajL2.Pointwise
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.FullOutLip.MajL2.KerDom
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.FullOutLip.MajL2.DilL2
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.FullOutLip.MajL2.DilMeas
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.FullOutLip.MajL2.DilAxisym
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.FullOutLip.MajL2.ChartL2
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.FullOutLip.MajL2.NsSymTv4
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.GAxFacts
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.AgeShift
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.PolarReduction
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartChange
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartChangeSE
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartChangeTQ
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartL2Source

/-!
# `fullMajL2` (`PartIII-b:C/near/masked/18/3/2/4`, source 3996-4011, 2683)

Assembly of `FullMajL2` from the seven analytic facts `fmPointwise`, `fmKerDom`, `fmDilL2`,
`fmDilMeasurable`, `fmDilAxisym`, `fmChartL2`, `fmNsSymTv4` and the axis/chart-source facts
`gAxFacts_holds` and `chartL2Source_of` (with `ageShift_holds`, `polarReduction_holds`,
`chartChange_of`, `chartChangeSE_holds`, `chartChangeTQ_holds`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

theorem fullMajL2 : UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.FullMajL2 :=
  fullMajL2_of fmPointwise fmKerDom fmDilL2 fmDilMeasurable fmDilAxisym fmChartL2 fmNsSymTv4
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.gAxFacts_holds
    (UnforcedLeray.Short.PartIIIb.NearInst.Masked.chartL2Source_of
      UnforcedLeray.Short.PartIIIb.NearInst.Masked.ageShift_holds
      UnforcedLeray.Short.PartIIIb.NearInst.Masked.polarReduction_holds
      (UnforcedLeray.Short.PartIIIb.NearInst.Masked.chartChange_of
        UnforcedLeray.Short.PartIIIb.NearInst.Masked.chartChangeSE_holds
        UnforcedLeray.Short.PartIIIb.NearInst.Masked.chartChangeTQ_holds)
      UnforcedLeray.Short.PartIIIb.NearInst.Masked.gAxFacts_holds)

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
