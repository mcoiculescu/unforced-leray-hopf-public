import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.FarMajorantPointwise
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.CartLiftNormOffAxis
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.AxisNull
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.FarKernL1
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.DilMajL2
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.DilMajFixedL
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.PeriodShift
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.DilMajMeasurable
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.DilMajAxisym
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.RotExists
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.GAxFacts
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartL2Majorant
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartL2Source
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.AgeShift
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.PolarReduction
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartChange
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartChangeSE
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartChangeTQ
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.NsSymNormLe
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PositiveKernel.FarSeparation
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PositiveKernel.TailL1
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PositiveKernel.DilationMargin
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PositiveKernel.YoungDilated
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PositiveKernel.PhaseMinkowski

/-!
# `farMajorantL2_holds` (source 3996-4005)

Source of record: `the November 2 reference manuscript`, lines 3996-4005.

Assembles `FarMajorantL2` from the proved sibling leaves: `farMajorantL2_of` applied to
`farMajorantPointwise_of`, `farKernL1_of`, `dilationMargin_holds`, `dilMajL2_of`,
`dilMajMeasurable_holds`, `dilMajAxisym_of`, `gAxFacts_holds`, `chartL2Majorant_of`,
`chartL2Source_of` and `nsSymNormLe_holds`. The argument structure follows the proof in
`Sub/Strip/Far.lean`, restricted to the imports this theorem needs.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

theorem farMajorantL2_holds : FarMajorantL2 :=
  farMajorantL2_of
    (farMajorantPointwise_of farSeparation_holds cartLiftNormOffAxis_holds axisNull_holds)
    (farKernL1_of tailL1_holds) dilationMargin_holds
    (dilMajL2_of (dilMajFixedL_of youngDilated_holds periodShift_holds dilMajMeasurable_holds)
      phaseMinkowski_holds dilMajMeasurable_holds)
    dilMajMeasurable_holds (dilMajAxisym_of rotExists_holds) gAxFacts_holds
    (chartL2Majorant_of ageShift_holds polarReduction_holds
      (chartChange_of chartChangeSE_holds chartChangeTQ_holds))
    (chartL2Source_of ageShift_holds polarReduction_holds
      (chartChange_of chartChangeSE_holds chartChangeTQ_holds) gAxFacts_holds)
    nsSymNormLe_holds

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
