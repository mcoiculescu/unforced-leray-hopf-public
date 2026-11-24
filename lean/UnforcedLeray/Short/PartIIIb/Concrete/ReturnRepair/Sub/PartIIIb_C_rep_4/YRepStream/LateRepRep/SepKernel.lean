import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.SepKernel.Props
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.SepKernel.FarKernel

/-!
# Organizer task `PartIII-b:C/rep/4/4/1/org/6/1`: `lateSepKernel`

Source `shorter-proof-2026-11-02.tex` 5318, 5323-5339, 5303-5308. The late-output kernel bound is
`lateSepKernel_of_farRepRepUng` (`SepKernel/Props.lean`) applied to `farRepRepUng`
(`SepKernel/FarKernel.lean`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem lateSepKernel (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : LateSepKernel Pl σ₀ mZ dm dp :=
  lateSepKernel_of_farRepRepUng Pl σ₀ mZ dm dp (farRepRepUng Pl σ₀ mZ dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete
