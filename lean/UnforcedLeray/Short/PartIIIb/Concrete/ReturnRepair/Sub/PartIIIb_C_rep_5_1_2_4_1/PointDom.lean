import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.SeqGlue
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Uniform
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.MuLe

/-!
# `wardYPointDomSeq`: pointwise domination along the sequence

Source `the November 2 reference manuscript` 5585-5589 (pointwise domination of the
far thin-source velocity), 5946 (window `μ_n(z)`). Composition of the uniform pointwise statement
`wardYPointDomUniform` with the window bound `muWinLeOne` through `wardYPointDomSeq_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem wardYPointDomSeq (D : SeqData) {dm dp : ℝ} : D.WardYPointDomSeq dm dp :=
  wardYPointDomSeq_of wardYPointDomUniform muWinLeOne D

end UnforcedLeray.Short.PartIIIb.Concrete
