import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7.NewtonVEquiv
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7.NewtonVDivFree
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7.AxiGenerator
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7.RayFluxDeriv
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7.StreamPsiDzInt
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7.RayFluxTendsto
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7.StreamCutDiv
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_2
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_srcL_6_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1_2
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1_3

/-!
# `PartIII-b:C/srcL/7`: solenoidality of `X^mt` (`XmtSolenoidal`)

Source of record: `the November 2 reference manuscript`, lines 4170-4190 and
4797-4800.  The composition `xmtSolenoidal_of` (in `Sub/PartIII-b_C_srcL_7.lean`) reduces
`XmtSolenoidal` to the leaves: the rotation equivariance and divergence freeness of the Newton
field, the outward stream primitive, the stream cutoff divergence, and the smoothness and
decay inputs from `PartIII-b:C/srcL/6`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem xmtSolenoidal : XmtSolenoidal :=
  xmtSolenoidal_of newtonVEquivariant newtonVDivFree
    (streamPsiDz_of axiGenerator rayFluxDeriv streamPsiDzInt rayFluxTendsto)
    streamCutDiv
    (newtonVSmooth_of newtonFamSmooth newtonFamMeas newtonFamDom)
    xsZDecay xsStreamPsi

end UnforcedLeray.Short.PartIIIb.Concrete
