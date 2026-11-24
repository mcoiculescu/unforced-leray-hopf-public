import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Dyn.Defs
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Defs

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **(D1) The tested derivative of the mollified adjoint, dual form** (`MollTestedAdj`). -/
theorem mollTestedAdj (m : ℝ) (hDual : UnforcedLeray.Short.IIIa.MollDual) :
    UnforcedLeray.Short.IIIa.MollTestedAdj m := by
  intro ν tr t s g φ a b χ hctx n ψ hψ u' hu' r hr
  obtain ⟨hν, -, -, -, -, hW, hATD, hta, hab, hbs, -⟩ := hctx
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  obtain ⟨hψ', -, hdual⟩ := hDual (ν ^ (-2 : ℝ)) m n hc ψ hψ
  have hrI : r ∈ Ioo t s := ⟨hta.trans_lt hr.1, hr.2.trans hbs⟩
  have hAT := hATD (mollR n ψ) u' hψ' hu'
  have hderiv := (hAT.2 r ⟨hrI.1.le, hrI.2.le⟩).hasDerivAt (Icc_mem_nhds hrI.1 hrI.2)
  refine hderiv.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hrI.1 hrI.2] with q hq
  exact (hdual (φ q) (hW.periodic q ⟨hq.1.le, hq.2⟩) (hW.memX q ⟨hq.1.le, hq.2.le⟩)).2

end UnforcedLeray.Short.IIIa
