import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_2
import UnforcedLeray.Lib.Cylinder.IBP

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

/-- Translation by `(c, 0)` in the coordinate form `(x.1 + c, x.2)` used by `B0579.IsCylTest`. -/
theorem testBridge_add_cPeriod (c : ℝ) (x : ℝ × ℝ) :
    x + ((c, 0) : ℝ × ℝ) = (x.1 + c, x.2) := by
  ext <;> simp

/-- **Test-class bridge** (`PartIII-a:T18/2/4/2/9`; `UnforcedLeray.Short.IIIa.TestBridge`). -/
theorem testBridge : UnforcedLeray.Short.IIIa.TestBridge := by
  intro c φ
  refine ⟨⟨fun h => ⟨h.smooth, fun x => ?_, h.band⟩, fun h => ⟨h.smooth, fun x => ?_, h.bounded⟩⟩,
    fun h x => ⟨?_, ?_⟩⟩
  · have e := h.periodic x
    rw [← testBridge_add_cPeriod] at e
    exact e
  · have e := h.periodic x
    rw [testBridge_add_cPeriod] at e
    exact e
  · have hd : Differentiable ℝ φ := h.differentiable
    show fderiv ℝ φ x (1, 0) = UnforcedLeray.Cyl.partialQ φ x
    exact (UnforcedLeray.Cyl.partialQ_eq_fderiv hd x).symm
  · have hd : Differentiable ℝ φ := h.differentiable
    show fderiv ℝ φ x (0, 1) = UnforcedLeray.Cyl.partialEta φ x
    exact (UnforcedLeray.Cyl.partialEta_eq_fderiv hd x).symm

end UnforcedLeray.Short.IIIa
