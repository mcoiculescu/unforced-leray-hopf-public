import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellTest
import Mathlib.MeasureTheory.Function.Holder

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

/-- Hölder continuity of the actual complex vector pairing on a spacetime measure. -/
theorem eLpNorm_dotL_bilinear_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p q : ℝ≥0∞} [ENNReal.HolderTriple p q 1]
    {f : α → UnforcedLeray.PhaseSpace.CVec3}
    {g : α → UnforcedLeray.PhaseSpace.CVec3}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun x => UnforcedLeray.PhaseSpace.dotL (f x) (g x)) 1 μ ≤
      ‖UnforcedLeray.PhaseSpace.dotL‖₊ * (eLpNorm f p μ * eLpNorm g q μ) := by
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (μ := μ) (p := p) (q := q) (r := 1)
    hf hg (fun a b => UnforcedLeray.PhaseSpace.dotL a b)
    ‖UnforcedLeray.PhaseSpace.dotL‖₊
    (Eventually.of_forall fun x => UnforcedLeray.PhaseSpace.dotL.le_opNorm₂ _ _)
  simpa [mul_assoc] using h

/-- A dual-exponent pair has an integrable pointwise dot product. -/
theorem integrable_dotL_of_memLp_holder {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p q : ℝ≥0∞} [ENNReal.HolderTriple p q 1]
    {f : α → UnforcedLeray.PhaseSpace.CVec3}
    {g : α → UnforcedLeray.PhaseSpace.CVec3}
    (hf : MemLp f p μ) (hg : MemLp g q μ) :
    Integrable (fun x => UnforcedLeray.PhaseSpace.dotL (f x) (g x)) μ := by
  exact memLp_one_iff_integrable.mp
    (UnforcedLeray.PhaseSpace.dotL.memLp_of_bilin 1 hf hg)

#print axioms eLpNorm_dotL_bilinear_le
#print axioms integrable_dotL_of_memLp_holder

end UnforcedLeray.Cons.C03.Concrete
