import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F5

/-!
# `PartII-b:F8/2` helper: the slice Sobolev statement

The cylinder Sobolev embedding `H¹(C_c) ⊂ L^{11/4}(C_c)` applied on almost every age slice of a
`c`-periodic profile with weak chart derivatives (SP 2311-2314: "`H²(C_c) ↪ W^{1,11/4}(C_c)`").
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.FlatKH2

open UnforcedLeray.Short.IIb

/-- **Slice Sobolev embedding** `H¹(C_c) ⊂ L^{11/4}(C_c)` on almost every age slice, with a constant
independent of the period `c ≥ 4`. -/
def SliceSobolev : Prop :=
  ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (c : ℝ), 4 ≤ c → ∀ (u uq uη : CProf),
    QPeriodic c u → StronglyMeasurable u → StronglyMeasurable uq → StronglyMeasurable uη →
    HasWeakVec vQ0 dZero u uq → HasWeakVec vEta dZero u uη →
    ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      eLpNorm (fun x => u (s, x)) (ENNReal.ofReal bgp) (volume.restrict (B0579.cell c)) ≤
        K * sliceH1Norm c u uq uη s

end UnforcedLeray.Short.IIb.FlatKH2
