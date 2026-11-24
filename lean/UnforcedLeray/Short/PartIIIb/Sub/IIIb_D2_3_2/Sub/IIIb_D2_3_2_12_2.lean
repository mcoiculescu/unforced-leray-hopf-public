import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_1.Generic

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Source pairing continuity** (source 2683-2689, 4284-4286): the pairing with the physical
velocity of a body force `f ∈ SrcG c` is continuous for a phase test. The measure
`srcMeasure c = π • ageμ c (-3/2)` dominates `ageμ c (-3/2)` up to the constant `(π)⁻¹`. -/
theorem srcPairCont_proved (c ε : ℝ) : SrcPairCont c ε := by
  intro hc hε H hH
  have hπ0 : ENNReal.ofReal Real.pi ≠ 0 := (ENNReal.ofReal_pos.2 Real.pi_pos).ne'
  have hπt : ENNReal.ofReal Real.pi ≠ ⊤ := ENNReal.ofReal_ne_top
  have hle : ageμ c (-3 / 2) ≤ (ENNReal.ofReal Real.pi)⁻¹ • srcMeasure c := by
    refine le_of_eq ?_
    unfold srcMeasure
    rw [smul_smul, ENNReal.inv_mul_cancel hπ0 hπt, one_smul]
  exact pairCont_of_le hc hε (ENNReal.inv_ne_top.2 hπ0) (ENNReal.inv_ne_zero.2 hπt) hle H hH

end UnforcedLeray.Short.PartIIIb.Concrete
