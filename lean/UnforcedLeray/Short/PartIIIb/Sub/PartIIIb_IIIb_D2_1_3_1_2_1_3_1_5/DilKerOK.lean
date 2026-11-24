import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5

/-!
# Leaf `DilKerOK`: dilations preserve smooth compact support

Source: `the November 2 reference manuscript` lines 1351-1362, 1470-1480.
Proves `dilKerOK : DilKerOK`. For `0 < s`, `z ↦ s⁻¹ • z` is a homeomorphism and a linear
smooth map, so `κ ∘ (s⁻¹ • ·)` is smooth with compact support when `κ` is; multiplying by a
constant preserves both properties.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem dilKerOK : DilKerOK := by
  intro κ s hκ hs
  have hc : s⁻¹ ≠ 0 := inv_ne_zero hs.ne'
  have hL : ContDiff ℝ ∞ (fun z : Space => s⁻¹ • z) := contDiff_const_smul _
  have hH : HasCompactSupport (fun z : Space => κ (s⁻¹ • z)) :=
    hκ.2.comp_homeomorph (Homeomorph.smulOfNeZero s⁻¹ hc)
  have hK : ContDiff ℝ ∞ (fun z : Space => κ (s⁻¹ • z)) := hκ.1.comp hL
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact contDiff_const.mul hK
  · exact HasCompactSupport.mul_left hH
  · exact contDiff_const.mul hK
  · exact HasCompactSupport.mul_left hH

end UnforcedLeray.Short.PartIIIb.Concrete
