import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_8_1

/-!
# `PartIII-b:C/ward/12/3/1/2/5/1/2/3`: `inletL0Transpose_of`

Source `the November 2 reference manuscript`
lines 4268, 2385-2387.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem inletL0Transpose_of (hReg : InletFieldRegular) : InletL0Transpose := by
  intro lam q hq dm dp hdm
  obtain ⟨ν₀, hν₀, H0⟩ := hReg lam q hq dm dp hdm
  refine ⟨ν₀, hν₀, fun p d hreg hν hm z g hg i ψ hψ => ?_⟩
  obtain ⟨_, _, hE⟩ := H0 p d hreg hν hm z g hg
  obtain ⟨hEs, hEp, _⟩ := hE i
  have h := ibpAdjoint_proved p.period p.ν 0 p.period_pos (p.Efun i) hEs hEp ψ hψ
  simpa using h

end UnforcedLeray.Short.PartIIIb.Concrete
