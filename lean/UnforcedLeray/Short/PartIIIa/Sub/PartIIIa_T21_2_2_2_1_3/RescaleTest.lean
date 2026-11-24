import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1_3
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1_3.Dil

/-!
# `PartIII-a:T21/2/2/2/1/3` leaf `RescaleTest` (SP 3052-3058)

A test `ψ` of the cell `c/√a` gives the test `x ↦ ψ(x/√a)` of the cell `c`
(`Dil.isCylTest_div`).
-/

set_option autoImplicit false

noncomputable section

theorem rescaleTest : UnforcedLeray.Short.IIIa.E0.RescaleTest := by
  intro c a hc ha ψ hψ
  exact UnforcedLeray.Short.IIIa.E0.RsDil.isCylTest_div (Real.sqrt_pos.mpr ha) hψ
