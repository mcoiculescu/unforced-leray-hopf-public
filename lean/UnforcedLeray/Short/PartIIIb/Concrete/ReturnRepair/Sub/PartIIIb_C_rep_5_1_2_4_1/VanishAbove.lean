import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.WardYoungPointwise

/-!
# `Y` vanishes above age `1/ν`

Source `the November 2 reference manuscript` 4161-4186 (`χ_y = χ_y' = 0` on `[1,∞)`).
For `1 < ν · age R y` the Ward stream cutoff `𝒞_y` vanishes near `y` at every time
(`wyp_at`), hence `X = 𝒞_y X₀` vanishes near `y`, and so does `Y = D_{μ+1} X` (`wyp_physDmu_zero`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem wardY_eq_zero_of_one_lt {ν μ R c : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy) (hR : 0 < R) (g : Chart → Ten3) (τ : ℝ) (y : Space) (hϱ : 0 < ϱ y) (hy : 1 < ν * age R y) : wardY ν μ R c χy g τ y = 0 := by
  unfold wardY
  exact wyp_physDmu_zero ν (μ + 1) (fun t => wyp_at ν μ R c hχy g hϱ hy t) τ

end UnforcedLeray.Short.PartIIIb.Concrete

end
