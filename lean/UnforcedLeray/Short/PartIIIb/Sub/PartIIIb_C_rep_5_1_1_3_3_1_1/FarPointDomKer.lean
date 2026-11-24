import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_1_3.Tail
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds

/-!
# `PartIII-b:C/rep/5/1/1/3/3/1/1/1` (part): the order-four kernel bound `FarKerDeriv`

Source `the November 2 reference manuscript` 3604-3610: `|∂_k K_t(x)| ≤ C|x|^{-4}`
is the case `j = 0` of `IIIa.SepKernelBounds`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem farKerDeriv_exists : ∃ C : ℝ, FarKerDeriv C := by
  obtain ⟨C, hC⟩ := UnforcedLeray.Short.IIIa.sepKernelBounds 0
  refine ⟨C, fun t ht x hx i j k => ?_⟩
  have h1 : ‖fderiv ℝ (fun y => UnforcedLeray.Short.IIIa.heatLerayK t i j y) x‖
      ≤ C * ‖x‖ ^ (-4 : ℝ) := by
    have h := (hC x hx i j).1 t ht
    simpa [norm_iteratedFDeriv_one] using h
  have hv : ‖coordinateVector k‖ = 1 := by
    simp [coordinateVector]
  have hp : ‖x‖ ^ (-4 : ℝ) = (‖x‖ ^ 4)⁻¹ := by
    rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg (norm_nonneg x),
      Real.rpow_natCast]
  calc ‖fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK t i j x) x (coordinateVector k)‖
      ≤ ‖fderiv ℝ (fun y => UnforcedLeray.Short.IIIa.heatLerayK t i j y) x‖
          * ‖coordinateVector k‖ := (fderiv ℝ (fun y => UnforcedLeray.Short.IIIa.heatLerayK t i j y) x).le_opNorm _
    _ ≤ C * ‖x‖ ^ (-4 : ℝ) * 1 := by
        rw [hv, mul_one, mul_one]
        exact h1
    _ = C * (‖x‖ ^ 4)⁻¹ := by rw [mul_one, hp]

end UnforcedLeray.Short.PartIIIb.Concrete
