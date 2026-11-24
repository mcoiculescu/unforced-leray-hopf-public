import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_2_1

/-!
# `PartIII-b:C/near/masked/14/2/3/2/1`: the axis `{y₀² + y₁² = 0}` is Lebesgue-null (`AxisNull`)

The axis is contained in the proper submodule `{y | y 0 = 0}` of `ℝ³`, which has Haar measure zero.
Source: `the November 2 reference manuscript` 3996-4011.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

theorem axisNull : UnforcedLeray.Short.PartIIIb.NearInst.Masked.AxisNull14 := by
  unfold UnforcedLeray.Short.PartIIIb.NearInst.Masked.AxisNull14
  have hsub : {y : EuclideanSpace ℝ (Fin 3) | y 0 ^ 2 + y 1 ^ 2 = 0} ⊆
      ((LinearMap.ker (EuclideanSpace.proj (0 : Fin 3) : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).toLinearMap
        : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) : Set (EuclideanSpace ℝ (Fin 3))) := by
    intro y hy
    have hy' : y 0 ^ 2 + y 1 ^ 2 = 0 := hy
    have h2 : y 0 ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg (y 1)]) (sq_nonneg _)
    have h0 : y 0 = 0 := pow_eq_zero_iff two_ne_zero |>.1 h2
    show (EuclideanSpace.proj (0 : Fin 3) : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) y = 0
    exact h0
  have hne : LinearMap.ker (EuclideanSpace.proj (0 : Fin 3) : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).toLinearMap
      ≠ (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) := by
    intro htop
    have hmem : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : EuclideanSpace ℝ (Fin 3)) ∈
        LinearMap.ker (EuclideanSpace.proj (0 : Fin 3) : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).toLinearMap := by
      rw [htop]
      exact Submodule.mem_top
    have h1 : (EuclideanSpace.proj (0 : Fin 3) : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
        (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) = 0 := hmem
    simp at h1
  exact measure_mono_null hsub (Measure.addHaar_submodule volume _ hne)

end UnforcedLeray.Short.PartIIIb.NearInst.Masked

end
