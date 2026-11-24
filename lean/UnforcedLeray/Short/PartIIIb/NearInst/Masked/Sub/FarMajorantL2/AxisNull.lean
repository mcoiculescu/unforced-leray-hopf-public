import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.Defs

/-!
# The axis is Lebesgue-null (source 2666-2668)

`{z | hRad z = 0}` lies in the hyperplane `{z | z 0 = 0}`, a proper subspace of `ℝ³`, which has
Haar measure zero.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open UnforcedLeray.Short.PartIIIb.NearInst

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

theorem axisNull_holds : AxisNull := by
  unfold AxisNull
  have hsub : {z : UnforcedLeray.Space | hRad z = 0} ⊆
      ((LinearMap.ker (EuclideanSpace.proj (0 : Fin 3) : UnforcedLeray.Space →L[ℝ] ℝ).toLinearMap
        : Submodule ℝ UnforcedLeray.Space) : Set UnforcedLeray.Space) := by
    intro z hz
    have hz' : Real.sqrt (z 0 ^ 2 + z 1 ^ 2) = 0 := hz
    have hle : z 0 ^ 2 + z 1 ^ 2 ≤ 0 := Real.sqrt_eq_zero'.1 hz'
    have h2 : z 0 ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg (z 1)]) (sq_nonneg _)
    have h0 : z 0 = 0 := pow_eq_zero_iff two_ne_zero |>.1 h2
    show (EuclideanSpace.proj (0 : Fin 3) : UnforcedLeray.Space →L[ℝ] ℝ) z = 0
    exact h0
  have hne : LinearMap.ker (EuclideanSpace.proj (0 : Fin 3) : UnforcedLeray.Space →L[ℝ] ℝ).toLinearMap
      ≠ (⊤ : Submodule ℝ UnforcedLeray.Space) := by
    intro htop
    have hmem : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : UnforcedLeray.Space) ∈
        LinearMap.ker (EuclideanSpace.proj (0 : Fin 3) : UnforcedLeray.Space →L[ℝ] ℝ).toLinearMap := by
      rw [htop]
      exact Submodule.mem_top
    have h1 : (EuclideanSpace.proj (0 : Fin 3) : UnforcedLeray.Space →L[ℝ] ℝ)
        (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) = 0 := hmem
    simp at h1
  exact measure_mono_null hsub (Measure.addHaar_submodule volume _ hne)

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
