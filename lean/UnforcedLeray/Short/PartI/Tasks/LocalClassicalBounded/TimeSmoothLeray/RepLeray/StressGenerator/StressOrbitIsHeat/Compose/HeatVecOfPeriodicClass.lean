import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_1_1_6_Bridges

/-!
# Bridge 3c: vector heat of a periodic class is the class of the heated periodic field

Source: `the November 2 reference manuscript`,
lines 261-288. The `L²` class `K` equals `toVec ∘ T` a.e. on the normalized cell, so
`toVecL.symm ∘ K` is the plane class of `T` and lies in `L²`. Then `heatVecL2CLM_apply` reduces the
vector heat to the plane heat, `NeedHeatPeriodicL2` (N4) identifies that with the class of
`heat θ T`, and `toVecL` maps it back to `toVec ∘ heat θ T`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.HeatCylinder

theorem heatVecOfPeriodicClass : HeatVecOfPeriodicClass := by
  intro n4 c hc θ hθ T hper hmeas K hK hm
  have hKmem : MemLp (K : Plane → Vec) 2 (UnforcedLeray.B0284.cellMeasure c) := Lp.memLp K
  have hTmem : MemLp T 2 (UnforcedLeray.B0284.cellMeasure c) := by
    have h1 : MemLp (fun z => (Train.toVecL.symm : Vec →L[ℝ] Plane) ((K : Plane → Vec) z)) 2
        (UnforcedLeray.B0284.cellMeasure c) :=
      (Train.toVecL.symm : Vec →L[ℝ] Plane).comp_memLp' hKmem
    refine (memLp_congr_ae ?_).mp h1
    filter_upwards [hK] with z hz
    rw [hz]
    exact Train.toVecL.symm_apply_apply (T z)
  have hX : (Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL 2
      (UnforcedLeray.B0284.cellMeasure c) K = hTmem.toLp T := by
    apply Lp.ext
    filter_upwards [ContinuousLinearMap.coeFn_compLpL
      (Train.toVecL.symm : Vec →L[ℝ] Plane) K, hTmem.coeFn_toLp, hK] with z e1 e2 e3
    rw [e1, e2, e3]
    exact Train.toVecL.symm_apply_apply (T z)
  obtain ⟨hh, hEq⟩ := n4 hc θ T hper hmeas hTmem
  rw [heatVecL2CLM_apply, hX, hEq]
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (Train.toVecL : Plane →L[ℝ] Vec)
    (hh.toLp (UnforcedLeray.B0284.heat θ T)), hh.coeFn_toLp, hm.coeFn_toLp] with z e1 e2 e3
  rw [e1, e2, e3] <;> rfl

end UnforcedLeray.Short.PartI
