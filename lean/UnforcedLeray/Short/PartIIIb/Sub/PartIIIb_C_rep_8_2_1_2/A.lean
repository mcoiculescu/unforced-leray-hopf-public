import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2

/-!
# `AxisExtPd`: the axis extension has the same derivatives off the axis (`PartIII-b:C/rep/8/2/1/2`, (A))

Source `the November 2 reference manuscript`,
line 5201 (smooth Cartesian extension through the axis). The axis is closed, so off the axis
`axisExt f` agrees with `f` on a neighbourhood, hence has the same first and second derivatives.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Axi

theorem axisExtPd : AxisExtPd := by
  intro f y hy
  have hEq : UnforcedLeray.Cons.C03.Concrete.axisExt f =ᶠ[𝓝 y] f := by
    filter_upwards [isOpen_compl_axis.mem_nhds hy] with z hz
    exact UnforcedLeray.Cons.C03.Concrete.axisExt_of_not_mem hz
  have hG : ∀ l : Fin 3, (fun z => physPd (UnforcedLeray.Cons.C03.Concrete.axisExt f) l z) =ᶠ[𝓝 y]
      (fun z => physPd f l z) := by
    intro l
    filter_upwards [hEq.fderiv (𝕜 := ℝ)] with z hz
    unfold physPd
    rw [hz]
  refine ⟨fun j => ?_, fun j l => ?_⟩
  · unfold physPd
    rw [hEq.fderiv_eq]
  · exact congrArg (fun g => g (coordinateVector j)) ((hG l).fderiv_eq (𝕜 := ℝ))

end UnforcedLeray.Short.PartIIIb.Concrete
