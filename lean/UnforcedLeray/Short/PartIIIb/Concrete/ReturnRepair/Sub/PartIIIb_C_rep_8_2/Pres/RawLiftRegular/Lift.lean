import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.RawLiftRegular
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.RawLiftRegular.Chart

/-!
# Smoothness of the flat lifted pressure off the axis (task `PartIII-b:C/rep/8/2/pres/6/2/5`)

Source `the November 2 reference manuscript`
lines 1217, 5272-5282.

`liftP L τ y = age L.ε⁻¹ y * L.train.p (chart L.ε⁻¹ τ y).1 (chart L.ε⁻¹ τ y).2`.
Off the axis the chart is `C^∞` into `Ici 0 ×ˢ univ` (`chart_contDiffOn_offAxis`, `age_pos`), the
train pressure is `C^∞` there (`IsTrain.smooth_p`), and `age` is `C^∞` off the axis.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff Classical

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **The flat lifted pressure is `C^∞` off the axis** (source 1217, 5272-5282). -/
theorem liftOffAxisSmooth_of (L : ReturnLevel) : LiftOffAxisSmooth L := by
  have hR : L.ε⁻¹ ≠ 0 := (inv_pos.2 L.ε_pos).ne'
  have hc : ContDiffOn ℝ ∞ (fun x : ℝ × Space => chart L.ε⁻¹ x.1 x.2)
      {x : ℝ × Space | x.2 ∉ axis} := chart_contDiffOn_offAxis L.ε⁻¹ hR
  have hsnd : ContDiffOn ℝ ∞ (fun x : ℝ × Space => x.2)
      {x : ℝ × Space | x.2 ∉ axis} := contDiff_snd.contDiffOn
  have hmaps : MapsTo (fun x : ℝ × Space => chart L.ε⁻¹ x.1 x.2)
      {x : ℝ × Space | x.2 ∉ axis} (Set.Ici 0 ×ˢ Set.univ) := by
    intro x hx
    refine ⟨?_, Set.mem_univ _⟩
    exact (age_pos hR hx).le
  have hpc : ContDiffOn ℝ ∞
      (fun x : ℝ × Space => L.train.p (chart L.ε⁻¹ x.1 x.2).1 (chart L.ε⁻¹ x.1 x.2).2)
      {x : ℝ × Space | x.2 ∉ axis} :=
    L.train.isTrain.smooth_p.comp hc hmaps
  have hage : ContDiffOn ℝ ∞ (fun x : ℝ × Space => age L.ε⁻¹ x.2)
      {x : ℝ × Space | x.2 ∉ axis} :=
    (offAxis_age_contDiffOn L.ε⁻¹).comp hsnd (fun x hx => hx)
  unfold LiftOffAxisSmooth liftP
  exact hage.mul hpc

end UnforcedLeray.Short.PartIIIb.Concrete
