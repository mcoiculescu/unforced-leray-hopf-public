import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.Props
import UnforcedLeray.Cons.L2.BackgroundConcrete.Operators

/-!
# `GELinFieldPer`: periodicity of the linear-term field in the phase (source 2525-2533)

Task `PartIII-b:C/ward/12/3/1/2/6/9`.  Pointwise, `rep v (τ+P) y = rep v τ y` and
`raw (τ+P) = raw τ` as functions of `y`, so all `rawD`, `rawDD` terms agree.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (rep rep_add_period)

theorem gELinFieldPer : GELinFieldPer := by
  intro p z g h j hp τ y
  have hraw : p.raw (τ + p.period) = p.raw τ := funext (hp.2 τ)
  simp only [GELinField, rawD, rawDD, hraw, rep_add_period]

end UnforcedLeray.Short.PartIIIb.Concrete
