import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_srcL_6_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1_3.Helpers

/-!
# Smoothness of the Newton leaves on the region (task `PartIII-b:C/srcL/6/1/1/1`)

Source of record: `the November 2 reference manuscript` lines 4776-4791, 4917-4937.
Leaf 1 `NewtonFamSmooth`: for `t ∈ (0,1]`, `newtonFam i t` is `C^∞` on the region
`U = {5ν/6 < x₀²+x₁²}`. It equals `t^{2μ+2}` times the parametric integral
`∫ famF t a da`, which is `C^∞` on `U` by `UnforcedLeray.L09.contDiffOn_integral`, using the
family facts of `PartIII-b_C_srcL_6_1_1_3/Helpers.lean` (smoothness of each `famF t a`,
measurability in `a`, local domination).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem newtonFamSmooth : NewtonFamSmooth := by
  intro c ν μ χo M hc hν hμ hχ hM i t ht
  show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun y : Vec3 => t ^ (2 * μ + 2) *
      ∫ a : ℝ × ℝ, NewtonFam.famF c ν χo M t i a y ∂(volume : Measure (ℝ × ℝ)))
    {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2}
  exact contDiffOn_const.mul (NewtonFam.famF_integral_contDiffOn c ν χo M hc hν hχ hM t ht i)

end UnforcedLeray.Short.PartIIIb.Concrete
