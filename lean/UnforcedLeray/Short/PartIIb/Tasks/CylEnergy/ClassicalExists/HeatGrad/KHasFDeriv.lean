import UnforcedLeray.Short.PartIIb.Sub.T22_1_6

/-!
# `PartII-b:T22/1/6/2`: the Fréchet derivative of `x ↦ K_a(x - y)`

Proves `HeatKHasFDeriv` (leaf K2 of `T22/1/6`, source `the November 2 reference manuscript`
lines 2103-2105). Chain rule on `K_a(z) = (4πa)⁻¹ exp(-(z₁² + z₂²)/(4a))`, then the derivative is
matched with `heatKdCLM a (x - y)` by extensionality.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric

namespace UnforcedLeray.Short.IIb.CylPDE

/-- **Leaf K2** (`PartII-b:T22/1/6/2`): `x ↦ K_a(x - y)` is Fréchet differentiable with derivative
`heatKdCLM a (x - y)`. -/
theorem heatKHasFDeriv : UnforcedLeray.Short.IIb.CylPDE.HeatKHasFDeriv := by
  intro a ha x y
  have hz : HasFDerivAt (fun x : Pl => x - y) (ContinuousLinearMap.id ℝ Pl) x :=
    hasFDerivAt_sub_const y
  have h1 := hz.fst
  have h2 := hz.snd
  have hS := (h1.mul h1).add (h2.mul h2)
  have hD := hS.const_mul (-(1 / (4 * a)))
  have hE := hD.exp
  have hF := hE.const_mul (1 / (4 * Real.pi * a))
  have hfun : (fun x : Pl => heatK a (x - y)) = (fun x : Pl =>
      1 / (4 * Real.pi * a) * Real.exp (-(1 / (4 * a)) * ((x - y).1 * (x - y).1 + (x - y).2 * (x - y).2))) := by
    funext x
    simp only [heatK, sq]
    congr 2
    ring
  rw [hfun]
  refine hF.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp [heatKdCLM, heatKd, heatK, Pi.mul_apply, smul_eq_mul]
  field_simp
  ring

end UnforcedLeray.Short.IIb.CylPDE
