import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1.Defs
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# `PartIII-a:T16/1/1/6` : `SepDiffWEqIntegral` (Fubini for `sep:resolvent`)

Source `the November 2 reference manuscript` lines 3611-3617.
Componentwise: `MeasureTheory.eval_integral` moves the component inside the Bochner integral,
`integral_prod` (Fubini on `(vol|_{(0,1)}) ⊗ vol`) gives the iterated integral, and
`integral_const_mul` pulls the constant `-2` and the factor `λ^{2μ+2}` out of the `z`-integral.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **`PartIII-a:T16/1/1/6`**: if `p ↦ sepDiffF ν μ T τ p y` is `sepDiffRho`-integrable then
`sepW` equals the product-measure integral of `sepDiffF`. -/
theorem sepDiffWEqIntegral : UnforcedLeray.Short.IIIa.SepDiffWEqIntegral := by
  intro ν μ T τ y h
  funext i
  rw [eval_integral (integrable_pi_iff.mp h) i]
  have h' : Integrable (fun p => sepDiffF ν μ T τ p y i) sepDiffRho :=
    (integrable_pi_iff.mp h) i
  unfold sepDiffRho at h' ⊢
  rw [integral_prod _ h']
  unfold sepW sepDiffF
  simp only [integral_const_mul]

end UnforcedLeray.Short.IIIa
