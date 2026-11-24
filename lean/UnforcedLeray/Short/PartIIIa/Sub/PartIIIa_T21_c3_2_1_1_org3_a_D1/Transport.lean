import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_a_D1.Profile
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1
import UnforcedLeray.Short.PartI.Tasks.TransportGroupHjM.Zero

/-!
# Helper for `PartIII-a:T21/c3/2/1/1/org/3/a/1/1`: the radial Euler transport of a real test

Source: SP 841-852 (`T(t)f(r,ϑ) = f(r, ϑ - Ω(r)t)`), SP 2962-2964.

`Planar.transportGroupW m z Wφ` is represented by `y ↦ φ(flowP z y)` (`transportGroupW_ae`),
from `PartI.TransportGroupHjMZero.coeFn_transportGroupW_flow` and the coordinate form
`cToPlane (flowMap z w) = flowP z (cToPlane w)` (`cToPlane_flowMap`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory

namespace UnforcedLeray.Short.IIIa.RelFreeTestSub.D1Aux

open UnforcedLeray.Short.PartI.TransportGroupHjMZero

theorem omega_eq_omg (w : ℂ) : UnforcedLeray.B0009.Omega w = omg (cToPlane w) := by
  simp only [UnforcedLeray.B0009.Omega, UnforcedLeray.GaussianVortex.radialOmega, omg, cToPlane]
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring_nf

theorem cToPlane_flowMap (z : ℝ) (w : ℂ) : cToPlane (flowMap z w) = flowP z (cToPlane w) := by
  simp only [flowMap, flowP, rotP, cToPlane, omega_eq_omg]
  refine Prod.ext ?_ ?_
  · simp only [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  · simp only [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring

/-- The radial Euler transport of a real test represented by `φ ∘ cToPlane`. -/
theorem transportGroupW_ae {m : ℝ} (z : ℝ) {φ : ℝ × ℝ → ℝ} {Wφ : Planar.L2w m}
    (hWφ : ⇑Wφ =ᵐ[volume] fun w => ((φ (cToPlane w) : ℝ) : ℂ)) :
    ⇑(Planar.transportGroupW m z Wφ) =ᵐ[volume] fun w => ((φ (flowP z (cToPlane w)) : ℝ) : ℂ) := by
  have h1 := coeFn_transportGroupW_flow m z Wφ
  have h2 : (⇑Wφ ∘ flowMap z) =ᵐ[Planar.wMeasure m]
      ((fun w => ((φ (cToPlane w) : ℝ) : ℂ)) ∘ flowMap z) :=
    (measurePreserving_flowMap m z).quasiMeasurePreserving.ae_eq_comp
      ((Planar.wMeasure_ac m).ae_le hWφ)
  have h3 := (Planar.volume_ac m).ae_le h2
  filter_upwards [h1, h3] with w hw1 hw3
  rw [hw1]
  simp only [Function.comp_apply] at hw3
  rw [hw3, cToPlane_flowMap]

end UnforcedLeray.Short.IIIa.RelFreeTestSub.D1Aux
