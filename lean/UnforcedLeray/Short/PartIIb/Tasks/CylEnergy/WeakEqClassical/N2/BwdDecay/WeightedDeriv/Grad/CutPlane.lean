import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2_1

/-!


Source: `the November 2 reference manuscript` lines 2100-2105.
`cutζ η0 x = cutθ (x.2 - η0)` depends only on the second coordinate, so `∂_0 = 0`,
`∂_1 = cutθ'(x.2 - η0)` and `Δ = ∂_1²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

/-- Partials of a function of the second coordinate shifted by `η0`. -/
theorem cutPlane_shift (h : ℝ → ℝ) (η0 : ℝ) (hd : Differentiable ℝ h) (x : B0579.Plane) :
    B0579.pd 0 (fun y : B0579.Plane => h (y.2 - η0)) x = 0 ∧
    B0579.pd 1 (fun y : B0579.Plane => h (y.2 - η0)) x = deriv h (x.2 - η0) := by
  have hf : HasFDerivAt (fun y : B0579.Plane => y.2 - η0)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
    (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.snd ℝ ℝ ℝ)).sub_const η0
  have hh : HasDerivAt h (deriv h (x.2 - η0)) (x.2 - η0) := (hd (x.2 - η0)).hasDerivAt
  have hc : HasFDerivAt (fun y : B0579.Plane => h (y.2 - η0))
      (deriv h (x.2 - η0) • ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
    hh.comp_hasFDerivAt x hf
  unfold B0579.pd
  rw [hc.fderiv]
  simp [B0579.dir]

theorem cutPlane : UnforcedLeray.Short.IIb.CutPlane := by
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) cutθ :=
    (cutBump.contDiff).pow 2
  have hd : Differentiable ℝ cutθ := hsm.differentiable (by simp)
  have hd2 : Differentiable ℝ (deriv cutθ) :=
    (contDiff_infty_iff_deriv.1 hsm).2.differentiable (by simp)
  have hz : ∀ η0 : ℝ, cutζ η0 = fun y : B0579.Plane => cutθ (y.2 - η0) := fun η0 => rfl
  intro η0 x
  have h1 : B0579.pd 0 (cutζ η0) = fun _ : B0579.Plane => (0 : ℝ) := by
    funext y
    rw [hz η0]
    exact (cutPlane_shift cutθ η0 hd y).1
  have h2 : B0579.pd 1 (cutζ η0) = fun y : B0579.Plane => deriv cutθ (y.2 - η0) := by
    funext y
    rw [hz η0]
    exact (cutPlane_shift cutθ η0 hd y).2
  refine ⟨?_, ?_, ?_⟩
  · rw [hz η0]
    exact (cutPlane_shift cutθ η0 hd x).1
  · rw [hz η0]
    exact (cutPlane_shift cutθ η0 hd x).2
  · have h3 : B0579.pd 0 (fun _ : B0579.Plane => (0 : ℝ)) x = 0 := by
      simp [B0579.pd]
    unfold lapP
    rw [h1, h2, h3, (cutPlane_shift (deriv cutθ) η0 hd2 x).2, zero_add]

end UnforcedLeray.Short.IIb
