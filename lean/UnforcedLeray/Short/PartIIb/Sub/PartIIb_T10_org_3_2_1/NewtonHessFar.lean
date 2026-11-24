import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_3_2_1_defs

/-!
# `PartII-b:T10/org/3/2/1`: far-field bound of the Newton Hessian (`NewtonHessFar`)

Source of record `the November 2 reference manuscript`,
lines 119-120 (`R_iR_k = ∂_i∂_k(-Δ)^{-1}`, whose kernel off the support is `K_ik = ∂_i∂_k N`).

This is `rieszPairTest_decay` (`Lib/CZL2/TestOffSupport.lean`) with its constants made explicit:
for `f` vanishing outside `B̄_ρ` and `|y| ≥ 2ρ + 1`, `y` lies off the support, so
`∂ᵢ∂ₖ(N ∗ f)(y) = ∫ K_ik(y - x) f(x) dx` (`rieszPairTest_offSupport`), and `|y - x| ≥ |y|/2` on the
support gives `|K_ik(y - x)| ≤ π⁻¹ (|y|/2)⁻³ = 8 π⁻¹ |y|⁻³` (`abs_newtonHessianKernel_le_of_le`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIb.LTS

open UnforcedLeray.RieszLp UnforcedLeray.PressureAnalysis

/-- **`NewtonHessFar`**: `|∂ᵢ∂ₖ(N ∗ f)(y)| ≤ 8 π⁻¹ ‖f‖₁ |y|⁻³` for `|y| ≥ 2ρ + 1`. -/
theorem newtonHessFar_proof : NewtonHessFar := by
  intro f hf ρ hρ hsupp i k y hy
  have hfi : Integrable f volume := hf.integrable
  have hypos : 0 < ‖y‖ := by linarith
  have hsub : tsupport f ⊆ Metric.closedBall (0 : Space) ρ := by
    refine closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall
    by_contra h
    have h' : ρ < ‖x‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right, not_le] using h
    exact hx (hsupp x h')
  have hyt : y ∉ tsupport f := fun h => by
    have h1 := hsub h
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    linarith
  rw [rieszPairTest_offSupport hf i k hyt]
  have hpt : ∀ x, ‖newtonHessianKernel i k (y - x) * f x‖ ≤
      8 * Real.pi⁻¹ * (‖y‖ ^ 3)⁻¹ * |f x| := by
    intro x
    by_cases hx : f x = 0
    · simp [hx]
    · have hx' : ‖x‖ ≤ ρ := by
        by_contra h
        exact hx (hsupp x (lt_of_not_ge h))
      have hd : ‖y‖ / 2 ≤ ‖y - x‖ := by
        have h2 := norm_sub_norm_le y x
        linarith
      have hy0 : ‖y‖ ≠ 0 := hypos.ne'
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      refine (abs_newtonHessianKernel_le_of_le i k (by linarith) hd).trans (le_of_eq ?_)
      field_simp
      ring
  have h := norm_integral_le_of_norm_le (hfi.abs.const_mul (8 * Real.pi⁻¹ * (‖y‖ ^ 3)⁻¹))
    (Eventually.of_forall hpt)
  rw [integral_const_mul, Real.norm_eq_abs] at h
  exact h.trans (le_of_eq (by ring))

#print axioms newtonHessFar_proof

end UnforcedLeray.Short.IIb.LTS
