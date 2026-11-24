import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.WeightedHeatOperatorBound

/-!
# A nonnegative-age actual weighted heat family

This packages the positive-age weighted Gaussian map together with the actual zero-age identity.
The result acts on all `X_m`; preservation of the zero-circulation subspace is a separate
remaining bridge.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory
open scoped ENNReal
open UnforcedLeray.B0579

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- The actual first-coordinate Gaussian heat family on `X_m`, with identity at age zero.
Positive ages are restricted to the short strip for which the explicit moment bound is proved. -/
noncomputable def xColumnHeatS0CLM {c m : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c)
    (hm : 1 ≤ m) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    X c m →L[ℝ] X c m := by
  by_cases hθ : 0 < θ
  · exact xColumnHeatS0PositiveCLM hc hc1 hm hθ hθ1
  · exact ContinuousLinearMap.id ℝ (X c m)

@[simp] theorem xColumnHeatS0CLM_zero {c m : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c)
    (hm : 1 ≤ m) :
    xColumnHeatS0CLM hc hc1 hm (θ := 0) le_rfl (by norm_num) =
      ContinuousLinearMap.id ℝ (X c m) := by
  simp [xColumnHeatS0CLM]

theorem xColumnHeatS0CLM_apply_of_pos {c m θ : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (f : X c m) :
    xColumnHeatS0CLM hc hc1 hm (by linarith) hθ1 f =
      xColumnHeatS0Positive hc hm hθ hθ1 f := by
  simp [xColumnHeatS0CLM, hθ, xColumnHeatS0PositiveCLM_apply]

theorem xColumnHeatS0CLM_apply_zero {c m : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c)
    (hm : 1 ≤ m) (f : X c m) :
    xColumnHeatS0CLM hc hc1 hm (θ := 0) le_rfl (by norm_num) f = f := by
  simp [xColumnHeatS0CLM]

private theorem axialHeatMomentMass_nonneg {m : ℝ} (hm : 1 ≤ m) :
    0 ≤ 2 ^ (m / 2) * ∫ z : Plane, axialHeatMomentDensity 1 m z := by
  have hmoment : 0 ≤ ∫ z : Plane, axialHeatMomentDensity 1 m z := by
    apply integral_nonneg_of_ae
    filter_upwards with z
    unfold axialHeatMomentDensity
    exact mul_nonneg (B0284.heatKernel2_nonneg one_pos z) (by
      dsimp [axialWeight, axialBracket]
      positivity)
  exact mul_nonneg (by positivity) hmoment

/-- Uniform-on-the-short-strip operator norm bound for the actual weighted heat family.
The constant is explicit in `c,m`; no cylinder-uniform growth estimate is claimed. -/
theorem norm_xColumnHeatS0CLM_le {c m θ : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c)
    (hm : 1 ≤ m) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ‖xColumnHeatS0CLM hc hc1 hm hθ0 hθ1‖ ≤
      max 1 ((1 + c ^ 2 / 4) ^ (m / 2) *
        (2 ^ (m / 2) * ∫ z : Plane, axialHeatMomentDensity 1 m z)) := by
  let K : ℝ := (1 + c ^ 2 / 4) ^ (m / 2) *
    (2 ^ (m / 2) * ∫ z : Plane, axialHeatMomentDensity 1 m z)
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (by positivity) (axialHeatMomentMass_nonneg hm)
  by_cases hθ : 0 < θ
  · rw [show xColumnHeatS0CLM hc hc1 hm hθ0 hθ1 =
        xColumnHeatS0PositiveCLM hc hc1 hm hθ hθ1 by
          simp [xColumnHeatS0CLM, hθ]]
    have hMle := axialHeatKernel_lintegral_le hθ hθ1 (by linarith : 0 ≤ m)
    have hMtop : (∫⁻ w : Plane, axialHeatKernel m θ w) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hMle
    have hMass :
        (∫⁻ w : Plane, axialHeatKernel m θ w).toReal ≤
          2 ^ (m / 2) * ∫ z : Plane, axialHeatMomentDensity 1 m z := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hMle
      rw [ENNReal.toReal_ofReal (axialHeatMomentMass_nonneg hm)] at h
      exact h
    have hNorm := norm_xColumnHeatS0PositiveCLM_le hc hc1 hm hθ hθ1
    have hCc : 0 ≤ (1 + c ^ 2 / 4) ^ (m / 2) := by positivity
    calc
      ‖xColumnHeatS0PositiveCLM hc hc1 hm hθ hθ1‖ ≤
          (1 + c ^ 2 / 4) ^ (m / 2) *
            (∫⁻ w : Plane, axialHeatKernel m θ w).toReal := hNorm
      _ ≤ K := by
        dsimp [K]
        exact mul_le_mul_of_nonneg_left hMass hCc
      _ ≤ max 1 K := le_max_right _ _
  · have hzero : θ = 0 := by linarith
    subst θ
    rw [xColumnHeatS0CLM_zero hc hc1 hm]
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro f
    change ‖f‖ ≤ max 1 K * ‖f‖
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right (le_max_left 1 K) (norm_nonneg f))

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.xColumnHeatS0CLM
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.xColumnHeatS0CLM_zero
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.norm_xColumnHeatS0CLM_le
