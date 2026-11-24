import UnforcedLeray.Short.PartIIb.Sub.T12_7_3
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.FlatHeatContraction

/-!
# Part II-b, leaf `DeqhsIdent` (SP 1923-1927): coordinatewise convolution identity

Statement `DeqhsIdent` of `Sub/T12_7_3.lean`. From the integrability hypothesis, for a.e. `z`
with `ψ z ≠ 0` the map `w ↦ K_θ(w) g(z - w)` is Bochner integrable; the coordinate functional
`EuclideanSpace.proj i` (restricted to `ℝ`) commutes with the integral
(`ContinuousLinearMap.integral_comp_comm`). The remaining `z` have `ψ z = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem deqhsIdent : UnforcedLeray.Short.IIb.DeqhsIdent := by
  intro c r g hc hr hg θ hθ ψ hψ hψc hint i
  have hprod := hint.prod_right_ae
  refine integral_congr_ae ?_
  filter_upwards [hprod] with z hz
  by_cases h0 : ψ z = 0
  · simp [h0]
  have habs : |ψ z| ≠ 0 := abs_ne_zero.2 h0
  -- integrability of `w ↦ K_θ(w) ‖g(z - w)‖`
  have hz2 : Integrable (fun w : ℝ × ℝ => flatHeatKernel θ w * ‖g (z - w)‖) := by
    have h := hz.div_const (|ψ z|)
    convert h using 1
    funext w
    exact (mul_div_cancel_right₀ _ habs).symm
  have hKnn : ∀ w : ℝ × ℝ, 0 ≤ flatHeatKernel θ w := by
    intro w
    unfold flatHeatKernel
    have h1 : (0 : ℝ) ≤ (4 * Real.pi * θ)⁻¹ := by
      apply inv_nonneg.2
      exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hθ.le
    exact mul_nonneg h1 (Real.exp_pos _).le
  have hmeas : AEStronglyMeasurable (fun w : ℝ × ℝ => g (z - w)) volume :=
    hg.2.1.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure (ℝ × ℝ)) z)
  have hKc : Continuous (flatHeatKernel θ) := by
    unfold flatHeatKernel
    fun_prop
  have hvm : AEStronglyMeasurable (fun w : ℝ × ℝ => flatHeatKernel θ w • g (z - w)) volume :=
    (hKc.aestronglyMeasurable).smul hmeas
  have hv : Integrable (fun w : ℝ × ℝ => flatHeatKernel θ w • g (z - w)) volume := by
    refine Integrable.mono' hz2 hvm (Filter.Eventually.of_forall fun w => ?_)
    rw [norm_smul, Real.norm_of_nonneg (hKnn w)]
  -- the coordinate functional
  let L : CMerid →L[ℝ] ℂ := (EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).restrictScalars ℝ
  have hcomm := ContinuousLinearMap.integral_comp_comm L hv
  have hLapp : ∀ v : CMerid, L v = v i := fun v => rfl
  have hcoord : flatHeat θ g z i = ∫ w : ℝ × ℝ, (flatHeatKernel θ w : ℂ) * g (z - w) i := by
    unfold flatHeat
    have e1 : ∀ w : ℝ × ℝ, L (flatHeatKernel θ w • g (z - w))
        = (flatHeatKernel θ w : ℂ) * g (z - w) i := by
      intro w
      rw [hLapp]
      simp only [PiLp.smul_apply, Complex.real_smul]
    have e2 : (∫ w : ℝ × ℝ, flatHeatKernel θ w • g (z - w)) i
        = L (∫ w : ℝ × ℝ, flatHeatKernel θ w • g (z - w)) := (hLapp _).symm
    rw [e2, ← hcomm]
    exact integral_congr_ae (Filter.Eventually.of_forall e1)
  rw [hcoord]
