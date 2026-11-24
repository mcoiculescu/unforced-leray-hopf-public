import UnforcedLeray.Short.PartIIb.Sub.T12_7
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.HeatSymm.Leaf.DeqhsAbsInt

/-!
# Part II-b, helper for `PartII-b:T12/7/6/1` (`deqPairSplit`): integrability of `e^{θΔ}g_i · ψ`

For a `DeqSliceGood` slice `g`, `θ > 0` and a continuous compactly supported real `ψ`, the map
`z ↦ (e^{θΔ} g)_i(z) ψ(z)` is Lebesgue integrable. Proof: integrate out `w` in the absolutely
integrable product `deqhsAbsInt` (`Integrable.integral_prod_left`), and identify
`(e^{θΔ} g)_i(z) = ∫ K_θ(w) g_i(z - w) dw` for a.e. `z` (the coordinate identity of
`HeatSymm/Leaf/DeqhsIdent.lean`, repeated pointwise).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem deqFlatHeatMulInt {c r θ : ℝ} {g : ℝ × ℝ → CMerid} (hc : 0 < c) (hr : 1 < r)
    (hg : DeqSliceGood c r g) (hθ : 0 < θ) {ψ : ℝ × ℝ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (i : Fin 2) :
    Integrable (fun z : ℝ × ℝ => flatHeat θ g z i * (ψ z : ℂ)) := by
  obtain ⟨hn, hi⟩ := deqhsAbsInt c r g hc hr hg θ hθ ψ hψ hψc
  have h1 : Integrable (fun z : ℝ × ℝ =>
      (∫ w : ℝ × ℝ, (flatHeatKernel θ w : ℂ) * g (z - w) i) * (ψ z : ℂ)) := by
    refine (hi i).integral_prod_left.congr (Eventually.of_forall fun z => ?_)
    simp only [integral_mul_const]
  refine h1.congr ?_
  filter_upwards [hn.prod_right_ae] with z hz
  by_cases h0 : ψ z = 0
  · simp [h0]
  have habs : |ψ z| ≠ 0 := abs_ne_zero.2 h0
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

end UnforcedLeray.Short.IIb
