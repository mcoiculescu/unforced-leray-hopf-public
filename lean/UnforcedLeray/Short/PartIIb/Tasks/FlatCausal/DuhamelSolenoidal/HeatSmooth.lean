import UnforcedLeray.Short.PartIIb.Sub.T12_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.FlatHeatContraction

/-!
# Part II-b, leaf `PartII-b:T12/6/9` (`DsolHeatSmooth`): smoothness of the planar heat flow of a test

Source of record: `the November 2 reference manuscript`, line 1924 (inside the
causal formula of lines 1920-1930). The statement is `DsolHeatSmooth` of `Sub/T12_6.lean`: for
`θ > 0` and `φ ∈ C_c^∞(ℝ²)`, `K_θ * φ` is `C^∞` and `D(K_θ * φ)(y) e = (K_θ * D_eφ)(y)`.

Proof outline.
* The flat heat kernel is integrable (`flatHeat_kernel_eq` identifies it with the unit-mass kernel
  of B0284) and even, so `dsolHeatConv θ φ` equals the Mathlib convolution
  `flatHeatKernel θ ⋆[lsmul] φ` (substitution `w ↦ -w`).
* Smoothness: `HasCompactSupport.contDiff_convolution_right`.
* Derivative: `HasCompactSupport.hasFDerivAt_convolution_right` gives the derivative as the
  CLM-valued convolution with `fderiv φ`, and `convolution_precompR_apply` evaluates it in the
  direction `e`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The flat heat kernel is even. -/
theorem dsolHK_even (θ : ℝ) (w : ℝ × ℝ) : flatHeatKernel θ (-w) = flatHeatKernel θ w := by
  unfold flatHeatKernel
  simp only [Prod.fst_neg, Prod.snd_neg, neg_sq]

/-- The flat heat kernel is integrable for `θ > 0` (unit mass, by `flatHeat_kernel_eq`). -/
theorem dsolHK_integrable {θ : ℝ} (hθ : 0 < θ) : Integrable (flatHeatKernel θ) := by
  have hk : flatHeatKernel θ = UnforcedLeray.B0284.heatKernel2 θ :=
    funext (flatHeat_kernel_eq hθ)
  rw [hk]
  refine Integrable.of_integral_ne_zero ?_
  rw [UnforcedLeray.B0284.integral_heatKernel2 hθ]
  exact one_ne_zero

/-- The heat convolution `dsolHeatConv θ φ` is the Mathlib convolution of the flat heat kernel
with `φ` (for every `φ`), via the substitution `w ↦ -w` and evenness of the kernel. -/
theorem dsolHeatConv_eq_convolution (θ : ℝ) (φ : ℝ × ℝ → ℝ) :
    dsolHeatConv θ φ =
      convolution (flatHeatKernel θ) φ (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  funext y
  rw [convolution_def]
  unfold dsolHeatConv
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have h := integral_neg_eq_self (fun w : ℝ × ℝ => flatHeatKernel θ w * φ (y + w)) volume
  simp only [dsolHK_even, ← sub_eq_add_neg] at h
  exact h.symm

/-- **Leaf `PartII-b:T12/6/9`** (smoothness of the heat flow of a test and the derivative
formula). For `θ > 0` and `φ ∈ C_c^∞(ℝ²)`, `K_θ * φ` is `C^∞` and `D(K_θ * φ)(y) e =
(K_θ * Dφ(·) e)(y)`. -/
theorem dsolHeatSmooth : DsolHeatSmooth := by
  intro θ φ hθ hφ hφc
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hKloc : LocallyIntegrable (flatHeatKernel θ) volume :=
    (dsolHK_integrable hθ).locallyIntegrable
  refine ⟨?_, fun y e => ?_⟩
  · rw [dsolHeatConv_eq_convolution θ φ]
    exact hφc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hKloc hφ
  · have hfd := hφc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hKloc hφ1 y
    rw [dsolHeatConv_eq_convolution θ φ, hfd.fderiv,
      dsolHeatConv_eq_convolution θ (fun z => fderiv ℝ φ z e)]
    exact convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hKloc (hφc.fderiv ℝ)
      (hφ1.continuous_fderiv one_ne_zero) y e

end UnforcedLeray.Short.IIb
