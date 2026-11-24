import UnforcedLeray.Analysis.Pressure.ConvolutionIdentity
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# The Newton potential of a compact smooth test (INF01 level L0, target T2)

Blueprint: INF01 (scoping note `INF01-CZ.md` §5, target T2); decision D5 of
`scoping/README.md` §3. Manuscript: the convention `R_j = ∂_j(-Δ)^{-1/2}` and
`p = Σ R_iR_k(u_iu_k)` (`paper/main.tex` lines 107–111), used through
`R_iR_k = ∂_i∂_k(-Δ)^{-1}` and `(-Δ)^{-1} f = N ∗ f`.

For a compact smooth scalar test `f`, `newtonConv f = N ∗ f` with the compiled
normalized Newton potential `N(x) = 1/(4π|x|)`
(`PressureAnalysis.newtonPotential`). We prove that it is smooth, that coordinate
derivatives commute with it, that `Δ(N ∗ f) = -f`, and that `N ∗ ∂ᵢf` is the
pairing of `f` with the compiled Newton-gradient kernel `∂ᵢN`.
The far-field decay `|∫ ∂ᵢN(x - y) f(x) dx| ≤ π⁻¹ |y|⁻² ‖f‖₁` is also proved here.
No Fourier transform and no Calderón–Zygmund estimate is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal Topology

namespace UnforcedLeray.RieszLp

open PressureAnalysis

/-- The Newton potential `(N ∗ f)(x) = ∫ N(x - y) f(y) dy`, `N(z) = 1/(4π|z|)`
(INF01 T2, `newtonConv`; `paper/main.tex` lines 107–111 via `(-Δ)^{-1} = N ∗`). -/
def newtonConv (f : Space → ℝ) (x : Space) : ℝ :=
  ∫ y, newtonPotential (x - y) * f y

/-- The pairing `y ↦ ∫ ∂ᵢN(x - y) f(x) dx` of `f` with the translated Newton
gradient kernel. For a test `f` it equals `-(N ∗ ∂ᵢf)(y)` (`newtonConv_partial`). -/
def newtonPair (i : Fin 3) (f : Space → ℝ) (y : Space) : ℝ :=
  ∫ x, newtonGradientKernel i (x - y) * f x

theorem newtonPotential_neg (x : Space) : newtonPotential (-x) = newtonPotential x := by
  simp [newtonPotential]

/-- `newtonConv` is the Mathlib convolution of the Newton potential with `f`. -/
theorem newtonConv_eq_convolution (f : Space → ℝ) :
    newtonConv f = convolution newtonPotential f (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  funext x
  rw [convolution_def, newtonConv,
    ← integral_sub_left_eq_self (fun y => newtonPotential (x - y) * f y) volume x]
  simp [sub_sub_cancel]

/-- The integrand of `newtonConv f x` is integrable for continuous compactly supported `f`. -/
theorem newtonConv_integrable {f : Space → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    (x : Space) : Integrable (fun y => newtonPotential (x - y) * f y) volume := by
  have h := (hc.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ)
    newtonPotential_locallyIntegrable hf x).integrable
  have h2 := h.comp_sub_left x
  refine h2.congr (Eventually.of_forall fun y => ?_)
  simp [sub_sub_cancel]

/-- `N ∗ f` is smooth for every compact smooth test `f` (INF01 T2, `newtonConv_contDiff`). -/
theorem newtonConv_contDiff {f : Space → ℝ} (hf : IsSpatialTest f) :
    ContDiff ℝ ∞ (newtonConv f) := by
  rw [newtonConv_eq_convolution]
  exact hf.compact.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    newtonPotential_locallyIntegrable hf.smooth

/-- Coordinate derivatives commute with the Newton potential on tests. -/
theorem spatialTestDerivative_newtonConv {f : Space → ℝ} (hf : IsSpatialTest f) (i : Fin 3) :
    spatialTestDerivative i (newtonConv f) = newtonConv (spatialTestDerivative i f) := by
  funext x
  have h := hf.compact.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    newtonPotential_locallyIntegrable (hf.smooth.of_le (by simp)) x
  change fderiv ℝ (newtonConv f) x (coordinateVector i) = newtonConv (spatialTestDerivative i f) x
  rw [newtonConv_eq_convolution f, h.fderiv, newtonConv_eq_convolution (spatialTestDerivative i f)]
  exact convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ)
    newtonPotential_locallyIntegrable (hf.compact.fderiv ℝ)
    (hf.smooth.continuous_fderiv (by simp)) x (coordinateVector i)

/-- Additivity of the Newton potential on tests. -/
theorem newtonConv_add {f g : Space → ℝ} (hf : IsSpatialTest f) (hg : IsSpatialTest g) :
    newtonConv (fun x => f x + g x) = fun x => newtonConv f x + newtonConv g x := by
  funext x
  simp only [newtonConv, mul_add]
  exact integral_add (newtonConv_integrable hf.continuous hf.compact x)
    (newtonConv_integrable hg.continuous hg.compact x)

/-- Finite additivity of the Newton potential on tests. -/
theorem newtonConv_sum {ι : Type*} (s : Finset ι) {f : ι → Space → ℝ}
    (hf : ∀ j, IsSpatialTest (f j)) :
    newtonConv (fun x => ∑ j ∈ s, f j x) = fun x => ∑ j ∈ s, newtonConv (f j) x := by
  funext x
  simp only [newtonConv, Finset.mul_sum]
  exact integral_finsetSum s (fun j _ => newtonConv_integrable (hf j).continuous (hf j).compact x)

/-- `-Δ(N ∗ f) = f` pointwise for a compact smooth test, through the compiled
fundamental-solution identity `newtonPotential_laplacian_test`. -/
theorem newtonConv_laplacian_test {f : Space → ℝ} (hf : IsSpatialTest f) (x : Space) :
    newtonConv (Heat.laplacian f) x = -f x := by
  have hΔ := scalarTest_laplacian hf
  have ht := Leray.isSpatialTest_translate x hf
  calc newtonConv (Heat.laplacian f) x
      = ∫ z, newtonPotential (x - (z + x)) * Heat.laplacian f (z + x) :=
        (integral_add_right_eq_self
          (fun y => newtonPotential (x - y) * Heat.laplacian f y) x).symm
    _ = ∫ z, newtonPotential z * Heat.laplacian (fun y => f (y + x)) z := by
        apply integral_congr_ae
        refine Eventually.of_forall fun z => ?_
        simp only [sub_add_cancel_right, newtonPotential_neg, scalar_laplacian_translate]
    _ = -f (0 + x) := newtonPotential_laplacian_test ht
    _ = -f x := by rw [zero_add]

/-- `Δ(N ∗ f) = -f` for every compact smooth test (INF01 T2, `laplacian_newtonConv`). -/
theorem laplacian_newtonConv {f : Space → ℝ} (hf : IsSpatialTest f) :
    Heat.laplacian (newtonConv f) = fun x => -f x := by
  funext x
  have he : Heat.laplacian (newtonConv f) x =
      ∑ i : Fin 3, spatialTestDerivative i (spatialTestDerivative i (newtonConv f)) x := rfl
  have hΔ : Heat.laplacian f =
      fun y => ∑ i : Fin 3, spatialTestDerivative i (spatialTestDerivative i f) y := rfl
  rw [he, ← newtonConv_laplacian_test hf x, hΔ,
    newtonConv_sum Finset.univ (fun i => (hf.derivative i).derivative i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [spatialTestDerivative_newtonConv hf i,
    spatialTestDerivative_newtonConv (hf.derivative i) i]

/-- `(N ∗ ∂ᵢf)(y) = -∫ ∂ᵢN(x - y) f(x) dx` for a compact smooth test `f`. -/
theorem newtonConv_partial {f : Space → ℝ} (hf : IsSpatialTest f) (i : Fin 3) (y : Space) :
    newtonConv (spatialTestDerivative i f) y = -newtonPair i f y := by
  have ht := Leray.isSpatialTest_translate y hf
  have hK := newtonGradientKernel_test i ht
  have h1 : newtonConv (spatialTestDerivative i f) y =
      ∫ z, newtonPotential z * spatialTestDerivative i (fun w => f (w + y)) z := by
    calc newtonConv (spatialTestDerivative i f) y
        = ∫ z, newtonPotential (y - (z + y)) * spatialTestDerivative i f (z + y) :=
          (integral_add_right_eq_self
            (fun x => newtonPotential (y - x) * spatialTestDerivative i f x) y).symm
      _ = _ := by
          apply integral_congr_ae
          refine Eventually.of_forall fun z => ?_
          simp only [sub_add_cancel_right, newtonPotential_neg,
            Leray.spatialTestDerivative_translate]
  have h2 : newtonPair i f y = ∫ z, newtonGradientKernel i z * f (z + y) := by
    calc newtonPair i f y
        = ∫ z, newtonGradientKernel i ((z + y) - y) * f (z + y) :=
          (integral_add_right_eq_self (fun x => newtonGradientKernel i (x - y) * f x) y).symm
      _ = _ := by simp only [add_sub_cancel_right]
  rw [h1, h2, hK, neg_neg]

/-- Far-field bound for the kernel pairing: if `f` vanishes outside the ball of radius `ρ`
and `2ρ ≤ |y|`, `y ≠ 0`, then `|∫ ∂ᵢN(x - y) f(x) dx| ≤ π⁻¹ |y|⁻² ∫ |f|`. -/
theorem abs_newtonPair_le_of_far (i : Fin 3) {f : Space → ℝ} (hf : Integrable f volume)
    {ρ : ℝ} (hsupp : ∀ x, ρ < ‖x‖ → f x = 0) {y : Space} (hy : 2 * ρ ≤ ‖y‖) (hy0 : y ≠ 0) :
    |newtonPair i f y| ≤ Real.pi⁻¹ * (‖y‖ ^ 2)⁻¹ * ∫ x, |f x| := by
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hpt : ∀ x, ‖newtonGradientKernel i (x - y) * f x‖ ≤
      Real.pi⁻¹ * (‖y‖ ^ 2)⁻¹ * |f x| := by
    intro x
    by_cases hx : ρ < ‖x‖
    · rw [hsupp x hx]; simp
    · push Not at hx
      rw [norm_mul, Real.norm_eq_abs (f x)]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      have hd : ‖y‖ / 2 ≤ ‖x - y‖ := by
        have := norm_sub_norm_le y x
        rw [norm_sub_rev] at this
        linarith
      have hd0 : 0 < ‖y‖ / 2 := by positivity
      have hk := norm_newtonGradientKernel_le i (x - y)
      have hxy : 0 < ‖x - y‖ := lt_of_lt_of_le hd0 hd
      rw [Real.rpow_neg (norm_nonneg _), Real.rpow_two] at hk
      refine hk.trans ?_
      have hsq : (‖y‖ / 2) ^ 2 ≤ ‖x - y‖ ^ 2 := pow_le_pow_left₀ hd0.le hd 2
      have hinv : (‖x - y‖ ^ 2)⁻¹ ≤ ((‖y‖ / 2) ^ 2)⁻¹ :=
        inv_anti₀ (by positivity) hsq
      calc (4 * Real.pi)⁻¹ * (‖x - y‖ ^ 2)⁻¹ ≤ (4 * Real.pi)⁻¹ * ((‖y‖ / 2) ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = Real.pi⁻¹ * (‖y‖ ^ 2)⁻¹ := by
            field_simp
            ring
  have hint : Integrable (fun x => Real.pi⁻¹ * (‖y‖ ^ 2)⁻¹ * |f x|) volume :=
    hf.abs.const_mul _
  have h := norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
  rw [integral_const_mul] at h
  rw [← Real.norm_eq_abs]
  exact h

end UnforcedLeray.RieszLp
