import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Shared
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellPeriodicLocInt

/-!
# `PartIII-a:T21/2/7/2/1/1/5/5`: smoothness and periodicity of the convolution, derivatives on the kernel

Source of record: `the November 2 reference manuscript` (SP), lines 3060-3061.
For a smooth compactly supported real kernel `K` and a `c`-periodic `f` in `X_{-m,c}` (locally
integrable, `CellPeriodicLocInt`), the convolution `cellConv K f = K ⋆ f` is smooth, `c`-periodic,
and every classical partial falls on the kernel.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The partial derivative of a smooth compactly supported real kernel is smooth and compactly
supported. -/
theorem pd_contDiff_cellConvDeriv {j : Fin 2} {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (B0579.pd j φ) :=
  ((contDiff_infty_iff_fderiv.1 hφ).2).clm_apply contDiff_const

theorem pd_hasCompactSupport_cellConvDeriv {j : Fin 2} {φ : ℝ × ℝ → ℝ}
    (hφ : HasCompactSupport φ) : HasCompactSupport (B0579.pd j φ) :=
  hφ.fderiv_apply (𝕜 := ℝ) (B0579.dir j)

/-- Periodicity of the convolution (the kernel integral is translated by `(c, 0)`). -/
theorem cellConv_periodic_cellConvDeriv {c : ℝ} (K : ℝ × ℝ → ℝ) (f : ℝ × ℝ → ℂ)
    (hper : ∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) (x : ℝ × ℝ) :
    cellConv K f (x.1 + c, x.2) = cellConv K f x := by
  unfold cellConv
  apply integral_congr_ae
  filter_upwards with y
  have e : ((x.1 + c, x.2) - y : ℝ × ℝ) = ((x - y).1 + c, (x - y).2) := by
    ext <;> simp; ring
  rw [e, hper (x - y)]

/-- One derivative falls on the kernel: `∂_j (K ⋆ f) = (∂_j K) ⋆ f`. -/
theorem pdCx_cellConv_cellConvDeriv (K : ℝ × ℝ → ℝ) (f : ℝ × ℝ → ℂ)
    (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K) (hf : LocallyIntegrable f volume)
    (j : Fin 2) (x : ℝ × ℝ) :
    pdCx j (cellConv K f) x = cellConv (B0579.pd j K) f x := by
  have hK1 : ContDiff ℝ 1 K := hK.of_le (by simp)
  have hd := hKc.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hK1 hf x
  rw [← cellConv_eq_convolution] at hd
  unfold pdCx
  rw [hd.fderiv]
  have hcv : ConvolutionExists (fderiv ℝ K) f
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (ℝ × ℝ)) volume :=
    (hKc.fderiv (𝕜 := ℝ)).convolutionExists_left _
      (hK.continuous_fderiv (by simp)) hf
  have hint := hcv x
  rw [convolution_def, ContinuousLinearMap.integral_apply hint]
  unfold cellConv
  apply integral_congr_ae
  filter_upwards with y
  rfl

/-- Words: the derivatives commute with the convolution and fall on the kernel. -/
theorem words_cellConvDeriv (f : ℝ × ℝ → ℂ) (hf : LocallyIntegrable f volume) :
    ∀ (w : List (Fin 2)) (K : ℝ × ℝ → ℝ), ContDiff ℝ ∞ K → HasCompactSupport K →
      adjSpatial w (cellConv K f) = cellConv (pdWordR w K) f ∧
        ContDiff ℝ ∞ (pdWordR w K) ∧ HasCompactSupport (pdWordR w K)
  | [], K, hK, hKc => ⟨rfl, hK, hKc⟩
  | j :: w, K, hK, hKc => by
    obtain ⟨h1, h2, h3⟩ := words_cellConvDeriv f hf w K hK hKc
    refine ⟨?_, pd_contDiff_cellConvDeriv h2, pd_hasCompactSupport_cellConvDeriv h3⟩
    funext x
    show pdCx j (adjSpatial w (cellConv K f)) x = cellConv (B0579.pd j (pdWordR w K)) f x
    rw [h1]
    exact pdCx_cellConv_cellConvDeriv (pdWordR w K) f h2 h3 hf j x

theorem cellConvDeriv : CellConvDeriv := by
  intro c m K f hc hK hKc hper hf
  have hloc : LocallyIntegrable f volume := (cellPeriodicLocInt c m f hc hper hf).2
  refine ⟨?_, fun x => cellConv_periodic_cellConvDeriv K f hper x, fun w => ?_⟩
  · rw [cellConv_eq_convolution]
    exact hKc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hK hloc
  · exact (words_cellConvDeriv f hloc w K hK hKc).1

end UnforcedLeray.Short.IIIa
