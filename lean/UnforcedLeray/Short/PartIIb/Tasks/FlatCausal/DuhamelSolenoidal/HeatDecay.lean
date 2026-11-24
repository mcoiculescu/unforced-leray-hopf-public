import UnforcedLeray.Short.PartIIb.Sub.T12_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelSolenoidal.HeatSmooth

/-!
# Part II-b, leaf `PartII-b:T12/6/10` (`DsolHeatDecay`): Gaussian decay of the planar heat flow

Source of record: `the November 2 reference manuscript`, line 1924. The statement
is `DsolHeatDecay` of `Sub/T12_6.lean`: for `θ > 0` and `φ ∈ C_c^∞(ℝ²)` there are `a > 0` and `C`
with `‖K_θ * φ (y)‖ + ‖D(K_θ * φ)(y)‖ ≤ C e^{-a|y|²}`.

Proof outline.
* Let `R` be such that `tsupport φ ⊆ closedBall 0 R` (sup norm box). A generic bound
  (`dsolDec_conv_bound`) says that for any `ψ` with `|ψ| ≤ M` and support in the box,
  `‖K_θ * ψ (y)‖ ≤ M · dsolKc θ R · e^{-(|y|²)/(16θ)}`.
  The pointwise estimate (`dsolDec_pointwise`) uses that `ψ(y+w) ≠ 0` forces
  `|y|² ≤ 4R² + 2|w|²`, so `K_θ(w) ≤ (4πθ)⁻¹ e^{R²/(4θ)} e^{-|y|²/(16θ)} e^{-|w|²/(8θ)}`.
* The derivative is `K_θ * Dφ(·) e` by `DsolHeatSmooth` (`dsolHeatSmooth`), and `‖Dφ(z) e‖ ≤ M‖e‖`,
  so the operator norm is bounded by the same estimate applied to `Dφ(·) e`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The Gaussian `e^{-|w|²/(8θ)}` is integrable on the plane for `θ > 0`. -/
theorem dsolDec_gauss_integrable {θ : ℝ} (hθ : 0 < θ) :
    Integrable (fun w : ℝ × ℝ => Real.exp (-(1 / (8 * θ)) * (w.1 ^ 2 + w.2 ^ 2))) := by
  have h1 : Integrable (fun x : ℝ => Real.exp (-(1 / (8 * θ)) * x ^ 2)) :=
    integrable_exp_neg_mul_sq (div_pos one_pos (by linarith))
  have h2 := h1.mul_prod h1
  have hfun : (fun w : ℝ × ℝ => Real.exp (-(1 / (8 * θ)) * (w.1 ^ 2 + w.2 ^ 2))) =
      fun z : ℝ × ℝ => Real.exp (-(1 / (8 * θ)) * z.1 ^ 2) * Real.exp (-(1 / (8 * θ)) * z.2 ^ 2) := by
    funext w
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfun]
  exact h2

/-- Pointwise bound: if `|ψ| ≤ M` and `ψ` vanishes off the box `‖z‖ ≤ R`, then the integrand of
the heat convolution at `y` is dominated by a Gaussian in `w`. -/
theorem dsolDec_pointwise {θ R M : ℝ} (hθ : 0 < θ) (ψ : ℝ × ℝ → ℝ) (hψ : ∀ z, |ψ z| ≤ M)
    (hsupp : ∀ z : ℝ × ℝ, R < ‖z‖ → ψ z = 0) (y w : ℝ × ℝ) :
    ‖flatHeatKernel θ w * ψ (y + w)‖ ≤
      M * (4 * Real.pi * θ)⁻¹ * Real.exp (R ^ 2 / (4 * θ)) *
        Real.exp (-(1 / (16 * θ)) * (y.1 ^ 2 + y.2 ^ 2)) *
        Real.exp (-(1 / (8 * θ)) * (w.1 ^ 2 + w.2 ^ 2)) := by
  have hK : 0 ≤ flatHeatKernel θ w := by unfold flatHeatKernel; positivity
  have hM : 0 ≤ M := (abs_nonneg _).trans (hψ 0)
  by_cases h : ‖y + w‖ ≤ R
  · have h1 : |(y + w).1| ≤ R := by
      rw [← Real.norm_eq_abs]; exact (norm_fst_le _).trans h
    have h2 : |(y + w).2| ≤ R := by
      rw [← Real.norm_eq_abs]; exact (norm_snd_le _).trans h
    have hz1 : (y.1 + w.1) ^ 2 ≤ R ^ 2 := by
      have := sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
      rw [Prod.fst_add] at this
      exact this
    have hz2 : (y.2 + w.2) ^ 2 ≤ R ^ 2 := by
      have := sq_le_sq' (abs_le.mp h2).1 (abs_le.mp h2).2
      rw [Prod.snd_add] at this
      exact this
    have hQ : y.1 ^ 2 + y.2 ^ 2 ≤ 4 * R ^ 2 + 2 * (w.1 ^ 2 + w.2 ^ 2) := by
      nlinarith [sq_nonneg (y.1 + 2 * w.1), sq_nonneg (y.2 + 2 * w.2)]
    have hKle : flatHeatKernel θ w ≤
        (4 * Real.pi * θ)⁻¹ * (Real.exp (R ^ 2 / (4 * θ)) *
          Real.exp (-(1 / (16 * θ)) * (y.1 ^ 2 + y.2 ^ 2)) *
          Real.exp (-(1 / (8 * θ)) * (w.1 ^ 2 + w.2 ^ 2))) := by
      have hθ' : θ ≠ 0 := hθ.ne'
      have hid : R ^ 2 / (4 * θ) + -(1 / (16 * θ)) * (y.1 ^ 2 + y.2 ^ 2) +
          -(1 / (8 * θ)) * (w.1 ^ 2 + w.2 ^ 2) - (-(w.1 ^ 2 + w.2 ^ 2) / (4 * θ)) =
          (4 * R ^ 2 - (y.1 ^ 2 + y.2 ^ 2) + 2 * (w.1 ^ 2 + w.2 ^ 2)) / (16 * θ) := by
        field_simp
        ring
      have hnn : 0 ≤ (4 * R ^ 2 - (y.1 ^ 2 + y.2 ^ 2) + 2 * (w.1 ^ 2 + w.2 ^ 2)) / (16 * θ) :=
        div_nonneg (by linarith) (by linarith)
      unfold flatHeatKernel
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    rw [norm_mul, Real.norm_of_nonneg hK, Real.norm_eq_abs]
    calc flatHeatKernel θ w * |ψ (y + w)| ≤ flatHeatKernel θ w * M :=
          mul_le_mul_of_nonneg_left (hψ _) hK
      _ ≤ (4 * Real.pi * θ)⁻¹ * (Real.exp (R ^ 2 / (4 * θ)) *
          Real.exp (-(1 / (16 * θ)) * (y.1 ^ 2 + y.2 ^ 2)) *
          Real.exp (-(1 / (8 * θ)) * (w.1 ^ 2 + w.2 ^ 2))) * M :=
          mul_le_mul_of_nonneg_right hKle hM
      _ = M * (4 * Real.pi * θ)⁻¹ * Real.exp (R ^ 2 / (4 * θ)) *
          Real.exp (-(1 / (16 * θ)) * (y.1 ^ 2 + y.2 ^ 2)) *
          Real.exp (-(1 / (8 * θ)) * (w.1 ^ 2 + w.2 ^ 2)) := by ring
  · push Not at h
    rw [hsupp _ h, mul_zero, norm_zero]
    have hC : 0 ≤ M * (4 * Real.pi * θ)⁻¹ * Real.exp (R ^ 2 / (4 * θ)) *
        Real.exp (-(1 / (16 * θ)) * (y.1 ^ 2 + y.2 ^ 2)) :=
      mul_nonneg (mul_nonneg (mul_nonneg hM (by positivity)) (Real.exp_pos _).le)
        (Real.exp_pos _).le
    exact mul_nonneg hC (Real.exp_pos _).le

/-- The constant `(4πθ)⁻¹ e^{R²/(4θ)} ∫ e^{-|w|²/(8θ)}` of the decay estimate. -/
def dsolKc (θ R : ℝ) : ℝ :=
  (4 * Real.pi * θ)⁻¹ * Real.exp (R ^ 2 / (4 * θ)) *
    ∫ w : ℝ × ℝ, Real.exp (-(1 / (8 * θ)) * (w.1 ^ 2 + w.2 ^ 2))

theorem dsolKc_nonneg {θ : ℝ} (hθ : 0 < θ) (R : ℝ) : 0 ≤ dsolKc θ R := by
  unfold dsolKc
  exact mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)
    (integral_nonneg fun w => (Real.exp_pos _).le)

/-- Decay of the heat convolution of a bounded test vanishing off the box of radius `R`. -/
theorem dsolDec_conv_bound {θ R M : ℝ} (hθ : 0 < θ) (ψ : ℝ × ℝ → ℝ) (hψ : ∀ z, |ψ z| ≤ M)
    (hsupp : ∀ z : ℝ × ℝ, R < ‖z‖ → ψ z = 0) (y : ℝ × ℝ) :
    ‖dsolHeatConv θ ψ y‖ ≤ M * dsolKc θ R * Real.exp (-(1 / (16 * θ)) * (y.1 ^ 2 + y.2 ^ 2)) := by
  have hint := dsolDec_gauss_integrable hθ
  have hbound : ∀ w : ℝ × ℝ, ‖flatHeatKernel θ w * ψ (y + w)‖ ≤
      M * (4 * Real.pi * θ)⁻¹ * Real.exp (R ^ 2 / (4 * θ)) *
        Real.exp (-(1 / (16 * θ)) * (y.1 ^ 2 + y.2 ^ 2)) *
        Real.exp (-(1 / (8 * θ)) * (w.1 ^ 2 + w.2 ^ 2)) :=
    fun w => dsolDec_pointwise hθ ψ hψ hsupp y w
  have hnorm := norm_integral_le_of_norm_le (hint.const_mul
      (M * (4 * Real.pi * θ)⁻¹ * Real.exp (R ^ 2 / (4 * θ)) *
        Real.exp (-(1 / (16 * θ)) * (y.1 ^ 2 + y.2 ^ 2))))
    (ae_of_all _ hbound)
  rw [integral_const_mul] at hnorm
  unfold dsolHeatConv dsolKc
  exact hnorm.trans (le_of_eq (by ring))

/-- **Leaf `PartII-b:T12/6/10`** (Gaussian decay of the heat flow of a test; uses
`DsolHeatSmooth`). For `θ > 0` and `φ ∈ C_c^∞(ℝ²)` there are `a, C` with
`‖K_θ * φ (y)‖ + ‖D(K_θ * φ)(y)‖ ≤ C e^{-a|y|²}`. -/
theorem dsolHeatDecay : DsolHeatDecay := by
  intro θ φ hθ hφ hφc
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  obtain ⟨R, hR⟩ := hφc.isCompact.isBounded.subset_closedBall 0
  have hsupp : ∀ z : ℝ × ℝ, R < ‖z‖ → φ z = 0 := by
    intro z hz
    apply image_eq_zero_of_notMem_tsupport
    intro hzt
    have := hR hzt
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  have hsuppD : ∀ z : ℝ × ℝ, R < ‖z‖ → ∀ e : ℝ × ℝ, fderiv ℝ φ z e = 0 := by
    intro z hz e
    have h0 : fderiv ℝ φ z = 0 := by
      by_contra hne
      have hmem : z ∈ tsupport φ := support_fderiv_subset ℝ (Function.mem_support.2 hne)
      have := hR hmem
      rw [Metric.mem_closedBall, dist_zero_right] at this
      linarith
    simp [h0]
  have hfc : HasCompactSupport (fderiv ℝ φ) := hφc.fderiv ℝ
  have hfcont : Continuous (fderiv ℝ φ) := hφ1.continuous_fderiv one_ne_zero
  obtain ⟨Mder, hMder⟩ := hfcont.bounded_above_of_compact_support hfc
  obtain ⟨Mφ, hMφ⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hφbd : ∀ z, |φ z| ≤ Mφ := fun z => by rw [← Real.norm_eq_abs]; exact hMφ z
  have hMder0 : 0 ≤ Mder := (norm_nonneg _).trans (hMder 0)
  have hMφ0 : 0 ≤ Mφ := (norm_nonneg _).trans (hMφ 0)
  have hK0 := dsolKc_nonneg hθ R
  refine ⟨1 / (16 * θ), Mφ * dsolKc θ R + Mder * dsolKc θ R,
    div_pos one_pos (by linarith), fun y => ?_⟩
  have h1 : ‖dsolHeatConv θ φ y‖ ≤
      Mφ * dsolKc θ R * Real.exp (-(1 / (16 * θ)) * (y.1 ^ 2 + y.2 ^ 2)) :=
    dsolDec_conv_bound hθ φ hφbd hsupp y
  have hψe : ∀ e : ℝ × ℝ, ∀ z : ℝ × ℝ, |fderiv ℝ φ z e| ≤ Mder * ‖e‖ := by
    intro e z
    rw [← Real.norm_eq_abs]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hMder z) (norm_nonneg _))
  have hderiv : ‖fderiv ℝ (dsolHeatConv θ φ) y‖ ≤
      Mder * dsolKc θ R * Real.exp (-(1 / (16 * θ)) * (y.1 ^ 2 + y.2 ^ 2)) := by
    have hM'0 : 0 ≤ Mder * dsolKc θ R * Real.exp (-(1 / (16 * θ)) * (y.1 ^ 2 + y.2 ^ 2)) :=
      mul_nonneg (mul_nonneg hMder0 hK0) (Real.exp_pos _).le
    refine ContinuousLinearMap.opNorm_le_bound _ hM'0 (fun e => ?_)
    have hbe : ‖dsolHeatConv θ (fun z => fderiv ℝ φ z e) y‖ ≤
        (Mder * ‖e‖) * dsolKc θ R *
          Real.exp (-(1 / (16 * θ)) * (y.1 ^ 2 + y.2 ^ 2)) :=
      dsolDec_conv_bound hθ (fun z => fderiv ℝ φ z e) (hψe e)
        (fun z hz => hsuppD z hz e) y
    rw [(dsolHeatSmooth θ φ hθ hφ hφc).2 y e]
    calc ‖dsolHeatConv θ (fun z => fderiv ℝ φ z e) y‖
        ≤ (Mder * ‖e‖) * dsolKc θ R *
          Real.exp (-(1 / (16 * θ)) * (y.1 ^ 2 + y.2 ^ 2)) := hbe
      _ = (Mder * dsolKc θ R * Real.exp (-(1 / (16 * θ)) * (y.1 ^ 2 + y.2 ^ 2))) * ‖e‖ := by
          ring
  calc ‖dsolHeatConv θ φ y‖ + ‖fderiv ℝ (dsolHeatConv θ φ) y‖
      ≤ Mφ * dsolKc θ R * Real.exp (-(1 / (16 * θ)) * (y.1 ^ 2 + y.2 ^ 2)) +
        Mder * dsolKc θ R * Real.exp (-(1 / (16 * θ)) * (y.1 ^ 2 + y.2 ^ 2)) :=
        add_le_add h1 hderiv
    _ = (Mφ * dsolKc θ R + Mder * dsolKc θ R) *
        Real.exp (-(1 / (16 * θ)) * (y.1 ^ 2 + y.2 ^ 2)) := by ring

end UnforcedLeray.Short.IIb
