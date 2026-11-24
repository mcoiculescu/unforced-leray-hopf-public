import UnforcedLeray.Short.PartIIb.Sub.T12_7
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.FlatHeatContraction
import UnforcedLeray.Lib.HeatCylinder.HeatKernelAgeMajorant
import UnforcedLeray.Lib.HeatCylinder.HeatKernelAgeIntegrable
import UnforcedLeray.Lib.HeatCylinder.HeatKernelAgeDerivative
import UnforcedLeray.Units.B0296.Kernel

/-!
# Part II-b, leaf `PartII-b:T12/7/2` (`deqHeatDeriv`): planar heat equation for a test function

Source of record: `the November 2 reference manuscript`, lines 1923-1927 (the
heat semigroup `e^{ν(s-t)Δ}` in the causal formula). The statement is `DeqHeatDeriv` of
`Sub/T12_7.lean`.

Proof outline.
* For `θ > 0`, `flatHeatKernel θ = heatKernel2 θ` (`flatHeat_kernel_eq`), so the `θ`-derivative of
  `∫ K_θ(w) ψ(z - w) dw` is `∫ (∂_θ K)_θ(w) ψ(z - w) dw` (dominated differentiation under the
  integral, Gaussian majorant on `θ ∈ (θ₀/2, 2θ₀)`, as in `HeatEq/ThetaDeriv.lean`).
* The age derivative splits as `∂_θ K = (q²/(4θ²) - 1/(2θ)) K + (η²/(4θ²) - 1/(2θ)) K`.
* Each coordinate is moved to `ψ(z - ·)` by two Gaussian integrations by parts
  (`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`), which yields the planar Laplacian
  `planarLap ψ (z - w)`.

Helpers use the prefix `deqhd`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-! ## The planar Gaussian and its first derivatives -/

/-- The planar Gaussian `K_θ = heatKernel2 θ` (abbreviation). -/
abbrev deqhdK (θ : ℝ) : ℝ × ℝ → ℝ := UnforcedLeray.B0284.heatKernel2 θ

theorem deqhdK_diff {θ : ℝ} (hθ : θ ≠ 0) : Differentiable ℝ (deqhdK θ) := by
  have hg : Differentiable ℝ (UnforcedLeray.B0191.heatKernel 1 θ) :=
    fun x => (UnforcedLeray.B0296.hasDerivAt_heatKernel hθ x).differentiableAt
  exact (hg.comp differentiable_fst).mul (hg.comp differentiable_snd)

theorem deqhdK_cont {θ : ℝ} (hθ : θ ≠ 0) : Continuous (deqhdK θ) :=
  (deqhdK_diff hθ).continuous

theorem deqhd_slice_fst {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (a b : ℝ) :
    HasDerivAt (fun t : ℝ => f (t, b)) (fderiv ℝ f (a, b) ((1 : ℝ), (0 : ℝ))) a := by
  have h1 : HasDerivAt (fun t : ℝ => ((t, b) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) a :=
    (hasDerivAt_id' a).prodMk (hasDerivAt_const a b)
  exact (hf (a, b)).hasFDerivAt.comp_hasDerivAt a h1

theorem deqhd_slice_snd {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (a b : ℝ) :
    HasDerivAt (fun t : ℝ => f (a, t)) (fderiv ℝ f (a, b) ((0 : ℝ), (1 : ℝ))) b := by
  have h1 : HasDerivAt (fun t : ℝ => ((a, t) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) b :=
    (hasDerivAt_const b a).prodMk (hasDerivAt_id' b)
  exact (hf (a, b)).hasFDerivAt.comp_hasDerivAt b h1

theorem deqhd_fderiv_sub {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (z e w : ℝ × ℝ) :
    fderiv ℝ (fun y : ℝ × ℝ => f (z - y)) w e = -(fderiv ℝ f (z - w) e) := by
  have hm : HasFDerivAt (fun y : ℝ × ℝ => z - y) (-ContinuousLinearMap.id ℝ (ℝ × ℝ)) w :=
    (hasFDerivAt_id w).const_sub z
  have hcomp := (hf (z - w)).hasFDerivAt.comp w hm
  change fderiv ℝ (f ∘ (fun y : ℝ × ℝ => z - y)) w e = _
  rw [hcomp.fderiv]
  simp

theorem deqhd_fderiv_K_fst_ab {θ : ℝ} (hθ : θ ≠ 0) (a b : ℝ) :
    fderiv ℝ (deqhdK θ) (a, b) ((1 : ℝ), (0 : ℝ)) = -(a / (2 * θ)) * deqhdK θ (a, b) := by
  have h1 := deqhd_slice_fst (deqhdK_diff hθ) a b
  have h2 := UnforcedLeray.B0296.hasDerivAt_heatKernel2_fst hθ (a, b)
  have h3 : fderiv ℝ (deqhdK θ) (a, b) ((1 : ℝ), (0 : ℝ)) =
      UnforcedLeray.B0296.dHeatKernel θ a * UnforcedLeray.B0191.heatKernel 1 θ b :=
    h1.unique h2
  rw [h3]
  simp only [UnforcedLeray.B0296.dHeatKernel, deqhdK, UnforcedLeray.B0284.heatKernel2]
  ring

theorem deqhd_fderiv_K_fst {θ : ℝ} (hθ : θ ≠ 0) (w : ℝ × ℝ) :
    fderiv ℝ (deqhdK θ) w ((1 : ℝ), (0 : ℝ)) = -(w.1 / (2 * θ)) * deqhdK θ w := by
  obtain ⟨a, b⟩ := w
  exact deqhd_fderiv_K_fst_ab hθ a b

theorem deqhd_fderiv_K_snd_ab {θ : ℝ} (hθ : θ ≠ 0) (a b : ℝ) :
    fderiv ℝ (deqhdK θ) (a, b) ((0 : ℝ), (1 : ℝ)) = -(b / (2 * θ)) * deqhdK θ (a, b) := by
  have h1 := deqhd_slice_snd (deqhdK_diff hθ) a b
  have h2 := UnforcedLeray.B0296.hasDerivAt_heatKernel2_snd hθ (a, b)
  have h3 : fderiv ℝ (deqhdK θ) (a, b) ((0 : ℝ), (1 : ℝ)) =
      UnforcedLeray.B0191.heatKernel 1 θ a * UnforcedLeray.B0296.dHeatKernel θ b :=
    h1.unique h2
  rw [h3]
  simp only [UnforcedLeray.B0296.dHeatKernel, deqhdK, UnforcedLeray.B0284.heatKernel2]
  ring

theorem deqhd_fderiv_K_snd {θ : ℝ} (hθ : θ ≠ 0) (w : ℝ × ℝ) :
    fderiv ℝ (deqhdK θ) w ((0 : ℝ), (1 : ℝ)) = -(w.2 / (2 * θ)) * deqhdK θ w := by
  obtain ⟨a, b⟩ := w
  exact deqhd_fderiv_K_snd_ab hθ a b

/-- The derivative in `q` of `-(q/(2θ)) K_θ`: `(q²/(4θ²) - 1/(2θ)) K_θ`. -/
theorem deqhd_fderiv_D1 {θ : ℝ} (hθ : θ ≠ 0) (w : ℝ × ℝ) :
    fderiv ℝ (fun v : ℝ × ℝ => -(v.1 / (2 * θ)) * deqhdK θ v) w ((1 : ℝ), (0 : ℝ)) =
      (w.1 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * deqhdK θ w := by
  obtain ⟨a, b⟩ := w
  have hD : Differentiable ℝ (fun v : ℝ × ℝ => -(v.1 / (2 * θ)) * deqhdK θ v) :=
    (show Differentiable ℝ (fun v : ℝ × ℝ => -(v.1 / (2 * θ))) by fun_prop).mul (deqhdK_diff hθ)
  have h1 := deqhd_slice_fst hD a b
  have hx : HasDerivAt (fun t : ℝ => -(t / (2 * θ))) (-(1 / (2 * θ))) a := by
    exact ((hasDerivAt_id' a).div_const (2 * θ)).neg
  have h2 := hx.mul (deqhd_slice_fst (deqhdK_diff hθ) a b)
  rw [h1.unique h2, deqhd_fderiv_K_fst_ab hθ a b]
  dsimp only
  ring

/-- The derivative in `η` of `-(η/(2θ)) K_θ`: `(η²/(4θ²) - 1/(2θ)) K_θ`. -/
theorem deqhd_fderiv_D2 {θ : ℝ} (hθ : θ ≠ 0) (w : ℝ × ℝ) :
    fderiv ℝ (fun v : ℝ × ℝ => -(v.2 / (2 * θ)) * deqhdK θ v) w ((0 : ℝ), (1 : ℝ)) =
      (w.2 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * deqhdK θ w := by
  obtain ⟨a, b⟩ := w
  have hD : Differentiable ℝ (fun v : ℝ × ℝ => -(v.2 / (2 * θ)) * deqhdK θ v) :=
    (show Differentiable ℝ (fun v : ℝ × ℝ => -(v.2 / (2 * θ))) by fun_prop).mul (deqhdK_diff hθ)
  have h1 := deqhd_slice_snd hD a b
  have hx : HasDerivAt (fun t : ℝ => -(t / (2 * θ))) (-(1 / (2 * θ))) b := by
    exact ((hasDerivAt_id' b).div_const (2 * θ)).neg
  have h2 := hx.mul (deqhd_slice_snd (deqhdK_diff hθ) a b)
  rw [h1.unique h2, deqhd_fderiv_K_snd_ab hθ a b]
  dsimp only
  ring

/-! ## Polynomial and Gaussian bounds -/

theorem deqhd_abs_quad1 {θ : ℝ} (hθ : 0 < θ) (w : ℝ × ℝ) :
    |w.1 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)| ≤
      (1 / (4 * θ ^ 2) + 1 / (2 * θ)) * (1 + w.1 ^ 2 + w.2 ^ 2) := by
  have hc1 : 0 ≤ 1 / (4 * θ ^ 2) := by positivity
  have hc2 : 0 ≤ 1 / (2 * θ) := by positivity
  have e : w.1 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ) =
      (1 / (4 * θ ^ 2)) * w.1 ^ 2 - 1 / (2 * θ) := by ring
  rw [e, abs_le]
  constructor <;> nlinarith [mul_nonneg hc1 (sq_nonneg w.1), mul_nonneg hc1 (sq_nonneg w.2),
    mul_nonneg hc2 (sq_nonneg w.1), mul_nonneg hc2 (sq_nonneg w.2), sq_nonneg w.1, sq_nonneg w.2]

theorem deqhd_abs_quad2 {θ : ℝ} (hθ : 0 < θ) (w : ℝ × ℝ) :
    |w.2 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)| ≤
      (1 / (4 * θ ^ 2) + 1 / (2 * θ)) * (1 + w.1 ^ 2 + w.2 ^ 2) := by
  have hc1 : 0 ≤ 1 / (4 * θ ^ 2) := by positivity
  have hc2 : 0 ≤ 1 / (2 * θ) := by positivity
  have e : w.2 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ) =
      (1 / (4 * θ ^ 2)) * w.2 ^ 2 - 1 / (2 * θ) := by ring
  rw [e, abs_le]
  constructor <;> nlinarith [mul_nonneg hc1 (sq_nonneg w.1), mul_nonneg hc1 (sq_nonneg w.2),
    mul_nonneg hc2 (sq_nonneg w.1), mul_nonneg hc2 (sq_nonneg w.2), sq_nonneg w.1, sq_nonneg w.2]

theorem deqhd_abs_lin1 {θ : ℝ} (hθ : 0 < θ) (w : ℝ × ℝ) :
    |-(w.1 / (2 * θ))| ≤ (1 / (2 * θ)) * (1 + w.1 ^ 2 + w.2 ^ 2) := by
  have e : -(w.1 / (2 * θ)) = (-(1 / (2 * θ))) * w.1 := by ring
  have hc : 0 < 1 / (2 * θ) := by positivity
  rw [e, abs_mul, abs_neg, abs_of_pos hc]
  refine mul_le_mul_of_nonneg_left ?_ hc.le
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (w.1 - 1 / 2), sq_nonneg (w.1 + 1 / 2), sq_nonneg w.2]

theorem deqhd_abs_lin2 {θ : ℝ} (hθ : 0 < θ) (w : ℝ × ℝ) :
    |-(w.2 / (2 * θ))| ≤ (1 / (2 * θ)) * (1 + w.1 ^ 2 + w.2 ^ 2) := by
  have e : -(w.2 / (2 * θ)) = (-(1 / (2 * θ))) * w.2 := by ring
  have hc : 0 < 1 / (2 * θ) := by positivity
  rw [e, abs_mul, abs_neg, abs_of_pos hc]
  refine mul_le_mul_of_nonneg_left ?_ hc.le
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (w.2 - 1 / 2), sq_nonneg (w.2 + 1 / 2), sq_nonneg w.1]

/-- Gaussian integrability with a polynomial weight and a bounded continuous factor. -/
theorem deqhd_int_gauss {θ : ℝ} (hθ : 0 < θ) {P h : ℝ × ℝ → ℝ} {C B : ℝ} (hC : 0 ≤ C)
    (hP : Continuous P) (hPb : ∀ w, |P w| ≤ C * (1 + w.1 ^ 2 + w.2 ^ 2))
    (hh : Continuous h) (hhb : ∀ w, |h w| ≤ B) :
    Integrable (fun w => P w * deqhdK θ w * h w) := by
  have hKc : Continuous (deqhdK θ) := deqhdK_cont hθ.ne'
  refine Integrable.mono' ((UnforcedLeray.HeatCylinder.integrable_one_add_sq_mul_heatKernel2 hθ).const_mul
    (C * B)) ?_ ?_
  · exact ((hP.mul hKc).mul hh).aestronglyMeasurable
  · refine ae_of_all _ fun w => ?_
    have hK : 0 ≤ deqhdK θ w := UnforcedLeray.B0284.heatKernel2_nonneg hθ w
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hK]
    have h1 : |P w| * deqhdK θ w ≤ (C * (1 + w.1 ^ 2 + w.2 ^ 2)) * deqhdK θ w :=
      mul_le_mul_of_nonneg_right (hPb w) hK
    have h2 : |P w| * deqhdK θ w * |h w| ≤ (C * (1 + w.1 ^ 2 + w.2 ^ 2)) * deqhdK θ w * B :=
      mul_le_mul h1 (hhb w) (abs_nonneg _)
        (mul_nonneg (mul_nonneg hC (by positivity)) hK)
    calc |P w| * deqhdK θ w * |h w|
        ≤ (C * (1 + w.1 ^ 2 + w.2 ^ 2)) * deqhdK θ w * B := h2
      _ = (C * B) * ((1 + w.1 ^ 2 + w.2 ^ 2) * deqhdK θ w) := by ring

/-- Gaussian integrability against a bounded continuous factor. -/
theorem deqhd_int_K {θ : ℝ} (hθ : 0 < θ) {h : ℝ × ℝ → ℝ} {B : ℝ} (hh : Continuous h)
    (hhb : ∀ w, |h w| ≤ B) :
    Integrable (fun w => deqhdK θ w * h w) :=
  (UnforcedLeray.B0284.integrable_heatKernel2 hθ).mul_bdd hh.aestronglyMeasurable
    (ae_of_all _ fun w => by rw [Real.norm_eq_abs]; exact hhb w)

theorem deqhd_bdd_fn {φ : ℝ × ℝ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    ∃ B, ∀ y, ‖φ y‖ ≤ B :=
  hφ.bounded_above_of_compact_support hφc

theorem deqhd_cont_apply {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (v : ℝ × ℝ) :
    Continuous (fun y => fderiv ℝ φ y v) :=
  (hφ.continuous_fderiv (by simp)).clm_apply continuous_const

theorem deqhd_bdd_apply {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (v : ℝ × ℝ) : ∃ B, ∀ y, ‖fderiv ℝ φ y v‖ ≤ B :=
  (deqhd_cont_apply hφ v).bounded_above_of_compact_support (hφc.fderiv_apply ℝ v)

/-! ## Gaussian integration by parts in one coordinate -/

/-- Integration by parts in `q`: the `q`-derivative of the Gaussian moved onto `ψ(z - ·)`. -/
theorem deqhd_x_ibp {θ : ℝ} (hθ : 0 < θ) {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (z : ℝ × ℝ) :
    ∫ w : ℝ × ℝ, (w.1 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * deqhdK θ w * ψ (z - w) =
      ∫ w : ℝ × ℝ, deqhdK θ w *
        fderiv ℝ (fun y : ℝ × ℝ => fderiv ℝ ψ y (1, 0)) (z - w) (1, 0) := by
  have hθ0 : θ ≠ 0 := hθ.ne'
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hψc0 : Continuous ψ := hψ.continuous
  have hψ1 : ContDiff ℝ ∞ (fun y : ℝ × ℝ => fderiv ℝ ψ y (1, 0)) :=
    (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  have hψ1d : Differentiable ℝ (fun y : ℝ × ℝ => fderiv ℝ ψ y (1, 0)) :=
    hψ1.differentiable (by simp)
  have hψ1c : HasCompactSupport (fun y : ℝ × ℝ => fderiv ℝ ψ y (1, 0)) :=
    hψc.fderiv_apply ℝ _
  have hDd : Differentiable ℝ (fun v : ℝ × ℝ => -(v.1 / (2 * θ)) * deqhdK θ v) :=
    (show Differentiable ℝ (fun v : ℝ × ℝ => -(v.1 / (2 * θ))) by fun_prop).mul (deqhdK_diff hθ0)
  have hgdiff : Differentiable ℝ (fun y : ℝ × ℝ => ψ (z - y)) :=
    hψd.comp ((differentiable_const z).sub differentiable_id)
  have hg2diff : Differentiable ℝ (fun y : ℝ × ℝ => fderiv ℝ ψ (z - y) (1, 0)) :=
    hψ1d.comp ((differentiable_const z).sub differentiable_id)
  have hgd : ∀ w : ℝ × ℝ, fderiv ℝ (fun y : ℝ × ℝ => ψ (z - y)) w ((1 : ℝ), (0 : ℝ)) =
      -(fderiv ℝ ψ (z - w) ((1 : ℝ), (0 : ℝ))) :=
    fun w => deqhd_fderiv_sub hψd z _ w
  have hgd2 : ∀ w : ℝ × ℝ,
      fderiv ℝ (fun y : ℝ × ℝ => fderiv ℝ ψ (z - y) ((1 : ℝ), (0 : ℝ))) w ((1 : ℝ), (0 : ℝ)) =
        -(fderiv ℝ (fun y : ℝ × ℝ => fderiv ℝ ψ y (1, 0)) (z - w) ((1 : ℝ), (0 : ℝ))) :=
    fun w => deqhd_fderiv_sub hψ1d z _ w
  -- bounds and continuity of the factors
  obtain ⟨Bψ, hBψ⟩ := deqhd_bdd_fn hψc0 hψc
  obtain ⟨B1, hB1⟩ := deqhd_bdd_apply hψ hψc ((1 : ℝ), (0 : ℝ))
  obtain ⟨B2, hB2⟩ := deqhd_bdd_apply hψ1 hψ1c ((1 : ℝ), (0 : ℝ))
  have hcψ : Continuous (fun w : ℝ × ℝ => ψ (z - w)) :=
    hψc0.comp (continuous_const.sub continuous_id)
  have hcψ1 : Continuous (fun w : ℝ × ℝ => fderiv ℝ ψ (z - w) ((1 : ℝ), (0 : ℝ))) :=
    (deqhd_cont_apply hψ ((1 : ℝ), (0 : ℝ))).comp (continuous_const.sub continuous_id)
  have hcψ2 : Continuous (fun w : ℝ × ℝ =>
      fderiv ℝ (fun y : ℝ × ℝ => fderiv ℝ ψ y (1, 0)) (z - w) ((1 : ℝ), (0 : ℝ))) :=
    (deqhd_cont_apply hψ1 ((1 : ℝ), (0 : ℝ))).comp (continuous_const.sub continuous_id)
  have hbψ : ∀ w : ℝ × ℝ, |ψ (z - w)| ≤ Bψ := fun w => by
    rw [← Real.norm_eq_abs]; exact hBψ (z - w)
  have hbψ1 : ∀ w : ℝ × ℝ, |fderiv ℝ ψ (z - w) ((1 : ℝ), (0 : ℝ))| ≤ B1 := fun w => by
    rw [← Real.norm_eq_abs]; exact hB1 (z - w)
  have hbψ2 : ∀ w : ℝ × ℝ,
      |fderiv ℝ (fun y : ℝ × ℝ => fderiv ℝ ψ y (1, 0)) (z - w) ((1 : ℝ), (0 : ℝ))| ≤ B2 :=
    fun w => by rw [← Real.norm_eq_abs]; exact hB2 (z - w)
  -- integrability
  have hA1 : Integrable (fun w : ℝ × ℝ =>
      (w.1 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * deqhdK θ w * ψ (z - w)) :=
    deqhd_int_gauss hθ (by positivity) (by fun_prop) (fun w => deqhd_abs_quad1 hθ w)
      hcψ hbψ
  have hA2 : Integrable (fun w : ℝ × ℝ => (-(w.1 / (2 * θ))) * deqhdK θ w * ψ (z - w)) :=
    deqhd_int_gauss hθ (by positivity) (by fun_prop) (fun w => deqhd_abs_lin1 hθ w)
      hcψ hbψ
  have hA3 : Integrable (fun w : ℝ × ℝ =>
      (-(w.1 / (2 * θ))) * deqhdK θ w * (-(fderiv ℝ ψ (z - w) ((1 : ℝ), (0 : ℝ))))) :=
    deqhd_int_gauss hθ (by positivity) (by fun_prop) (fun w => deqhd_abs_lin1 hθ w)
      hcψ1.neg (fun w => by rw [abs_neg]; exact hbψ1 w)
  have hA4 : Integrable (fun w : ℝ × ℝ =>
      deqhdK θ w * fderiv ℝ ψ (z - w) ((1 : ℝ), (0 : ℝ))) :=
    deqhd_int_K hθ hcψ1 hbψ1
  have hA5 : Integrable (fun w : ℝ × ℝ =>
      deqhdK θ w * (-(fderiv ℝ (fun y : ℝ × ℝ => fderiv ℝ ψ y (1, 0)) (z - w)
        ((1 : ℝ), (0 : ℝ))))) :=
    deqhd_int_K hθ hcψ2.neg (fun w => by rw [abs_neg]; exact hbψ2 w)
  have hA6 : Integrable (fun w : ℝ × ℝ =>
      (-(w.1 / (2 * θ))) * deqhdK θ w * fderiv ℝ ψ (z - w) ((1 : ℝ), (0 : ℝ))) :=
    deqhd_int_gauss hθ (by positivity) (by fun_prop) (fun w => deqhd_abs_lin1 hθ w)
      hcψ1 hbψ1
  -- first integration by parts: `q`-derivative of `-(q/(2θ))K` onto `ψ(z - ·)`
  have ibp1 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun v : ℝ × ℝ => -(v.1 / (2 * θ)) * deqhdK θ v)
    (g := fun y : ℝ × ℝ => ψ (z - y)) (v := ((1 : ℝ), (0 : ℝ)))
    (by simp only [deqhd_fderiv_D1 hθ0]; exact hA1)
    (by simp only [hgd]; exact hA3)
    hA2
    (fun x _ => hDd.differentiableAt)
    (fun x _ => hgdiff.differentiableAt)
  -- second integration by parts: `K` against the `q`-derivative of `ψ1(z - ·)`
  have ibp2 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := deqhdK θ)
    (g := fun y : ℝ × ℝ => fderiv ℝ ψ (z - y) ((1 : ℝ), (0 : ℝ))) (v := ((1 : ℝ), (0 : ℝ)))
    (by simp only [deqhd_fderiv_K_fst hθ0]; exact hA6)
    (by simp only [hgd2]; exact hA5)
    hA4
    (fun x _ => (deqhdK_diff hθ0).differentiableAt)
    (fun x _ => hg2diff.differentiableAt)
  simp only [hgd, deqhd_fderiv_D1 hθ0, hgd2, deqhd_fderiv_K_fst hθ0, mul_neg, integral_neg]
    at ibp1 ibp2
  linarith

/-- Integration by parts in `η`: the `η`-derivative of the Gaussian moved onto `ψ(z - ·)`. -/
theorem deqhd_y_ibp {θ : ℝ} (hθ : 0 < θ) {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (z : ℝ × ℝ) :
    ∫ w : ℝ × ℝ, (w.2 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * deqhdK θ w * ψ (z - w) =
      ∫ w : ℝ × ℝ, deqhdK θ w *
        fderiv ℝ (fun y : ℝ × ℝ => fderiv ℝ ψ y (0, 1)) (z - w) (0, 1) := by
  have hθ0 : θ ≠ 0 := hθ.ne'
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hψc0 : Continuous ψ := hψ.continuous
  have hψ1 : ContDiff ℝ ∞ (fun y : ℝ × ℝ => fderiv ℝ ψ y (0, 1)) :=
    (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  have hψ1d : Differentiable ℝ (fun y : ℝ × ℝ => fderiv ℝ ψ y (0, 1)) :=
    hψ1.differentiable (by simp)
  have hψ1c : HasCompactSupport (fun y : ℝ × ℝ => fderiv ℝ ψ y (0, 1)) :=
    hψc.fderiv_apply ℝ _
  have hDd : Differentiable ℝ (fun v : ℝ × ℝ => -(v.2 / (2 * θ)) * deqhdK θ v) :=
    (show Differentiable ℝ (fun v : ℝ × ℝ => -(v.2 / (2 * θ))) by fun_prop).mul (deqhdK_diff hθ0)
  have hgdiff : Differentiable ℝ (fun y : ℝ × ℝ => ψ (z - y)) :=
    hψd.comp ((differentiable_const z).sub differentiable_id)
  have hg2diff : Differentiable ℝ (fun y : ℝ × ℝ => fderiv ℝ ψ (z - y) ((0 : ℝ), (1 : ℝ))) :=
    hψ1d.comp ((differentiable_const z).sub differentiable_id)
  have hgd : ∀ w : ℝ × ℝ, fderiv ℝ (fun y : ℝ × ℝ => ψ (z - y)) w ((0 : ℝ), (1 : ℝ)) =
      -(fderiv ℝ ψ (z - w) ((0 : ℝ), (1 : ℝ))) :=
    fun w => deqhd_fderiv_sub hψd z _ w
  have hgd2 : ∀ w : ℝ × ℝ,
      fderiv ℝ (fun y : ℝ × ℝ => fderiv ℝ ψ (z - y) ((0 : ℝ), (1 : ℝ))) w ((0 : ℝ), (1 : ℝ)) =
        -(fderiv ℝ (fun y : ℝ × ℝ => fderiv ℝ ψ y (0, 1)) (z - w) ((0 : ℝ), (1 : ℝ))) :=
    fun w => deqhd_fderiv_sub hψ1d z _ w
  obtain ⟨Bψ, hBψ⟩ := deqhd_bdd_fn hψc0 hψc
  obtain ⟨B1, hB1⟩ := deqhd_bdd_apply hψ hψc ((0 : ℝ), (1 : ℝ))
  obtain ⟨B2, hB2⟩ := deqhd_bdd_apply hψ1 hψ1c ((0 : ℝ), (1 : ℝ))
  have hcψ : Continuous (fun w : ℝ × ℝ => ψ (z - w)) :=
    hψc0.comp (continuous_const.sub continuous_id)
  have hcψ1 : Continuous (fun w : ℝ × ℝ => fderiv ℝ ψ (z - w) ((0 : ℝ), (1 : ℝ))) :=
    (deqhd_cont_apply hψ ((0 : ℝ), (1 : ℝ))).comp (continuous_const.sub continuous_id)
  have hcψ2 : Continuous (fun w : ℝ × ℝ =>
      fderiv ℝ (fun y : ℝ × ℝ => fderiv ℝ ψ y (0, 1)) (z - w) ((0 : ℝ), (1 : ℝ))) :=
    (deqhd_cont_apply hψ1 ((0 : ℝ), (1 : ℝ))).comp (continuous_const.sub continuous_id)
  have hbψ : ∀ w : ℝ × ℝ, |ψ (z - w)| ≤ Bψ := fun w => by
    rw [← Real.norm_eq_abs]; exact hBψ (z - w)
  have hbψ1 : ∀ w : ℝ × ℝ, |fderiv ℝ ψ (z - w) ((0 : ℝ), (1 : ℝ))| ≤ B1 := fun w => by
    rw [← Real.norm_eq_abs]; exact hB1 (z - w)
  have hbψ2 : ∀ w : ℝ × ℝ,
      |fderiv ℝ (fun y : ℝ × ℝ => fderiv ℝ ψ y (0, 1)) (z - w) ((0 : ℝ), (1 : ℝ))| ≤ B2 :=
    fun w => by rw [← Real.norm_eq_abs]; exact hB2 (z - w)
  have hA1 : Integrable (fun w : ℝ × ℝ =>
      (w.2 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * deqhdK θ w * ψ (z - w)) :=
    deqhd_int_gauss hθ (by positivity) (by fun_prop) (fun w => deqhd_abs_quad2 hθ w)
      hcψ hbψ
  have hA2 : Integrable (fun w : ℝ × ℝ => (-(w.2 / (2 * θ))) * deqhdK θ w * ψ (z - w)) :=
    deqhd_int_gauss hθ (by positivity) (by fun_prop) (fun w => deqhd_abs_lin2 hθ w)
      hcψ hbψ
  have hA3 : Integrable (fun w : ℝ × ℝ =>
      (-(w.2 / (2 * θ))) * deqhdK θ w * (-(fderiv ℝ ψ (z - w) ((0 : ℝ), (1 : ℝ))))) :=
    deqhd_int_gauss hθ (by positivity) (by fun_prop) (fun w => deqhd_abs_lin2 hθ w)
      hcψ1.neg (fun w => by rw [abs_neg]; exact hbψ1 w)
  have hA4 : Integrable (fun w : ℝ × ℝ =>
      deqhdK θ w * fderiv ℝ ψ (z - w) ((0 : ℝ), (1 : ℝ))) :=
    deqhd_int_K hθ hcψ1 hbψ1
  have hA5 : Integrable (fun w : ℝ × ℝ =>
      deqhdK θ w * (-(fderiv ℝ (fun y : ℝ × ℝ => fderiv ℝ ψ y (0, 1)) (z - w)
        ((0 : ℝ), (1 : ℝ))))) :=
    deqhd_int_K hθ hcψ2.neg (fun w => by rw [abs_neg]; exact hbψ2 w)
  have hA6 : Integrable (fun w : ℝ × ℝ =>
      (-(w.2 / (2 * θ))) * deqhdK θ w * fderiv ℝ ψ (z - w) ((0 : ℝ), (1 : ℝ))) :=
    deqhd_int_gauss hθ (by positivity) (by fun_prop) (fun w => deqhd_abs_lin2 hθ w)
      hcψ1 hbψ1
  have ibp1 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun v : ℝ × ℝ => -(v.2 / (2 * θ)) * deqhdK θ v)
    (g := fun y : ℝ × ℝ => ψ (z - y)) (v := ((0 : ℝ), (1 : ℝ)))
    (by simp only [deqhd_fderiv_D2 hθ0]; exact hA1)
    (by simp only [hgd]; exact hA3)
    hA2
    (fun x _ => hDd.differentiableAt)
    (fun x _ => hgdiff.differentiableAt)
  have ibp2 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := deqhdK θ)
    (g := fun y : ℝ × ℝ => fderiv ℝ ψ (z - y) ((0 : ℝ), (1 : ℝ))) (v := ((0 : ℝ), (1 : ℝ)))
    (by simp only [deqhd_fderiv_K_snd hθ0]; exact hA6)
    (by simp only [hgd2]; exact hA5)
    hA4
    (fun x _ => (deqhdK_diff hθ0).differentiableAt)
    (fun x _ => hg2diff.differentiableAt)
  simp only [hgd, deqhd_fderiv_D2 hθ0, hgd2, deqhd_fderiv_K_snd hθ0, mul_neg, integral_neg]
    at ibp1 ibp2
  linarith

/-! ## Differentiation in the heat age -/

/-- Differentiation in `θ` of `∫ K_θ(w) ψ(z - w) dw` at `θ₀ > 0` (dominated convergence on
`θ ∈ (θ₀/2, 2θ₀)`, as in `HeatEq/ThetaDeriv.lean`). -/
theorem deqhd_theta_hasDerivAt {ψ : ℝ × ℝ → ℝ} (hψc : Continuous ψ) {B : ℝ}
    (hψB : ∀ y : ℝ × ℝ, ‖ψ y‖ ≤ B) {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (z : ℝ × ℝ) :
    HasDerivAt (fun θ : ℝ => ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * ψ (z - w))
      (∫ w : ℝ × ℝ, UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ₀ w * ψ (z - w)) θ₀ := by
  have hψm : AEStronglyMeasurable (fun w : ℝ × ℝ => ψ (z - w)) (volume : Measure (ℝ × ℝ)) :=
    (hψc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hsmem : Ioo (θ₀ / 2) (2 * θ₀) ∈ 𝓝 θ₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have hF_meas : ∀ᶠ θ in 𝓝 θ₀,
      AEStronglyMeasurable (fun w : ℝ × ℝ => UnforcedLeray.B0284.heatKernel2 θ w * ψ (z - w))
        (volume : Measure (ℝ × ℝ)) := by
    filter_upwards [hsmem] with θ hθ
    exact (UnforcedLeray.B0284.integrable_heatKernel2 (by linarith [hθ.1] : 0 < θ)).aestronglyMeasurable.mul
      hψm
  have hF_int : Integrable (fun w : ℝ × ℝ =>
      UnforcedLeray.B0284.heatKernel2 θ₀ w * ψ (z - w)) :=
    (UnforcedLeray.B0284.integrable_heatKernel2 hθ₀).mul_bdd hψm
      (ae_of_all _ fun w => hψB (z - w))
  have hF'_meas : AEStronglyMeasurable (fun w : ℝ × ℝ =>
      UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ₀ w * ψ (z - w))
      (volume : Measure (ℝ × ℝ)) :=
    (UnforcedLeray.HeatCylinder.integrable_heatKernel2AgeDerivative hθ₀).aestronglyMeasurable.mul
      hψm
  set C : ℝ := 4 * (θ₀⁻¹ ^ 2 + 2 / θ₀) * B with hCdef
  have hbound_int : Integrable (fun w : ℝ × ℝ =>
      C * ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * θ₀) w)) :=
    (UnforcedLeray.HeatCylinder.integrable_one_add_sq_mul_heatKernel2
      (by linarith : (0 : ℝ) < 2 * θ₀)).const_mul C
  have h_bound : ∀ᵐ w ∂(volume : Measure (ℝ × ℝ)), ∀ s ∈ Ioo (θ₀ / 2) (2 * θ₀),
      ‖UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative s w * ψ (z - w)‖ ≤
        C * ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * θ₀) w) := by
    refine ae_of_all _ fun w s hs => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have hage := UnforcedLeray.HeatCylinder.abs_heatKernel2AgeDerivative_le_local hθ₀ hs.1 hs.2 w
    have hpos : 0 ≤ (1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * θ₀) w :=
      mul_nonneg (by positivity)
        (UnforcedLeray.B0284.heatKernel2_nonneg (by linarith : (0 : ℝ) < 2 * θ₀) w)
    have hz : |ψ (z - w)| ≤ B := by simpa [Real.norm_eq_abs] using hψB (z - w)
    calc |UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative s w| * |ψ (z - w)|
        ≤ (4 * (θ₀⁻¹ ^ 2 + 2 / θ₀) * ((1 + w.1 ^ 2 + w.2 ^ 2) *
            UnforcedLeray.B0284.heatKernel2 (2 * θ₀) w)) * B :=
          mul_le_mul hage hz (abs_nonneg _) (mul_nonneg (by positivity) hpos)
      _ = C * ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * θ₀) w) := by
          rw [hCdef]
          ring
  have h_diff : ∀ᵐ w ∂(volume : Measure (ℝ × ℝ)), ∀ s ∈ Ioo (θ₀ / 2) (2 * θ₀),
      HasDerivAt (fun θ : ℝ => UnforcedLeray.B0284.heatKernel2 θ w * ψ (z - w))
        (UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative s w * ψ (z - w)) s := by
    refine ae_of_all _ fun w s hs => ?_
    have hs0 : 0 < s := lt_trans (by linarith) hs.1
    exact (UnforcedLeray.HeatCylinder.hasDerivAt_heatKernel2_age hs0 w).mul_const (ψ (z - w))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure (ℝ × ℝ))) (x₀ := θ₀)
    (s := Ioo (θ₀ / 2) (2 * θ₀))
    (F := fun θ w => UnforcedLeray.B0284.heatKernel2 θ w * ψ (z - w))
    (F' := fun θ w => UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ w * ψ (z - w))
    (bound := fun w => C * ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * θ₀) w))
    hsmem hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  exact key.2

/-! ## The age-derivative identity -/

/-- `∫ (∂_θ K_θ)(w) ψ(z - w) dw = ∫ K_θ(w) (planarLap ψ)(z - w) dw` for `θ > 0`. -/
theorem deqhd_hval {θ : ℝ} (hθ : 0 < θ) {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (z : ℝ × ℝ) :
    ∫ w : ℝ × ℝ, UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ w * ψ (z - w) =
      ∫ w : ℝ × ℝ, deqhdK θ w * planarLap ψ (z - w) := by
  have hθ0 : θ ≠ 0 := hθ.ne'
  have hψ1 : ContDiff ℝ ∞ (fun y : ℝ × ℝ => fderiv ℝ ψ y (1, 0)) :=
    (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  have hψ2 : ContDiff ℝ ∞ (fun y : ℝ × ℝ => fderiv ℝ ψ y (0, 1)) :=
    (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  have hpt : ∀ w : ℝ × ℝ, UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ w * ψ (z - w) =
      (w.1 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * deqhdK θ w * ψ (z - w) +
        (w.2 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * deqhdK θ w * ψ (z - w) := by
    intro w
    unfold UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative
    ring
  have hpl : ∀ w : ℝ × ℝ, deqhdK θ w * planarLap ψ (z - w) =
      deqhdK θ w * fderiv ℝ (fun y : ℝ × ℝ => fderiv ℝ ψ y (1, 0)) (z - w) (1, 0) +
        deqhdK θ w * fderiv ℝ (fun y : ℝ × ℝ => fderiv ℝ ψ y (0, 1)) (z - w) (0, 1) := by
    intro w
    unfold planarLap
    ring
  obtain ⟨B1, hB1⟩ := deqhd_bdd_apply hψ1 (hψc.fderiv_apply ℝ _) ((1 : ℝ), (0 : ℝ))
  obtain ⟨B2, hB2⟩ := deqhd_bdd_apply hψ2 (hψc.fderiv_apply ℝ _) ((0 : ℝ), (1 : ℝ))
  -- `B1` bounds `∂_q ψ₁`, `B2` bounds `∂_η ψ₂`
  have hcx : Continuous (fun w : ℝ × ℝ =>
      fderiv ℝ (fun y : ℝ × ℝ => fderiv ℝ ψ y (1, 0)) (z - w) ((1 : ℝ), (0 : ℝ))) :=
    (deqhd_cont_apply hψ1 ((1 : ℝ), (0 : ℝ))).comp (continuous_const.sub continuous_id)
  have hcy : Continuous (fun w : ℝ × ℝ =>
      fderiv ℝ (fun y : ℝ × ℝ => fderiv ℝ ψ y (0, 1)) (z - w) ((0 : ℝ), (1 : ℝ))) :=
    (deqhd_cont_apply hψ2 ((0 : ℝ), (1 : ℝ))).comp (continuous_const.sub continuous_id)
  have hcψ : Continuous (fun w : ℝ × ℝ => ψ (z - w)) :=
    hψ.continuous.comp (continuous_const.sub continuous_id)
  obtain ⟨Bψ, hBψ⟩ := deqhd_bdd_fn hψ.continuous hψc
  have hbψ : ∀ w : ℝ × ℝ, |ψ (z - w)| ≤ Bψ := fun w => by
    rw [← Real.norm_eq_abs]; exact hBψ (z - w)
  have hbx : ∀ w : ℝ × ℝ,
      |fderiv ℝ (fun y : ℝ × ℝ => fderiv ℝ ψ y (1, 0)) (z - w) ((1 : ℝ), (0 : ℝ))| ≤ B1 :=
    fun w => by rw [← Real.norm_eq_abs]; exact hB1 (z - w)
  have hby : ∀ w : ℝ × ℝ,
      |fderiv ℝ (fun y : ℝ × ℝ => fderiv ℝ ψ y (0, 1)) (z - w) ((0 : ℝ), (1 : ℝ))| ≤ B2 :=
    fun w => by rw [← Real.norm_eq_abs]; exact hB2 (z - w)
  have hI1 : Integrable (fun w : ℝ × ℝ =>
      (w.1 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * deqhdK θ w * ψ (z - w)) :=
    deqhd_int_gauss hθ (by positivity) (by fun_prop) (fun w => deqhd_abs_quad1 hθ w)
      hcψ hbψ
  have hI2 : Integrable (fun w : ℝ × ℝ =>
      (w.2 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * deqhdK θ w * ψ (z - w)) :=
    deqhd_int_gauss hθ (by positivity) (by fun_prop) (fun w => deqhd_abs_quad2 hθ w)
      hcψ hbψ
  have hJ1 : Integrable (fun w : ℝ × ℝ =>
      deqhdK θ w * fderiv ℝ (fun y : ℝ × ℝ => fderiv ℝ ψ y (1, 0)) (z - w) ((1 : ℝ), (0 : ℝ))) :=
    deqhd_int_K hθ hcx hbx
  have hJ2 : Integrable (fun w : ℝ × ℝ =>
      deqhdK θ w * fderiv ℝ (fun y : ℝ × ℝ => fderiv ℝ ψ y (0, 1)) (z - w) ((0 : ℝ), (1 : ℝ))) :=
    deqhd_int_K hθ hcy hby
  have hX := deqhd_x_ibp hθ hψ hψc z
  have hY := deqhd_y_ibp hθ hψ hψc z
  simp only [hpt, hpl]
  rw [integral_add hI1 hI2, integral_add hJ1 hJ2, hX, hY]

/-! ## The leaf -/

theorem deqHeatDeriv : DeqHeatDeriv := by
  intro ψ hψ hψc z θ hθ
  have hψc0 : Continuous ψ := hψ.continuous
  obtain ⟨B, hB⟩ := deqhd_bdd_fn hψc0 hψc
  have key := deqhd_theta_hasDerivAt hψc0 hB hθ z
  have hev : (fun θ' : ℝ => ∫ w : ℝ × ℝ, flatHeatKernel θ' w * ψ (z - w)) =ᶠ[𝓝 θ]
      (fun θ' : ℝ => ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ' w * ψ (z - w)) := by
    filter_upwards [Ioi_mem_nhds hθ] with θ' hθ'
    simp only [flatHeat_kernel_eq (show (0 : ℝ) < θ' from hθ')]
  have h2 := key.congr_of_eventuallyEq hev
  have hv : (∫ w : ℝ × ℝ, flatHeatKernel θ w * planarLap ψ (z - w)) =
      ∫ w : ℝ × ℝ, UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ w * ψ (z - w) := by
    simp only [flatHeat_kernel_eq hθ]
    exact (deqhd_hval hθ hψ hψc z).symm
  rw [hv]
  exact h2

end UnforcedLeray.Short.IIb
