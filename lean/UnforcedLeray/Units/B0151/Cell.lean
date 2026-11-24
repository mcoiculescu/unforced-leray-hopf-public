import UnforcedLeray.Units.B0151.OneDim
import UnforcedLeray.Analysis.GaussianVortex.PlanarDefs

/-!
# B0151, part 2: the cylinder cell, slices and classical partial derivatives

Blueprint unit **B0151** (`unlabeled:2291`), `paper/main.tex` lines 2291–2294.

A field on the cylinder `ℝ × ℝ/Lℤ` (manuscript order: the periodic coordinate `q` first, the
axial coordinate `η` second, as in `UnforcedLeray.CylinderNS`) is a field on the plane with
`h (q + L, η) = h (q, η)`. Its `L^p` norms are taken over one cell `(0, L] × ℝ` with
Lebesgue measure, `cellMeasure L`. (This is the cell `oneCell` and the translation law `shift`
of the draft `UnforcedLeray.Analysis.CylinderNS.Defs`, written out here so that this unit does
not depend on that uncompiled draft.) Derivatives are the
actual Cartesian partial derivatives `GaussianVortex.partialX` (`∂_q`) and
`GaussianVortex.partialY` (`∂_η`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal ContDiff

namespace UnforcedLeray.B0151

open UnforcedLeray.GaussianVortex (partialX partialY)

/-- Lebesgue measure on one cell `(0, L] × ℝ` of the cylinder of period `L`. -/
def cellMeasure (L : ℝ) : Measure (ℝ × ℝ) := volume.restrict (Ioc 0 L ×ˢ univ)

/-- A field on the plane is a field on the cylinder of period `L`. -/
def IsPeriodicQ (L : ℝ) (h : ℝ × ℝ → ℝ) : Prop := ∀ q η, h (q + L, η) = h (q, η)

theorem cellMeasure_eq_prod (L : ℝ) :
    cellMeasure L = (volume.restrict (Ioc 0 L)).prod (volume : Measure ℝ) := by
  rw [cellMeasure, Measure.volume_eq_prod, ← Measure.prod_restrict,
    Measure.restrict_univ]

instance (L : ℝ) : SFinite (cellMeasure L) := by
  rw [cellMeasure]; infer_instance

theorem lintegral_cell (L : ℝ) {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂cellMeasure L = ∫⁻ q in Ioc 0 L, ∫⁻ η, f (q, η) := by
  rw [cellMeasure_eq_prod, lintegral_prod _ hf.aemeasurable]

theorem lintegral_cell_symm (L : ℝ) {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂cellMeasure L = ∫⁻ η, ∫⁻ q in Ioc 0 L, f (q, η) := by
  rw [cellMeasure_eq_prod, lintegral_prod_symm _ hf.aemeasurable]

/-- Almost every `η`-line of an integrable field on the cell is integrable. -/
theorem ae_integrable_slice {L : ℝ} {f : ℝ × ℝ → ℝ} (hf : Integrable f (cellMeasure L)) :
    ∀ᵐ q ∂(volume.restrict (Ioc 0 L)), Integrable (fun η => f (q, η)) := by
  rw [cellMeasure_eq_prod] at hf
  exact hf.prod_right_ae

/-- Cauchy–Schwarz on the cell. -/
theorem lintegral_enorm_mul_le {μ : Measure (ℝ × ℝ)} {f g : ℝ × ℝ → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    ∫⁻ z, ‖f z‖ₑ * ‖g z‖ₑ ∂μ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := by
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (p := 2) (q := 2) (r := 1) hf hg
    (fun a b : ℝ => a * b) 1 (ae_of_all _ fun z => by simp [norm_mul])
  rw [eLpNorm_one_eq_lintegral_enorm] at h
  simpa [enorm_mul] using h

theorem enorm_sq_eq (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal |x ^ 2| := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg x), abs_pow]

theorem lintegral_enorm_sq_eq {μ : Measure (ℝ × ℝ)} (f : ℝ × ℝ → ℝ) :
    ∫⁻ z, ‖f z‖ₑ ^ 2 ∂μ = eLpNorm f 2 μ ^ 2 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ) (p := 2) (by norm_num)
  have e2 : ((2 : NNReal) : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  simp only [e2, ENNReal.rpow_natCast, ENNReal.coe_ofNat] at h
  exact h.symm

/-! ### Classical partial derivatives -/

theorem hasDerivAt_sliceX {h : ℝ × ℝ → ℝ} (hd : Differentiable ℝ h) (x y : ℝ) :
    HasDerivAt (fun x' => h (x', y)) (partialX h (x, y)) x := by
  have : DifferentiableAt ℝ (fun x' : ℝ => h (x', y)) x :=
    (hd (x, y)).comp x (differentiableAt_id.prodMk (differentiableAt_const y))
  exact this.hasDerivAt

theorem hasDerivAt_sliceY {h : ℝ × ℝ → ℝ} (hd : Differentiable ℝ h) (x y : ℝ) :
    HasDerivAt (fun y' => h (x, y')) (partialY h (x, y)) y := by
  have : DifferentiableAt ℝ (fun y' : ℝ => h (x, y')) y :=
    (hd (x, y)).comp y ((differentiableAt_const x).prodMk differentiableAt_id)
  exact this.hasDerivAt

theorem partialX_eq_fderiv {h : ℝ × ℝ → ℝ} (hd : Differentiable ℝ h) (z : ℝ × ℝ) :
    partialX h z = fderiv ℝ h z (1, 0) := by
  have h1 : HasDerivAt (fun x' : ℝ => h (x', z.2)) (fderiv ℝ h (z.1, z.2) (1, 0)) z.1 := by
    have := (hd (z.1, z.2)).hasFDerivAt.comp_hasDerivAt z.1
      ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))
    exact this
  exact h1.deriv

theorem partialY_eq_fderiv {h : ℝ × ℝ → ℝ} (hd : Differentiable ℝ h) (z : ℝ × ℝ) :
    partialY h z = fderiv ℝ h z (0, 1) := by
  have h1 : HasDerivAt (fun y' : ℝ => h (z.1, y')) (fderiv ℝ h (z.1, z.2) (0, 1)) z.2 := by
    have := (hd (z.1, z.2)).hasFDerivAt.comp_hasDerivAt z.2
      ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))
    exact this
  exact h1.deriv

theorem contDiff_partialX {n : WithTop ℕ∞} {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ (n + 1) h) :
    ContDiff ℝ n (partialX h) := by
  have hd : Differentiable ℝ h := hh.differentiable (by simp)
  rw [show partialX h = fun z => fderiv ℝ h z (1, 0) from funext (partialX_eq_fderiv hd)]
  exact (hh.fderiv_right le_rfl).clm_apply contDiff_const

theorem contDiff_partialY {n : WithTop ℕ∞} {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ (n + 1) h) :
    ContDiff ℝ n (partialY h) := by
  have hd : Differentiable ℝ h := hh.differentiable (by simp)
  rw [show partialY h = fun z => fderiv ℝ h z (0, 1) from funext (partialY_eq_fderiv hd)]
  exact (hh.fderiv_right le_rfl).clm_apply contDiff_const

theorem continuous_partialX {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ 1 h) :
    Continuous (partialX h) :=
  (contDiff_partialX (n := 0) (by simpa using hh)).continuous

theorem continuous_partialY {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ 1 h) :
    Continuous (partialY h) :=
  (contDiff_partialY (n := 0) (by simpa using hh)).continuous

theorem IsPeriodicQ.slice {L : ℝ} {h : ℝ × ℝ → ℝ} (hp : IsPeriodicQ L h) (y : ℝ) :
    Function.Periodic (fun x => h (x, y)) L := fun x => hp x y

theorem IsPeriodicQ.partialX {L : ℝ} {h : ℝ × ℝ → ℝ} (hp : IsPeriodicQ L h) :
    IsPeriodicQ L (partialX h) := by
  intro q η
  change deriv (fun x => h (x, η)) (q + L) = deriv (fun x => h (x, η)) q
  have e : (fun x => h (x + L, η)) = fun x => h (x, η) := funext fun x => hp x η
  rw [← deriv_comp_add_const, e]

theorem IsPeriodicQ.partialY {L : ℝ} {h : ℝ × ℝ → ℝ} (hp : IsPeriodicQ L h) :
    IsPeriodicQ L (partialY h) := by
  intro q η
  change deriv (fun y => h (q + L, y)) η = deriv (fun y => h (q, y)) η
  have e : (fun y => h (q + L, y)) = fun y => h (q, y) := funext fun y => hp q y
  rw [e]

/-- `∂_q (h²) = 2 h ∂_q h` along a line. -/
theorem hasDerivAt_sq_sliceX {h : ℝ × ℝ → ℝ} (hd : Differentiable ℝ h) (x y : ℝ) :
    HasDerivAt (fun x' => h (x', y) ^ 2) (2 * h (x, y) * partialX h (x, y)) x := by
  have h1 := (hasDerivAt_sliceX hd x y).mul (hasDerivAt_sliceX hd x y)
  have e : ((fun x' => h (x', y)) * fun x' => h (x', y)) = fun x' => h (x', y) ^ 2 :=
    funext fun _ => (sq _).symm
  rw [e] at h1
  exact h1.congr_deriv (by ring)

/-- `∂_η (h²) = 2 h ∂_η h` along a line. -/
theorem hasDerivAt_sq_sliceY {h : ℝ × ℝ → ℝ} (hd : Differentiable ℝ h) (x y : ℝ) :
    HasDerivAt (fun y' => h (x, y') ^ 2) (2 * h (x, y) * partialY h (x, y)) y := by
  have h1 := (hasDerivAt_sliceY hd x y).mul (hasDerivAt_sliceY hd x y)
  have e : ((fun y' => h (x, y')) * fun y' => h (x, y')) = fun y' => h (x, y') ^ 2 :=
    funext fun _ => (sq _).symm
  rw [e] at h1
  exact h1.congr_deriv (by ring)

end UnforcedLeray.B0151
