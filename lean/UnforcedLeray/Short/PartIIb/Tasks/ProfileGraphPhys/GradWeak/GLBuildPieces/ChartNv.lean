import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_1_3

/-!
# Part II-b, task `PartII-b:T10/7/1/1/3/4` (`GLBuildPieces/ChartNv`): the ring lift of the chart profile

Source of record: `the November 2 reference manuscript` lines 1912-1921 (chart 1639-1668).

Target: `gl_chartNv : UnforcedLeray.Short.IIb.GLChartNv`.

Proof outline. Off the axis, with `R = ε⁻¹`, `s = age R y = (R/ϱ)^2 > 0`:
* `invChart ε (chart R τ y) = (τ, mer y)` (log algebra, `√s = ε⁻¹/ϱ`).
* `chartProf ε A B (chart R τ y) = s⁻¹ • !₂[A(τ, mer y), B(τ, mer y)]`.
* `sqrtS (chartProf ε A B) (chart R τ y) = (√s)⁻¹ • !₂[A, B]` (since `√s · s⁻¹ = (√s)⁻¹`).
* Real and imaginary meridional parts: `reM`, `imM` pull the real scalar `(√s)⁻¹` out; the lift
  `Axi.Nv` multiplies by `√s` and `Axi.frameL_apply` gives `Re A · e_r + Re B · e_3`
  (resp. `Im`), and `NvC` recombines them as `A e_r + B e_3` with complex coefficients.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

namespace ChartNvHelp

/-- The inverse chart undoes `Axi.chart ε⁻¹` off the axis. -/
theorem invChart_chart {ε : ℝ} (hε : 0 < ε) {τ : ℝ} {y : Space} (hy : y ∉ Axi.axis) :
    invChart ε (Axi.chart ε⁻¹ τ y) = (τ, Axi.mer y) := by
  have hϱ : 0 < Axi.ϱ y := Axi.ϱ_pos hy
  have hs : Axi.age ε⁻¹ y = (ε⁻¹ / Axi.ϱ y) ^ 2 := by
    rw [Axi.age, div_pow]
  have hsq : Real.sqrt (Axi.age ε⁻¹ y) = ε⁻¹ / Axi.ϱ y := by
    rw [hs]
    exact Real.sqrt_sq (div_nonneg (inv_nonneg.2 hε.le) hϱ.le)
  have hεi : ε * ε⁻¹ = 1 := mul_inv_cancel₀ hε.ne'
  have hϱne : Axi.ϱ y ≠ 0 := hϱ.ne'
  unfold invChart
  simp only [Axi.chart, Axi.mer]
  rw [hsq]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [Axi.phase]
    linear_combination (τ - Real.log (Axi.age ε⁻¹ y)) * hεi
  · field_simp
  · simp only [Axi.trans]
    field_simp

/-- The profile `chartProf` at a chart point off the axis. -/
theorem chartProf_chart {ε : ℝ} (hε : 0 < ε) (A B : ℝ × (ℝ × ℝ) → ℂ) {τ : ℝ} {y : Space}
    (hy : y ∉ Axi.axis) :
    chartProf ε A B (Axi.chart ε⁻¹ τ y) =
      ((Axi.age ε⁻¹ y : ℝ) : ℂ)⁻¹ • (!₂[A (τ, Axi.mer y), B (τ, Axi.mer y)] : CMerid) := by
  have hϱ : 0 < Axi.ϱ y := Axi.ϱ_pos hy
  have hpos : 0 < (Axi.chart ε⁻¹ τ y).1 := by
    show 0 < Axi.age ε⁻¹ y
    rw [Axi.age]
    exact div_pos (pow_pos (inv_pos.2 hε) 2) (pow_pos hϱ 2)
  unfold chartProf
  rw [if_pos hpos, invChart_chart hε hy]
  rfl

/-- The scalar identity `√s · s⁻¹ = (√s)⁻¹` for `s > 0`, in `ℂ`. -/
theorem sqrt_mul_inv_cast {s : ℝ} (hs : 0 < s) :
    ((Real.sqrt s : ℝ) : ℂ) * ((s : ℝ) : ℂ)⁻¹ = (((Real.sqrt s)⁻¹ : ℝ) : ℂ) := by
  have hr : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have h2 : (s : ℂ) = ((Real.sqrt s : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hs.le]
  have hC : ((Real.sqrt s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [h2]
  push_cast
  field_simp

/-- `sqrtS` of the chart profile at a chart point off the axis. -/
theorem sqrtS_chartProf {ε : ℝ} (hε : 0 < ε) (A B : ℝ × (ℝ × ℝ) → ℂ) {τ : ℝ} {y : Space}
    (hy : y ∉ Axi.axis) :
    sqrtS (chartProf ε A B) (Axi.chart ε⁻¹ τ y) =
      (((Real.sqrt (Axi.age ε⁻¹ y))⁻¹ : ℝ) : ℂ) • (!₂[A (τ, Axi.mer y), B (τ, Axi.mer y)] : CMerid) := by
  have hϱ : 0 < Axi.ϱ y := Axi.ϱ_pos hy
  have hs : 0 < Axi.age ε⁻¹ y := by
    rw [Axi.age]
    exact div_pos (pow_pos (inv_pos.2 hε) 2) (pow_pos hϱ 2)
  show (Real.sqrt (Axi.age ε⁻¹ y) : ℂ) • chartProf ε A B (Axi.chart ε⁻¹ τ y) = _
  rw [chartProf_chart hε A B hy, smul_smul, sqrt_mul_inv_cast hs]

/-- `reM` and `imM` pull a real scalar out of a complex scalar multiple. -/
theorem reM_ofReal_smul (c : ℝ) (w : CMerid) : reM (((c : ℝ) : ℂ) • w) = c • reM w := by
  ext i
  simp [reM, Complex.re_ofReal_mul]

theorem imM_ofReal_smul (c : ℝ) (w : CMerid) : imM (((c : ℝ) : ℂ) • w) = c • imM w := by
  ext i
  simp [imM, Complex.im_ofReal_mul]

/-- The real-part ring lift at a chart point. -/
theorem nv_reM {ε : ℝ} (hε : 0 < ε) (A B : ℝ × (ℝ × ℝ) → ℂ) {τ : ℝ} {y : Space}
    (hy : y ∉ Axi.axis) :
    Axi.Nv ε⁻¹ (fun z => reM (sqrtS (chartProf ε A B) z)) τ y =
      (A (τ, Axi.mer y)).re • Axi.eR y + (B (τ, Axi.mer y)).re • Axi.e3 := by
  have hϱ : 0 < Axi.ϱ y := Axi.ϱ_pos hy
  have hs : 0 < Axi.age ε⁻¹ y := by
    rw [Axi.age]
    exact div_pos (pow_pos (inv_pos.2 hε) 2) (pow_pos hϱ 2)
  have hσ : 0 < Real.sqrt (Axi.age ε⁻¹ y) := Real.sqrt_pos.2 hs
  simp only [Axi.Nv]
  rw [sqrtS_chartProf hε A B hy, reM_ofReal_smul, map_smul, Axi.frameL_apply, smul_smul,
    mul_inv_cancel₀ hσ.ne', one_smul]
  simp [reM]

/-- The imaginary-part ring lift at a chart point. -/
theorem nv_imM {ε : ℝ} (hε : 0 < ε) (A B : ℝ × (ℝ × ℝ) → ℂ) {τ : ℝ} {y : Space}
    (hy : y ∉ Axi.axis) :
    Axi.Nv ε⁻¹ (fun z => imM (sqrtS (chartProf ε A B) z)) τ y =
      (A (τ, Axi.mer y)).im • Axi.eR y + (B (τ, Axi.mer y)).im • Axi.e3 := by
  have hϱ : 0 < Axi.ϱ y := Axi.ϱ_pos hy
  have hs : 0 < Axi.age ε⁻¹ y := by
    rw [Axi.age]
    exact div_pos (pow_pos (inv_pos.2 hε) 2) (pow_pos hϱ 2)
  have hσ : 0 < Real.sqrt (Axi.age ε⁻¹ y) := Real.sqrt_pos.2 hs
  simp only [Axi.Nv]
  rw [sqrtS_chartProf hε A B hy, imM_ofReal_smul, map_smul, Axi.frameL_apply, smul_smul,
    mul_inv_cancel₀ hσ.ne', one_smul]
  simp [imM]

/-- `realC` is `ℝ`-bilinear in the sense needed for the ring lift. -/
theorem realC_lin (a b : ℝ) (x z : Space) :
    B0412.realC (a • x + b • z) = (a : ℂ) • B0412.realC x + (b : ℂ) • B0412.realC z := by
  ext i
  simp only [B0412.realC_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Complex.ofReal_add, Complex.ofReal_mul]

end ChartNvHelp

open ChartNvHelp

/-- **(CB1)** The ring lift of the chart profile recovers `A e_r + B e_3` off the axis. -/
theorem gl_chartNv : UnforcedLeray.Short.IIb.GLChartNv := by
  intro ε A B τ y hε hy
  unfold NvC
  dsimp only
  rw [nv_reM hε A B hy, nv_imM hε A B hy, realC_lin, realC_lin]
  conv_rhs => rw [← Complex.re_add_im (A (τ, Axi.mer y)), ← Complex.re_add_im (B (τ, Axi.mer y))]
  module

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.gl_chartNv
