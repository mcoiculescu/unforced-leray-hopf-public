import UnforcedLeray.Lib.Axisymmetric.Cylindrical
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# AX03 (chart and chain rules): the similarity ring chart `y ↦ (s, ξ, η)`


§5 Layer 3, target AX03 (`Axi/RingChart.lean`), chain-rule part; the measure part is in
`Lib/Axisymmetric/RingMeasure.lean`. Blueprint units served: B0186 (`eq:m3-ring-lift`,
tex 2070–2098), B0197 (`eq:st18-t00198`, tex 2994–3003), B0203 (`eq:st18-t00205`,
tex 3082–3092), B0443 (tex 3734–3761).

The similarity chart of `eq:m3-ring-lift` (tex 2073–2075), with `R = ε⁻¹`:
`s = R²/ϱ²`, `ξ = Rτ/2 − (R/2) log s`, `η = R y₃/ϱ` (`age`, `phase`, `trans`). A profile
`F(s, (ξ, η))` composed with the chart is differentiated by the rules (`y` off the axis,
`R > 0`, `F` differentiable at the chart point):
* `∂_ρ = √s (∂_ξ − ε K)` with `K = 2s∂_s + η∂_η` (`radial_chain`; cf. tex 3755–3756,
  `∂_ρ(√s b) = s Q_ε b`, and B0184's `∂_r = a_r D_ε`);
* `∂_z = √s ∂_η` (`axial_chain`; tex 3757);
* `∂_τ = (R/2) ∂_ξ` (`phase_chain`);
* `T₀ = ∂_τ − (1/2) y·∇ = s∂_s` (`T0_chain`; tex 3754, `T₀(√s b) = √s(S + 1/2) b`).

Here `∂_ρ G(y) := DG(y) e_r(y)`, `∂_z G(y) := DG(y) e₃` and `y·∇ G(y) := DG(y) y`, with the
Fréchet derivative on `Space`. The profile variables are ordered `(s, (ξ, η))`, the layout of
`ageμ c a = (ds-weighted) × avgμ c` in the scoping note (AX04).

Junk values: on the axis `ϱ = 0` and `age = R²/0 = 0`, `log 0 = 0`; all derivative statements
assume `y ∉ axis`. `√(age R y) = R/ϱ(y)` needs `R > 0` (`sqrt_age`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real
open scoped ENNReal

namespace UnforcedLeray.Axi

/-- The age `s = R²/ϱ²` (tex 2073). -/
def age (R : ℝ) (y : Space) : ℝ := R ^ 2 / ϱ y ^ 2

/-- The transverse coordinate `η = R y₃/ϱ` (tex 2074). -/
def trans (R : ℝ) (y : Space) : ℝ := R * y 2 / ϱ y

/-- The phase (log-radius) coordinate `ξ = Rτ/2 − (R/2) log s` (tex 2073). -/
def phase (R τ : ℝ) (y : Space) : ℝ := R * τ / 2 - (R / 2) * Real.log (age R y)

/-- The similarity ring chart `y ↦ (s, (ξ, η))` at phase time `τ`. -/
def chart (R τ : ℝ) (y : Space) : ℝ × (ℝ × ℝ) := (age R y, (phase R τ y, trans R y))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Profile partial derivative `∂_s`. -/
def dS (F : ℝ × (ℝ × ℝ) → E) (p : ℝ × (ℝ × ℝ)) : E := fderiv ℝ F p (1, (0, 0))
/-- Profile partial derivative `∂_ξ` (written `∂_q` in the scoping note). -/
def dQ (F : ℝ × (ℝ × ℝ) → E) (p : ℝ × (ℝ × ℝ)) : E := fderiv ℝ F p (0, (1, 0))
/-- Profile partial derivative `∂_η`. -/
def dEta (F : ℝ × (ℝ × ℝ) → E) (p : ℝ × (ℝ × ℝ)) : E := fderiv ℝ F p (0, (0, 1))

/-- Linearity on profile space: `L(a, (b, c)) = a L e_s + b L e_ξ + c L e_η`. -/
theorem clm_triple (L : ℝ × (ℝ × ℝ) →L[ℝ] E) (a b c : ℝ) :
    L (a, (b, c)) = a • L (1, (0, 0)) + b • L (0, (1, 0)) + c • L (0, (0, 1)) := by
  have h : ((a, (b, c)) : ℝ × (ℝ × ℝ)) = a • ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) +
      b • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) + c • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) := by simp
  rw [h, map_add, map_add, map_smul, map_smul, map_smul]

/-! ### Elementary identities -/

theorem age_pos {R : ℝ} (hR : R ≠ 0) {y : Space} (hy : y ∉ axis) : 0 < age R y :=
  div_pos (lt_of_le_of_ne (sq_nonneg R) (Ne.symm (pow_ne_zero 2 hR))) (pow_pos (ϱ_pos hy) 2)

/-- `√s = R/ϱ` (tex 2995: `r_y = R/√s`). -/
theorem sqrt_age {R : ℝ} (hR : 0 < R) {y : Space} (hy : y ∉ axis) :
    √(age R y) = R / ϱ y := by
  rw [age, ← div_pow, Real.sqrt_sq (div_pos hR (ϱ_pos hy)).le]

theorem e3_two : e3 2 = 1 := by simp

theorem ϱD_eR {y : Space} (hy : y ∉ axis) : ϱD y (eR y) = 1 := by
  rw [ϱD_apply, eR_apply_zero, eR_apply_one]
  linear_combination eR_sq_sum hy

theorem ϱD_e3 (y : Space) : ϱD y e3 = 0 := by
  rw [ϱD_apply]
  simp

theorem ϱD_self {y : Space} (hy : y ∉ axis) : ϱD y y = ϱ y := by
  rw [ϱD_apply, div_eq_iff (ϱ_ne_zero hy)]
  linear_combination (-1 : ℝ) * ϱ_sq y

/-! ### The derivative of the chart -/

/-- `Ds = −(2R²/ϱ³) Dϱ`. -/
def ageD (R : ℝ) (y : Space) : Space →L[ℝ] ℝ := (-(2 * R ^ 2 / ϱ y ^ 3)) • ϱD y

/-- `Dξ = (R/ϱ) Dϱ`. -/
def phaseD (R : ℝ) (y : Space) : Space →L[ℝ] ℝ := (R / ϱ y) • ϱD y

/-- `Dη = (R/ϱ) dy₃ − (R y₃/ϱ²) Dϱ`. -/
def transD (R : ℝ) (y : Space) : Space →L[ℝ] ℝ :=
  (R / ϱ y) • (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ) - (R * y 2 / ϱ y ^ 2) • ϱD y

/-- The derivative of the chart `y ↦ (s, (ξ, η))`. -/
def chartD (R : ℝ) (y : Space) : Space →L[ℝ] ℝ × (ℝ × ℝ) :=
  (ageD R y).prod ((phaseD R y).prod (transD R y))

theorem chartD_apply (R : ℝ) (y v : Space) :
    chartD R y v = (-(2 * R ^ 2 / ϱ y ^ 3) * ϱD y v,
      (R / ϱ y * ϱD y v, R / ϱ y * v 2 - R * y 2 / ϱ y ^ 2 * ϱD y v)) := by
  simp only [chartD, ageD, phaseD, transD, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, smul_eq_mul,
    EuclideanSpace.coe_proj]

theorem hasDerivAt_sq_div (R : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun x : ℝ => R ^ 2 / x ^ 2) (-(2 * R ^ 2 / r ^ 3)) r := by
  have h := (hasDerivAt_const r (R ^ 2)).fun_div (hasDerivAt_pow 2 r) (pow_ne_zero 2 hr)
  refine h.congr_deriv ?_
  rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat, zero_mul, zero_sub, neg_div,
    neg_inj, div_eq_div_iff (pow_ne_zero 2 (pow_ne_zero 2 hr)) (pow_ne_zero 3 hr)]
  ring

theorem hasFDerivAt_age (R : ℝ) {y : Space} (hy : y ∉ axis) :
    HasFDerivAt (age R) (ageD R y) y :=
  (hasDerivAt_sq_div R (ϱ_ne_zero hy)).comp_hasFDerivAt y (hasFDerivAt_ϱ hy)

theorem hasFDerivAt_phase {R : ℝ} (hR : R ≠ 0) (τ : ℝ) {y : Space} (hy : y ∉ axis) :
    HasFDerivAt (phase R τ) (phaseD R y) y := by
  have hρ := ϱ_ne_zero hy
  have hlog := (hasFDerivAt_age R hy).log (age_pos hR hy).ne'
  have h := (hlog.const_mul (R / 2)).const_sub (R * τ / 2)
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, ageD,
    phaseD, age]
  field_simp

theorem hasFDerivAt_trans (R : ℝ) {y : Space} (hy : y ∉ axis) :
    HasFDerivAt (trans R) (transD R y) y := by
  have hρ := ϱ_ne_zero hy
  have h2 : HasFDerivAt (fun x : Space => x 2)
      (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ) y :=
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt
  have hinv : HasFDerivAt (fun x => (ϱ x)⁻¹) ((-(ϱ y ^ 2)⁻¹) • ϱD y) y :=
    (hasDerivAt_inv hρ).comp_hasFDerivAt y (hasFDerivAt_ϱ hy)
  have h := (h2.const_mul R).fun_mul hinv
  have he : trans R = fun x => R * x 2 * (ϱ x)⁻¹ := funext fun x => div_eq_mul_inv _ _
  rw [he]
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, transD, EuclideanSpace.coe_proj]
  field_simp
  ring

theorem hasFDerivAt_chart {R : ℝ} (hR : R ≠ 0) (τ : ℝ) {y : Space} (hy : y ∉ axis) :
    HasFDerivAt (chart R τ) (chartD R y) y :=
  (hasFDerivAt_age R hy).prodMk ((hasFDerivAt_phase hR τ hy).prodMk (hasFDerivAt_trans R hy))

/-- Derivative of a profile composed with the chart. -/
theorem fderiv_comp_chart_apply {F : ℝ × (ℝ × ℝ) → E} {R τ : ℝ} (hR : R ≠ 0) {y : Space}
    (hy : y ∉ axis) (hF : DifferentiableAt ℝ F (chart R τ y)) (v : Space) :
    fderiv ℝ (fun x => F (chart R τ x)) y v = fderiv ℝ F (chart R τ y) (chartD R y v) := by
  have hc : HasFDerivAt (fun x => F (chart R τ x))
      ((fderiv ℝ F (chart R τ y)).comp (chartD R y)) y :=
    hF.hasFDerivAt.comp y (hasFDerivAt_chart hR τ hy)
  rw [hc.fderiv]
  rfl

/-! ### The chain rules -/

/-- **AX03 `radial_chain`.** `∂_ρ (F ∘ chart) = √s (∂_ξ F − ε (2s ∂_s F + η ∂_η F))`, `ε = R⁻¹`
(tex 2073–2075; the scalar form of tex 3755–3756 and of B0184's `∂_r = a_r D_ε`). -/
theorem radial_chain {F : ℝ × (ℝ × ℝ) → E} {R τ : ℝ} (hR : 0 < R) {y : Space} (hy : y ∉ axis)
    (hF : DifferentiableAt ℝ F (chart R τ y)) :
    fderiv ℝ (fun x => F (chart R τ x)) y (eR y) =
      √(age R y) • (dQ F (chart R τ y) -
        R⁻¹ • ((2 * age R y) • dS F (chart R τ y) + trans R y • dEta F (chart R τ y))) := by
  have hρ := ϱ_ne_zero hy
  have hR0 := hR.ne'
  rw [fderiv_comp_chart_apply hR0 hy hF, chartD_apply, ϱD_eR hy, eR_apply_two, clm_triple,
    sqrt_age hR hy]
  simp only [dS, dQ, dEta, age, trans]
  match_scalars <;> field_simp <;> ring

/-- **AX03 `axial_chain`.** `∂_z (F ∘ chart) = √s ∂_η F` (tex 3757). -/
theorem axial_chain {F : ℝ × (ℝ × ℝ) → E} {R τ : ℝ} (hR : 0 < R) {y : Space} (hy : y ∉ axis)
    (hF : DifferentiableAt ℝ F (chart R τ y)) :
    fderiv ℝ (fun x => F (chart R τ x)) y e3 = √(age R y) • dEta F (chart R τ y) := by
  have hρ := ϱ_ne_zero hy
  rw [fderiv_comp_chart_apply hR.ne' hy hF, chartD_apply, ϱD_e3, e3_two, clm_triple,
    sqrt_age hR hy]
  simp only [dEta]
  match_scalars <;> field_simp <;> ring

/-- The chart moves only in `ξ` along the phase time: `∂_τ chart = (0, (R/2, 0))`. -/
theorem hasDerivAt_chart_time (R τ : ℝ) (y : Space) :
    HasDerivAt (fun t => chart R t y) ((0 : ℝ), ((R / 2 : ℝ), (0 : ℝ))) τ := by
  have h1 : HasDerivAt (fun t : ℝ => R * t / 2 - (R / 2) * Real.log (age R y)) (R / 2) τ := by
    have := (((hasDerivAt_id' τ).const_mul R).div_const 2).sub_const
      ((R / 2) * Real.log (age R y))
    simpa using this
  exact (hasDerivAt_const τ (age R y)).prodMk (h1.prodMk (hasDerivAt_const τ (trans R y)))

/-- **AX03 `phase_chain`.** `∂_τ (F ∘ chart) = (R/2) ∂_ξ F`. -/
theorem phase_chain {F : ℝ × (ℝ × ℝ) → E} {R τ : ℝ} (y : Space)
    (hF : DifferentiableAt ℝ F (chart R τ y)) :
    HasDerivAt (fun t => F (chart R t y)) ((R / 2) • dQ F (chart R τ y)) τ := by
  have h : HasDerivAt (fun t => F (chart R t y))
      (fderiv ℝ F (chart R τ y) ((0 : ℝ), ((R / 2 : ℝ), (0 : ℝ)))) τ :=
    hF.hasFDerivAt.comp_hasDerivAt τ (hasDerivAt_chart_time R τ y)
  convert h using 1
  rw [clm_triple, dQ]
  module

theorem deriv_phase_chain {F : ℝ × (ℝ × ℝ) → E} {R τ : ℝ} (y : Space)
    (hF : DifferentiableAt ℝ F (chart R τ y)) :
    deriv (fun t => F (chart R t y)) τ = (R / 2) • dQ F (chart R τ y) :=
  (phase_chain y hF).deriv

/-- **AX03 `T0_chain`.** The similarity transport `T₀ = ∂_τ − (1/2) y·∇` acts on profiles as
`s ∂_s` (tex 3754: `T₀(√s b) = √s (S + 1/2) b` with `S = s∂_s`). -/
theorem T0_chain {F : ℝ × (ℝ × ℝ) → E} {R τ : ℝ} (hR : R ≠ 0) {y : Space} (hy : y ∉ axis)
    (hF : DifferentiableAt ℝ F (chart R τ y)) :
    deriv (fun t => F (chart R t y)) τ - (1 / 2 : ℝ) • fderiv ℝ (fun x => F (chart R τ x)) y y =
      age R y • dS F (chart R τ y) := by
  have hρ := ϱ_ne_zero hy
  rw [deriv_phase_chain y hF, fderiv_comp_chart_apply hR hy hF, chartD_apply, ϱD_self hy,
    clm_triple]
  simp only [dS, dQ, age]
  match_scalars <;> field_simp <;> ring

/-- **AX08 `phase_shift`** (critic correction 3 keeps only this part of AX08 in Wave 1).
One phase period `P = 2c/R` shifts the phase coordinate by one cell: `ξ(τ + P) = ξ(τ) + c`
(tex 2075–2078: the phase period is `P = 2εc`). -/
theorem phase_shift {R c P : ℝ} (hR : R ≠ 0) (hP : P = 2 * c / R) (τ : ℝ) (y : Space) :
    phase R (τ + P) y = phase R τ y + c := by
  subst hP
  unfold phase
  field_simp
  ring

/-- The chart is `P`-periodic in `τ` up to the cell shift `ξ ↦ ξ + c`. -/
theorem chart_add_period {R c P : ℝ} (hR : R ≠ 0) (hP : P = 2 * c / R) (τ : ℝ) (y : Space) :
    chart R (τ + P) y = (age R y, (phase R τ y + c, trans R y)) := by
  rw [chart, phase_shift hR hP]

end UnforcedLeray.Axi
