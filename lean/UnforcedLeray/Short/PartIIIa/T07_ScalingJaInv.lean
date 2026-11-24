import UnforcedLeray.Short.PartIIIa.Targets

/-!
# T07: scaling bound for `J_a⁻¹` (SP 2982-2986)

Proves `UnforcedLeray.Short.IIIa.scalingJaInv` (the `Prop` `ScalingJaInv` of `Targets.lean`):
for `m ≥ 0`, `a ≥ 1`, `d > 0` and measurable `f`,
`xNorm d m (JscaleInv a f) ≤ ENNReal.ofReal (a ^ (3/2)) * xNorm (d * √a) m f`.

Proof, by the change of variables `y ↦ √a • y`:
* `‖JscaleInv a f y‖ₑ² = ofReal (a⁴) * ‖f (√a • y)‖ₑ²`, since `JscaleInv a f y = a² f (√a • y)`.
* `jb y ≤ jb (√a • y)` for `a ≥ 1`, so `⟨y⟩^{2m} ≤ ⟨√a • y⟩^{2m}` for `m ≥ 0`; also
  `y ∈ cell d ↔ √a • y ∈ cell (d √a)`.
* Hence the cell integral of `‖JscaleInv a f‖²` is at most `a⁴ · a⁻¹ ∫_{cell (d √a)} ‖f‖²`,
  that is `a³` times the target integral.
* Take square roots: `(a³)^{1/2} = a^{3/2}`.

The helper declarations live in the namespace `T07` (copies of the `T06` helpers, so this file
does not depend on the compile state of `T06`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIIa

namespace T07

/-! ## Basic facts -/

/-- The cell density as an extended nonnegative real: `(density m x : ℝ≥0∞) = ofReal (jb x ^ m)`. -/
lemma density_coe (m : ℝ) (x : ℝ × ℝ) :
    ((B0579.density m x : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (B0579.jb x ^ m) := rfl

/-- The enorm of a nonnegative real scalar, viewed in `ℂ`. -/
lemma enorm_ofReal_cast {r : ℝ} (hr : 0 ≤ r) : ‖(r : ℂ)‖ₑ = ENNReal.ofReal r := by
  rw [enorm_eq_nnnorm, Complex.nnnorm_real, ← Real.toNNReal_eq_nnnorm_of_nonneg hr]
  rfl

/-- The `L²` norm as the square root of the lintegral of the squared enorm. -/
lemma eLpNorm_two_eq_lintegral (f : ℝ × ℝ → ℂ) (μ : Measure (ℝ × ℝ)) :
    eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2' : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have htr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2 h2', htr]
  simp only [ENNReal.rpow_two]

/-- The weighted cell integral as an integral over the whole plane, with the cell indicator. -/
lemma lintegral_cellMeasure_eq (c m : ℝ) (g : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ x, g x ∂(B0579.cellMeasure c m) =
      ∫⁻ x, (B0579.cell c).indicator (fun x => ((B0579.density m x : ℝ≥0) : ℝ≥0∞) * g x) x := by
  rw [B0579.cellMeasure,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (B0579.measurable_density m).coe_nnreal_ennreal
      (Filter.Eventually.of_forall fun _ => ENNReal.coe_lt_top),
    lintegral_indicator (B0579.measurableSet_cell c)]
  try rfl

/-- Smul by `R > 0` maps the cell of width `d R` onto the cell of width `d`. -/
lemma smul_mem_cell_iff (d R : ℝ) (hR : 0 < R) (y : ℝ × ℝ) :
    R • y ∈ B0579.cell (d * R) ↔ y ∈ B0579.cell d := by
  have key : ∀ t : ℝ, (-(d * R / 2) ≤ R * t ∧ R * t < d * R / 2) ↔
      (-(d / 2) ≤ t ∧ t < d / 2) := by
    intro t
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · by_contra h
        have h' := not_le.mp h
        nlinarith
      · by_contra h
        have h' := not_lt.mp h
        nlinarith
    · rintro ⟨h1, h2⟩
      constructor
      · nlinarith
      · nlinarith
  simp only [B0579.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true, Prod.smul_fst,
    smul_eq_mul]
  exact key y.1

/-- Change of variables `y ↦ √a • y` on `ℝ × ℝ`: `∫⁻ H(√a • y) dy = a⁻¹ ∫⁻ H`. -/
lemma lintegral_comp_sqrt_smul {a : ℝ} (ha : 0 < a) {H : ℝ × ℝ → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ y, H (Real.sqrt a • y) = ENNReal.ofReal a⁻¹ * ∫⁻ x, H x := by
  have hR : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hfin : Module.finrank ℝ (ℝ × ℝ) = 2 := by
    simp [Module.finrank_prod]
  have hmap := Measure.map_addHaar_smul (volume : Measure (ℝ × ℝ)) hR
  simp only [hfin, Real.sq_sqrt ha.le, abs_inv, abs_of_pos ha] at hmap
  rw [← lintegral_map hH (measurable_const_smul (Real.sqrt a)), hmap, lintegral_smul_measure,
    smul_eq_mul]

/-- `√a • y = (√a y₁, √a y₂)`. -/
lemma sqrt_smul_eq (a : ℝ) (y : ℝ × ℝ) :
    Real.sqrt a • y = (Real.sqrt a * y.1, Real.sqrt a * y.2) := by
  ext <;> simp

/-! ## The weight comparison -/

/-- For `a ≥ 1` and `m ≥ 0`, the weight at `y` is at most the weight at `√a • y`:
`jb y ≤ jb (√a • y) = 1 + a(y₁² + y₂²)`. -/
lemma density_le_density_smul (a m : ℝ) (ha : 1 ≤ a) (hm : 0 ≤ m) (y : ℝ × ℝ) :
    ((B0579.density m y : ℝ≥0) : ℝ≥0∞) ≤
      ((B0579.density m (Real.sqrt a • y) : ℝ≥0) : ℝ≥0∞) := by
  have ha0 : 0 < a := by linarith
  have hR2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha0.le
  have hjb : B0579.jb y ≤ B0579.jb (Real.sqrt a • y) := by
    have e1 : B0579.jb (Real.sqrt a • y) = 1 + a * (y.1 ^ 2 + y.2 ^ 2) := by
      unfold B0579.jb
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      rw [mul_pow, mul_pow, hR2]
      ring
    rw [e1]
    unfold B0579.jb
    nlinarith [mul_nonneg (sub_nonneg.2 ha) (add_nonneg (sq_nonneg y.1) (sq_nonneg y.2))]
  rw [density_coe, density_coe]
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow (B0579.jb_pos _).le hjb hm

/-! ## The integrands on the cells -/

/-- The integrand `⟨y⟩^{2m} ‖J_a⁻¹ f y‖²` restricted to the cell `d`. -/
def Kinv (a d m : ℝ) (f : ℝ × ℝ → ℂ) : ℝ × ℝ → ℝ≥0∞ :=
  (B0579.cell d).indicator fun y => ((B0579.density m y : ℝ≥0) : ℝ≥0∞) * ‖JscaleInv a f y‖ₑ ^ 2

/-- The integrand `⟨x⟩^{2m} ‖f x‖²` restricted to the cell `c`. -/
def Gfun (c m : ℝ) (f : ℝ × ℝ → ℂ) : ℝ × ℝ → ℝ≥0∞ :=
  (B0579.cell c).indicator fun x => ((B0579.density m x : ℝ≥0) : ℝ≥0∞) * ‖f x‖ₑ ^ 2

/-- Measurability of `Gfun c m f` for measurable `f`. -/
lemma measurable_Gfun (c m : ℝ) {f : ℝ × ℝ → ℂ} (hf : Measurable f) :
    Measurable (Gfun c m f) := by
  unfold Gfun
  exact ((B0579.measurable_density m).coe_nnreal_ennreal.mul
    (hf.enorm.pow_const 2)).indicator (B0579.measurableSet_cell _)

/-- Pointwise bound after the change of variables:
`Kinv a d m f y ≤ a⁴ · Gfun (d √a) m f (√a • y)` for `a ≥ 1`, `m ≥ 0`. -/
lemma Kinv_le (a d m : ℝ) (ha : 1 ≤ a) (hm : 0 ≤ m) (f : ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    Kinv a d m f y ≤ ENNReal.ofReal (a ^ 4) * Gfun (d * Real.sqrt a) m f (Real.sqrt a • y) := by
  have ha0 : 0 < a := by linarith
  have hR : 0 < Real.sqrt a := Real.sqrt_pos.2 ha0
  by_cases hy : y ∈ B0579.cell d
  · have hmem : Real.sqrt a • y ∈ B0579.cell (d * Real.sqrt a) :=
      (smul_mem_cell_iff d (Real.sqrt a) hR y).2 hy
    have h4 : ENNReal.ofReal (a ^ 2) ^ 2 = ENNReal.ofReal (a ^ 4) := by
      rw [← ENNReal.ofReal_pow (pow_nonneg ha0.le 2) 2]
      congr 1
      ring
    have hJn : ‖JscaleInv a f y‖ₑ ^ 2 = ENNReal.ofReal (a ^ 4) * ‖f (Real.sqrt a • y)‖ₑ ^ 2 := by
      unfold JscaleInv
      rw [sqrt_smul_eq a y, enorm_mul, mul_pow, enorm_ofReal_cast (pow_nonneg ha0.le 2), h4]
    unfold Kinv Gfun
    simp only [Set.indicator_of_mem hmem, Set.indicator_of_mem hy]
    calc ((B0579.density m y : ℝ≥0) : ℝ≥0∞) * ‖JscaleInv a f y‖ₑ ^ 2
        = ((B0579.density m y : ℝ≥0) : ℝ≥0∞) *
            (ENNReal.ofReal (a ^ 4) * ‖f (Real.sqrt a • y)‖ₑ ^ 2) := by
          rw [hJn]
      _ ≤ ((B0579.density m (Real.sqrt a • y) : ℝ≥0) : ℝ≥0∞) *
            (ENNReal.ofReal (a ^ 4) * ‖f (Real.sqrt a • y)‖ₑ ^ 2) :=
          mul_le_mul_of_nonneg_right (density_le_density_smul a m ha hm y) zero_le
      _ = ENNReal.ofReal (a ^ 4) *
            (((B0579.density m (Real.sqrt a • y) : ℝ≥0) : ℝ≥0∞) * ‖f (Real.sqrt a • y)‖ₑ ^ 2) :=
          mul_left_comm _ _ _
  · have hmem : Real.sqrt a • y ∉ B0579.cell (d * Real.sqrt a) := fun h =>
      hy ((smul_mem_cell_iff d (Real.sqrt a) hR y).1 h)
    unfold Kinv Gfun
    simp [hmem, hy]

/-- The squared-norm bound before the square root:
`∫⁻_{cell d} ⟨y⟩^{2m} ‖J_a⁻¹ f‖² ≤ a³ ∫⁻_{cell (d √a)} ⟨x⟩^{2m} ‖f‖²`. -/
lemma lintegral_Kinv_le (a d m : ℝ) (ha : 1 ≤ a) (hm : 0 ≤ m) (f : ℝ × ℝ → ℂ)
    (hf : Measurable f) :
    ∫⁻ y, Kinv a d m f y ≤ ENNReal.ofReal (a ^ 3) * ∫⁻ x, Gfun (d * Real.sqrt a) m f x := by
  have ha0 : 0 < a := by linarith
  have hG : Measurable (Gfun (d * Real.sqrt a) m f) := measurable_Gfun _ m hf
  have h3 : a ^ 4 * a⁻¹ = a ^ 3 := by
    have ha' : a ≠ 0 := ha0.ne'
    rw [show a ^ 4 = a ^ 3 * a by ring, mul_assoc, mul_inv_cancel₀ ha', mul_one]
  calc ∫⁻ y, Kinv a d m f y
      ≤ ∫⁻ y, ENNReal.ofReal (a ^ 4) * Gfun (d * Real.sqrt a) m f (Real.sqrt a • y) :=
        lintegral_mono fun y => Kinv_le a d m ha hm f y
    _ = ENNReal.ofReal (a ^ 4) * ∫⁻ y, Gfun (d * Real.sqrt a) m f (Real.sqrt a • y) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (a ^ 4) *
          (ENNReal.ofReal a⁻¹ * ∫⁻ x, Gfun (d * Real.sqrt a) m f x) := by
        rw [lintegral_comp_sqrt_smul ha0 hG]
    _ = ENNReal.ofReal (a ^ 3) * ∫⁻ x, Gfun (d * Real.sqrt a) m f x := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg ha0.le 4), h3]

end T07

/-- **`ScalingJaInv`** (SP 2982-2986): `‖J_a⁻¹ f‖_{X_{m,d}} ≤ a^{3/2}‖f‖_{X_{m,c}}`,
`c = √a d`, for `m ≥ 0`, `a ≥ 1`, `d > 0` and measurable `f`. -/
theorem scalingJaInv : ScalingJaInv := by
  unfold ScalingJaInv
  intro m hm a d ha hd f hf
  have ha0 : 0 < a := by linarith
  have hI := T07.lintegral_Kinv_le a d m ha hm f hf
  have hpow : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hA : ∫⁻ x, ‖JscaleInv a f x‖ₑ ^ 2 ∂(B0579.cellMeasure d m) =
      ∫⁻ y, T07.Kinv a d m f y :=
    T07.lintegral_cellMeasure_eq d m _
  have hB : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(B0579.cellMeasure (d * Real.sqrt a) m) =
      ∫⁻ x, T07.Gfun (d * Real.sqrt a) m f x :=
    T07.lintegral_cellMeasure_eq (d * Real.sqrt a) m _
  unfold xNorm
  rw [T07.eLpNorm_two_eq_lintegral, T07.eLpNorm_two_eq_lintegral, hA, hB]
  calc (∫⁻ y, T07.Kinv a d m f y) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (a ^ 3) * ∫⁻ x, T07.Gfun (d * Real.sqrt a) m f x) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hI hpow
    _ = ENNReal.ofReal (a ^ 3) ^ (1 / 2 : ℝ) *
          (∫⁻ x, T07.Gfun (d * Real.sqrt a) m f x) ^ (1 / 2 : ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ hpow
    _ = ENNReal.ofReal (a ^ (3 / 2 : ℝ)) *
          (∫⁻ x, T07.Gfun (d * Real.sqrt a) m f x) ^ (1 / 2 : ℝ) := by
        congr 1
        rw [ENNReal.ofReal_rpow_of_nonneg (pow_nonneg ha0.le 3) hpow, ← Real.rpow_natCast,
          ← Real.rpow_mul ha0.le]
        norm_num

end UnforcedLeray.Short.IIIa
