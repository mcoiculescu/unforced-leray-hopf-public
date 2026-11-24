import UnforcedLeray.Short.PartIIIa.Targets

/-!
# T06: scaling bound for `J_a` (SP 2982-2985)

Proves `UnforcedLeray.Short.IIIa.scalingJa` (the `Prop` `ScalingJa` of `Targets.lean`): for
`m ≥ 0`, `a ≥ 1`, `d > 0`, `c = d √a` and measurable `W`,
`xNorm c m (Jscale a W) ≤ ENNReal.ofReal (a ^ ((m - 3) / 2)) * xNorm d m W`.

Proof, by the change of variables `x = √a • y`:
* `cell c = √a • cell d` (`smul_mem_cell_iff`), and Haar measure on `ℝ × ℝ` scales by `a` under
  `y ↦ √a • y` (`lintegral_comp_sqrt_smul`, from `Measure.map_addHaar_smul`).
* `Jscale a W (√a • y) = a^{-2} W y` (`Jscale_smul_sqrt`), and `jb (√a • y) = 1 + a |y|² ≤ a jb y`
  for `a ≥ 1`, so the weight `jb^m` contributes at most `a^m` (`Hfun_le`).
* The factors `a · a^m · a^{-4} = a^{m-3}` give the squared bound (`lintegral_scale_le`), and
  taking square roots gives `a^{(m-3)/2}`.

The helper declarations live in the namespace `T06`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIIa

namespace T06

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

/-- Measurability of `J_a W` for measurable `W`. -/
lemma measurable_Jscale (a : ℝ) {W : ℝ × ℝ → ℂ} (hW : Measurable W) :
    Measurable (Jscale a W) := by
  unfold Jscale
  have hpt : Measurable (fun x : ℝ × ℝ => (x.1 / Real.sqrt a, x.2 / Real.sqrt a)) :=
    (measurable_fst.div_const _).prodMk (measurable_snd.div_const _)
  exact (hW.comp hpt).const_mul _

/-- `J_a W (√a • y) = a^{-2} W y`. -/
lemma Jscale_smul_sqrt {a : ℝ} (ha : 0 < a) (W : ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    Jscale a W (Real.sqrt a • y) = ((a ^ (-2 : ℝ) : ℝ) : ℂ) * W y := by
  have hR : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hpt : ((Real.sqrt a • y).1 / Real.sqrt a, (Real.sqrt a • y).2 / Real.sqrt a) = y := by
    ext <;> simp [hR]
  unfold Jscale
  rw [hpt]

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

/-! ## The integrands on the whole plane -/

/-- The integrand `⟨x⟩^{2m} ‖J_a W x‖²` on the whole plane, restricted to the cell `c`. -/
def Hfun (c m a : ℝ) (W : ℝ × ℝ → ℂ) : ℝ × ℝ → ℝ≥0∞ :=
  (B0579.cell c).indicator fun x => ((B0579.density m x : ℝ≥0) : ℝ≥0∞) * ‖Jscale a W x‖ₑ ^ 2

/-- The integrand `⟨y⟩^{2m} ‖W y‖²` on the whole plane, restricted to the cell `d`. -/
def Kfun (d m : ℝ) (W : ℝ × ℝ → ℂ) : ℝ × ℝ → ℝ≥0∞ :=
  (B0579.cell d).indicator fun y => ((B0579.density m y : ℝ≥0) : ℝ≥0∞) * ‖W y‖ₑ ^ 2

/-- Pointwise bound after the change of variables: `Hfun c m a W (√a • y) ≤ a^{m-4} Kfun d m W y`
for `c = d √a`, `a ≥ 1`, `m ≥ 0`. -/
lemma Hfun_le (a d m : ℝ) (ha : 1 ≤ a) (hm : 0 ≤ m) (W : ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    Hfun (d * Real.sqrt a) m a W (Real.sqrt a • y) ≤
      ENNReal.ofReal (a ^ (m - 4)) * Kfun d m W y := by
  have ha0 : 0 < a := by linarith
  have hR : 0 < Real.sqrt a := Real.sqrt_pos.2 ha0
  have hR2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha0.le
  by_cases hy : y ∈ B0579.cell d
  · have hmem : Real.sqrt a • y ∈ B0579.cell (d * Real.sqrt a) :=
      (smul_mem_cell_iff d (Real.sqrt a) hR y).2 hy
    have e1 : B0579.jb (Real.sqrt a • y) = 1 + a * (y.1 ^ 2 + y.2 ^ 2) := by
      unfold B0579.jb
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      rw [mul_pow, mul_pow, hR2]
      ring
    have hjb : B0579.jb (Real.sqrt a • y) ≤ a * B0579.jb y := by
      have e2 : B0579.jb y = 1 + y.1 ^ 2 + y.2 ^ 2 := rfl
      rw [e1, e2]
      nlinarith [sq_nonneg y.1, sq_nonneg y.2]
    have hdens : ((B0579.density m (Real.sqrt a • y) : ℝ≥0) : ℝ≥0∞) ≤
        ENNReal.ofReal (a ^ m) * ((B0579.density m y : ℝ≥0) : ℝ≥0∞) := by
      rw [density_coe, density_coe, ← ENNReal.ofReal_mul (Real.rpow_nonneg ha0.le m)]
      apply ENNReal.ofReal_le_ofReal
      calc B0579.jb (Real.sqrt a • y) ^ m ≤ (a * B0579.jb y) ^ m :=
            Real.rpow_le_rpow (B0579.jb_pos _).le hjb hm
        _ = a ^ m * B0579.jb y ^ m := Real.mul_rpow ha0.le (B0579.jb_pos y).le
    have hJn : ‖Jscale a W (Real.sqrt a • y)‖ₑ = ENNReal.ofReal (a ^ (-2 : ℝ)) * ‖W y‖ₑ := by
      rw [Jscale_smul_sqrt ha0 W y, enorm_mul, enorm_ofReal_cast (Real.rpow_nonneg ha0.le _)]
    have hsc : ENNReal.ofReal (a ^ m) * ENNReal.ofReal (a ^ (-2 : ℝ)) ^ 2 =
        ENNReal.ofReal (a ^ (m - 4)) := by
      have hr : (a ^ (-2 : ℝ)) ^ 2 = a ^ (-4 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ha0.le]
        norm_num
      have hr2 : a ^ m * a ^ (-4 : ℝ) = a ^ (m - 4) := by
        rw [← Real.rpow_add ha0, sub_eq_add_neg]
      rw [← ENNReal.ofReal_pow (Real.rpow_nonneg ha0.le (-2 : ℝ)) 2,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg ha0.le m), hr, hr2]
    unfold Hfun Kfun
    simp only [Set.indicator_of_mem hmem, Set.indicator_of_mem hy]
    calc ((B0579.density m (Real.sqrt a • y) : ℝ≥0) : ℝ≥0∞) * ‖Jscale a W (Real.sqrt a • y)‖ₑ ^ 2
        = ((B0579.density m (Real.sqrt a • y) : ℝ≥0) : ℝ≥0∞) *
            (ENNReal.ofReal (a ^ (-2 : ℝ)) ^ 2 * ‖W y‖ₑ ^ 2) := by
          rw [hJn, mul_pow]
      _ ≤ (ENNReal.ofReal (a ^ m) * ((B0579.density m y : ℝ≥0) : ℝ≥0∞)) *
            (ENNReal.ofReal (a ^ (-2 : ℝ)) ^ 2 * ‖W y‖ₑ ^ 2) :=
          mul_le_mul_of_nonneg_right hdens zero_le
      _ = ENNReal.ofReal (a ^ (m - 4)) * (((B0579.density m y : ℝ≥0) : ℝ≥0∞) * ‖W y‖ₑ ^ 2) := by
          rw [← hsc]
          ring
  · have hmem : Real.sqrt a • y ∉ B0579.cell (d * Real.sqrt a) := fun h =>
      hy ((smul_mem_cell_iff d (Real.sqrt a) hR y).1 h)
    unfold Hfun Kfun
    simp [hmem, hy]

/-- The squared-norm bound before taking square roots:
`∫⁻_{cell (d √a)} ‖J_a W‖² ⟨x⟩^{2m} ≤ a^{m-3} ∫⁻_{cell d} ‖W‖² ⟨y⟩^{2m}`. -/
lemma lintegral_scale_le (a d m : ℝ) (ha : 1 ≤ a) (hm : 0 ≤ m) (W : ℝ × ℝ → ℂ)
    (hW : Measurable W) :
    ∫⁻ x, ‖Jscale a W x‖ₑ ^ 2 ∂(B0579.cellMeasure (d * Real.sqrt a) m) ≤
      ENNReal.ofReal (a ^ (m - 3)) * ∫⁻ y, ‖W y‖ₑ ^ 2 ∂(B0579.cellMeasure d m) := by
  have ha0 : 0 < a := by linarith
  have hJ : Measurable (Jscale a W) := measurable_Jscale a hW
  have hHm : Measurable (Hfun (d * Real.sqrt a) m a W) := by
    unfold Hfun
    exact ((B0579.measurable_density m).coe_nnreal_ennreal.mul
      (hJ.enorm.pow_const 2)).indicator (B0579.measurableSet_cell _)
  have hA : ∫⁻ x, ‖Jscale a W x‖ₑ ^ 2 ∂(B0579.cellMeasure (d * Real.sqrt a) m) =
      ∫⁻ x, Hfun (d * Real.sqrt a) m a W x :=
    lintegral_cellMeasure_eq (d * Real.sqrt a) m (fun x => ‖Jscale a W x‖ₑ ^ 2)
  have hB : ∫⁻ x, Hfun (d * Real.sqrt a) m a W x =
      ENNReal.ofReal a * ∫⁻ y, Hfun (d * Real.sqrt a) m a W (Real.sqrt a • y) := by
    rw [lintegral_comp_sqrt_smul ha0 hHm, ← mul_assoc, ← ENNReal.ofReal_mul ha0.le,
      mul_inv_cancel₀ ha0.ne', ENNReal.ofReal_one, one_mul]
  have hD : ∫⁻ y, Hfun (d * Real.sqrt a) m a W (Real.sqrt a • y) ≤
      ENNReal.ofReal (a ^ (m - 4)) * ∫⁻ y, Kfun d m W y := by
    calc ∫⁻ y, Hfun (d * Real.sqrt a) m a W (Real.sqrt a • y)
        ≤ ∫⁻ y, ENNReal.ofReal (a ^ (m - 4)) * Kfun d m W y :=
          lintegral_mono fun y => Hfun_le a d m ha hm W y
      _ = ENNReal.ofReal (a ^ (m - 4)) * ∫⁻ y, Kfun d m W y :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hE : ∫⁻ y, Kfun d m W y = ∫⁻ y, ‖W y‖ₑ ^ 2 ∂(B0579.cellMeasure d m) :=
    (lintegral_cellMeasure_eq d m (fun y => ‖W y‖ₑ ^ 2)).symm
  have hsc : a ^ (m - 3) = a * a ^ (m - 4) := by
    rw [show m - 3 = 1 + (m - 4) by ring, Real.rpow_add ha0, Real.rpow_one]
  calc ∫⁻ x, ‖Jscale a W x‖ₑ ^ 2 ∂(B0579.cellMeasure (d * Real.sqrt a) m)
      = ∫⁻ x, Hfun (d * Real.sqrt a) m a W x := hA
    _ = ENNReal.ofReal a * ∫⁻ y, Hfun (d * Real.sqrt a) m a W (Real.sqrt a • y) := hB
    _ ≤ ENNReal.ofReal a * (ENNReal.ofReal (a ^ (m - 4)) * ∫⁻ y, Kfun d m W y) :=
          mul_le_mul_of_nonneg_left hD zero_le
    _ = ENNReal.ofReal (a ^ (m - 3)) * ∫⁻ y, Kfun d m W y := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul ha0.le, hsc]
    _ = ENNReal.ofReal (a ^ (m - 3)) * ∫⁻ y, ‖W y‖ₑ ^ 2 ∂(B0579.cellMeasure d m) := by
          rw [hE]

end T06

/-- **`ScalingJa`** (SP 2982-2985): `‖J_a W‖_{X_{m,c}} ≤ a^{(m-3)/2} ‖W‖_{X_{m,d}}`,
`c = √a d`, for `m ≥ 0`, `a ≥ 1`, `d > 0` and measurable `W`. -/
theorem scalingJa : ScalingJa := by
  unfold ScalingJa
  intro m hm a d ha hd W hW
  have ha0 : 0 < a := by linarith
  have hI := T06.lintegral_scale_le a d m ha hm W hW
  have hpow : (0 : ℝ) ≤ 1 / 2 := by norm_num
  unfold xNorm
  rw [T06.eLpNorm_two_eq_lintegral, T06.eLpNorm_two_eq_lintegral]
  calc (∫⁻ x, ‖Jscale a W x‖ₑ ^ 2 ∂(B0579.cellMeasure (d * Real.sqrt a) m)) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (a ^ (m - 3)) * ∫⁻ y, ‖W y‖ₑ ^ 2 ∂(B0579.cellMeasure d m)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hI hpow
    _ = ENNReal.ofReal (a ^ (m - 3)) ^ (1 / 2 : ℝ) *
          (∫⁻ y, ‖W y‖ₑ ^ 2 ∂(B0579.cellMeasure d m)) ^ (1 / 2 : ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ hpow
    _ = ENNReal.ofReal (a ^ ((m - 3) / 2)) *
          (∫⁻ y, ‖W y‖ₑ ^ 2 ∂(B0579.cellMeasure d m)) ^ (1 / 2 : ℝ) := by
        congr 1
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg ha0.le _) hpow, ← Real.rpow_mul ha0.le,
          show (m - 3) * (1 / 2 : ℝ) = (m - 3) / 2 by ring]

end UnforcedLeray.Short.IIIa
