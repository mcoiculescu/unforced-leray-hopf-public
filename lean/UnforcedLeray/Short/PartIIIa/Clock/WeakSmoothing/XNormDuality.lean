import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.Adjoint
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.PhysFromMoving

/-!
# Weighted `L²` duality on the cell (SP 2823-2827, 3036-3040, 3074)

`xNormDuality m : XNormDuality m` (`Adjoint.lean`). Source of record:
`the November 2 reference manuscript` (SP).

Write `c = ν⁻²`, `a = clockA ν s ≥ 1`, `d = c/√a`, `W = J_a⁻¹ w(s)`, `V` a measurable
representative. The proof has three steps:
* finiteness: `‖W‖_{X_{m,d}} < ∞` from `‖w(s)‖_{X_{m,c}} < ∞` by the change of variables
  `y ↦ √a y` and the comparison `⟨y⟩^{2m} ≤ (R²)^{|m|}⟨Ry⟩^{2m}` (`xNorm_fin_of_scale`);
* the duality element `G = conj(V) ⟨y⟩^{2m} / ‖V‖_{X_{m,d}}` has `‖G‖_{X_{-m,d}} = 1` and
  `∫_{C_d} W G = ‖V‖_{X_{m,d}}` (`dual_core`);
* the cell change of variables and weighted-norm identities are copies of the helpers of
  `T08_ScalingJaInvDual.lean` (namespace `XND`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIIa

namespace XND

/-! ## Dilation of the cells -/

/-- Dilation by `R > 0` maps the cell of width `d R` onto the cell of width `d`. -/
lemma smul_mem_cell_iff {d R : ℝ} (hR : 0 < R) (y : ℝ × ℝ) :
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

/-- The same cell identity written for the dilation by `R` of a point of the cell `d`. -/
lemma smul_mem_cell_iff_div {d R : ℝ} (hR : 0 < R) (x : ℝ × ℝ) :
    R • x ∈ B0579.cell d ↔ x ∈ B0579.cell (d / R) := by
  have h := smul_mem_cell_iff (d := d / R) hR x
  rwa [div_mul_cancel₀ d hR.ne'] at h

/-- Test-function-free change of variables for the cell integral of an `IntegrableOn` function. -/
lemma integrableOn_cell_scale {d R : ℝ} (hR : 0 < R) {H : ℝ × ℝ → ℂ}
    (hH : IntegrableOn H (B0579.cell d)) :
    IntegrableOn (fun x => H (R • x)) (B0579.cell (d / R)) := by
  have hI : Integrable ((B0579.cell d).indicator H) :=
    (integrable_indicator_iff (B0579.measurableSet_cell d)).2 hH
  have hI' := hI.comp_smul hR.ne'
  have heq : (B0579.cell (d / R)).indicator (fun x => H (R • x)) =
      fun x => (B0579.cell d).indicator H (R • x) := by
    funext x
    by_cases hx : x ∈ B0579.cell (d / R)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((smul_mem_cell_iff_div hR x).2 hx)]
    · rw [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem (fun h => hx ((smul_mem_cell_iff_div hR x).1 h))]
  refine (integrable_indicator_iff (B0579.measurableSet_cell (d / R))).1 ?_
  rw [heq]
  exact hI'

/-- A measurable embedding for the dilation `y ↦ R • y`, `R ≠ 0`. -/
lemma measurableEmbedding_smul {R : ℝ} (hR : R ≠ 0) :
    MeasurableEmbedding (fun y : ℝ × ℝ => R • y) :=
  measurableEmbedding_const_smul₀ hR

/-- Lebesgue change of variables under `y ↦ R • y` (no measurability hypothesis on `K`). -/
lemma lintegral_comp_smul_eq {R : ℝ} (hR : 0 < R) (K : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ y, K (R • y) = ENNReal.ofReal ((R ^ 2)⁻¹) * ∫⁻ x, K x := by
  have hfin : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp [Module.finrank_prod]
  have hmap := Measure.map_addHaar_smul (volume : Measure (ℝ × ℝ)) hR.ne'
  rw [hfin] at hmap
  have h1 : ∫⁻ y, K (R • y) = ∫⁻ x, K x ∂(Measure.map (fun y : ℝ × ℝ => R • y) volume) :=
    ((measurableEmbedding_smul hR.ne').lintegral_map K).symm
  rw [h1, hmap, lintegral_smul_measure]
  simp only [abs_inv, abs_of_pos (pow_pos hR 2), smul_eq_mul]

/-- Cell-restricted lintegral form of the change of variables, indicator version:
`∫⁻_{cell (dR)} K = R² ∫⁻_{cell d} K(R·)`. -/
lemma lintegral_cell_scale_ind {d R : ℝ} (hR : 0 < R) (K : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ x, (B0579.cell (d * R)).indicator K x =
      ENNReal.ofReal (R ^ 2) * ∫⁻ y, (B0579.cell d).indicator (fun y => K (R • y)) y := by
  have hpt : ∀ y : ℝ × ℝ, (B0579.cell d).indicator (fun y => K (R • y)) y =
      (B0579.cell (d * R)).indicator K (R • y) := by
    intro y
    by_cases hy : y ∈ B0579.cell d
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem ((smul_mem_cell_iff hR y).2 hy)]
    · rw [Set.indicator_of_notMem hy,
        Set.indicator_of_notMem (fun h => hy ((smul_mem_cell_iff hR y).1 h))]
  simp_rw [hpt]
  rw [lintegral_comp_smul_eq hR ((B0579.cell (d * R)).indicator K), ← mul_assoc,
    ← ENNReal.ofReal_mul (sq_nonneg R), mul_inv_cancel₀ (pow_pos hR 2).ne', ENNReal.ofReal_one,
    one_mul]

/-- Bochner change of variables `∫_{cell (dR)} F = R² ∫_{cell d} F(R·)` for any `F` (the
Bochner integral of a non-integrable function is zero on both sides). -/
lemma integral_cell_scale {d R : ℝ} (hR : 0 < R) (F : ℝ × ℝ → ℂ) :
    ∫ x in B0579.cell (d * R), F x = ((R ^ 2 : ℝ) : ℂ) * ∫ y in B0579.cell d, F (R • y) := by
  have hfin : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp [Module.finrank_prod]
  have hpt : ∀ y : ℝ × ℝ, (B0579.cell d).indicator (fun y => F (R • y)) y =
      (B0579.cell (d * R)).indicator F (R • y) := by
    intro y
    by_cases hy : y ∈ B0579.cell d
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem ((smul_mem_cell_iff hR y).2 hy)]
    · rw [Set.indicator_of_notMem hy,
        Set.indicator_of_notMem (fun h => hy ((smul_mem_cell_iff hR y).1 h))]
  have hL : ∫ y in B0579.cell d, F (R • y) = ∫ y, (B0579.cell (d * R)).indicator F (R • y) := by
    rw [← integral_indicator (B0579.measurableSet_cell d)]
    congr 1
    funext y
    exact hpt y
  have hR' : ∫ x in B0579.cell (d * R), F x = ∫ x, (B0579.cell (d * R)).indicator F x := by
    rw [integral_indicator (B0579.measurableSet_cell _)]
  have h := Measure.integral_comp_smul (volume : Measure (ℝ × ℝ))
    ((B0579.cell (d * R)).indicator F) R
  rw [hfin, ← hL, ← hR'] at h
  rw [h, abs_inv, abs_of_pos (pow_pos hR 2), Complex.real_smul, ← mul_assoc,
    ← Complex.ofReal_mul, mul_inv_cancel₀ (pow_pos hR 2).ne', Complex.ofReal_one, one_mul]

/-! ## Weighted `L²` norms on the cell -/

/-- Lebesgue cell-measure formula with the weight `density p`, for an arbitrary function. -/
lemma lintegral_cellMeasure_eq (c m : ℝ) (g : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ x, g x ∂(B0579.cellMeasure c m) =
      ∫⁻ x, (B0579.cell c).indicator (fun x => ((B0579.density m x : ℝ≥0) : ℝ≥0∞) * g x) x := by
  rw [B0579.cellMeasure,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (B0579.measurable_density m).coe_nnreal_ennreal
      (Filter.Eventually.of_forall fun _ => ENNReal.coe_lt_top),
    lintegral_indicator (B0579.measurableSet_cell c)]
  try rfl

/-- The weighted integrand `density p x * ‖F x‖ₑ²`. -/
def cw (p : ℝ) (F : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℝ≥0∞ :=
  ((B0579.density p x : ℝ≥0) : ℝ≥0∞) * ‖F x‖ₑ ^ 2

lemma cellQ_eq (c p : ℝ) (F : ℝ × ℝ → ℂ) :
    ∫⁻ x, ‖F x‖ₑ ^ 2 ∂(B0579.cellMeasure c p) = ∫⁻ x, (B0579.cell c).indicator (cw p F) x :=
  lintegral_cellMeasure_eq c p (fun x => ‖F x‖ₑ ^ 2)

lemma eLpNorm_two_eq_lintegral' (f : ℝ × ℝ → ℂ) (μ : Measure (ℝ × ℝ)) :
    eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2' : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have htr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2 h2', htr]
  simp only [ENNReal.rpow_two]

lemma xNorm_sq (c m : ℝ) (F : ℝ × ℝ → ℂ) :
    xNorm c m F ^ 2 = ∫⁻ x, ‖F x‖ₑ ^ 2 ∂(B0579.cellMeasure c m) := by
  have hpow : ∀ X : ℝ≥0∞, (X ^ (1 / 2 : ℝ)) ^ 2 = X := by
    intro X
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  unfold xNorm
  rw [eLpNorm_two_eq_lintegral', hpow]

lemma enorm_ofReal_cast' (κ : ℝ) : ‖(κ : ℂ)‖ₑ = ENNReal.ofReal |κ| := by
  rw [← Real.enorm_eq_ofReal_abs]
  simp [enorm_eq_nnnorm]

lemma enorm_real_mul_sq (κ : ℝ) (z : ℂ) :
    ‖(κ : ℂ) * z‖ₑ ^ 2 = ENNReal.ofReal (κ ^ 2) * ‖z‖ₑ ^ 2 := by
  rw [enorm_mul, mul_pow, enorm_ofReal_cast']
  congr 1
  rw [← ENNReal.ofReal_pow (abs_nonneg κ), sq_abs]


/-! ## Density comparison under the dilation `y ↦ R y`, `R ≥ 1` -/

lemma jb_le_jb_dilate {R : ℝ} (hR : 1 ≤ R) (y : ℝ × ℝ) :
    B0579.jb y ≤ B0579.jb (R • y) := by
  unfold B0579.jb
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have hR2 : 1 ≤ R ^ 2 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 hR2) (add_nonneg (sq_nonneg y.1) (sq_nonneg y.2))]

lemma jb_dilate_le {R : ℝ} (hR : 1 ≤ R) (y : ℝ × ℝ) :
    B0579.jb (R • y) ≤ R ^ 2 * B0579.jb y := by
  unfold B0579.jb
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have hR2 : 1 ≤ R ^ 2 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 hR2) (add_nonneg (sq_nonneg y.1) (sq_nonneg y.2))]

/-- `⟨y⟩^{2m} ≤ (R²)^{|m|} ⟨Ry⟩^{2m}` for `R ≥ 1`: the weight at `y` is controlled by the weight
at `R y`. -/
lemma density_le_dilate {R : ℝ} (hR : 1 ≤ R) (m : ℝ) (y : ℝ × ℝ) :
    ((B0579.density m y : ℝ≥0) : ℝ≥0∞) ≤
      ENNReal.ofReal ((R ^ 2) ^ |m|) * ((B0579.density m (R • y) : ℝ≥0) : ℝ≥0∞) := by
  have hR0 : 0 < R := by linarith
  have hR2 : 1 ≤ R ^ 2 := by nlinarith
  have hR2pos : 0 < R ^ 2 := by positivity
  have hj1 := B0579.jb_pos y
  have hj2 := B0579.jb_pos (R • y)
  have key : B0579.jb y ^ m ≤ (R ^ 2) ^ |m| * B0579.jb (R • y) ^ m := by
    rcases le_total 0 m with hm | hm
    · rw [abs_of_nonneg hm]
      have h1 : B0579.jb y ^ m ≤ B0579.jb (R • y) ^ m :=
        Real.rpow_le_rpow hj1.le (jb_le_jb_dilate hR y) hm
      have h2 : (1 : ℝ) ≤ (R ^ 2) ^ m := Real.one_le_rpow hR2 hm
      have h3 : 0 ≤ B0579.jb (R • y) ^ m := Real.rpow_nonneg hj2.le _
      nlinarith
    · rw [abs_of_nonpos hm, Real.rpow_neg hR2pos.le]
      have hpos : 0 < B0579.jb (R • y) / R ^ 2 := div_pos hj2 hR2pos
      have hle : B0579.jb (R • y) / R ^ 2 ≤ B0579.jb y := by
        rw [div_le_iff₀ hR2pos]
        linarith [jb_dilate_le hR y]
      have h1 : B0579.jb y ^ m ≤ (B0579.jb (R • y) / R ^ 2) ^ m :=
        Real.rpow_le_rpow_of_nonpos hpos hle hm
      rw [Real.div_rpow hj2.le hR2pos.le, div_eq_inv_mul] at h1
      exact h1
  show ENNReal.ofReal (B0579.jb y ^ m) ≤
    ENNReal.ofReal ((R ^ 2) ^ |m|) * ENNReal.ofReal (B0579.jb (R • y) ^ m)
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (R ^ 2) ^ |m|)]
  exact ENNReal.ofReal_le_ofReal key

lemma xNorm_sq_ind (c p : ℝ) (F : ℝ × ℝ → ℂ) :
    xNorm c p F ^ 2 = ∫⁻ x, (B0579.cell c).indicator (cw p F) x := by
  rw [xNorm_sq, cellQ_eq]

lemma sqrt_smul_eq' (a : ℝ) (y : ℝ × ℝ) :
    Real.sqrt a • y = (Real.sqrt a * y.1, Real.sqrt a * y.2) := by
  ext <;> simp

lemma jscale_eq' (a : ℝ) (f : ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    JscaleInv a f y = ((a ^ 2 : ℝ) : ℂ) * f (Real.sqrt a • y) := by
  unfold JscaleInv
  rw [sqrt_smul_eq']

/-- Finiteness of the weighted norm of `J_a⁻¹ F` on the cell `d = c/√a` from that of `F` on
the cell `c` (change of variables `y ↦ √a y`, SP 2983-2989). -/
lemma xNorm_fin_of_scale {c d a m : ℝ} (ha : 1 ≤ a) (hd : 0 < d) (hdc : d * Real.sqrt a = c)
    {F : ℝ × ℝ → ℂ} (hF : xNorm c m F ≠ ⊤) :
    xNorm d m (JscaleInv a F) ≠ ⊤ := by
  have ha0 : 0 < a := by linarith
  have hR1 : 1 ≤ Real.sqrt a := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt ha
  have hR0 : 0 < Real.sqrt a := by linarith
  have hI : ∫⁻ y, (B0579.cell d).indicator (fun y => cw m F (Real.sqrt a • y)) y ≠ ⊤ := by
    have h1 := lintegral_cell_scale_ind (d := d) hR0 (cw m F)
    rw [hdc] at h1
    have h2 : ∫⁻ x, (B0579.cell c).indicator (cw m F) x ≠ ⊤ := by
      rw [← xNorm_sq_ind]; exact ENNReal.pow_ne_top hF
    rw [h1] at h2
    intro h
    apply h2
    rw [h]
    exact ENNReal.mul_top (ENNReal.ofReal_pos.2 (pow_pos hR0 2)).ne'
  have hC : ENNReal.ofReal ((Real.sqrt a ^ 2) ^ |m|) * ENNReal.ofReal ((a ^ 2) ^ 2) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hpt : ∀ y : ℝ × ℝ, (B0579.cell d).indicator (cw m (JscaleInv a F)) y ≤
      (ENNReal.ofReal ((Real.sqrt a ^ 2) ^ |m|) * ENNReal.ofReal ((a ^ 2) ^ 2)) *
        (B0579.cell d).indicator (fun y => cw m F (Real.sqrt a • y)) y := by
    intro y
    by_cases hy : y ∈ B0579.cell d
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      have hV : JscaleInv a F y = ((a ^ 2 : ℝ) : ℂ) * F (Real.sqrt a • y) := jscale_eq' a F y
      simp only [cw]
      rw [hV, enorm_real_mul_sq]
      calc ((B0579.density m y : ℝ≥0) : ℝ≥0∞) *
            (ENNReal.ofReal ((a ^ 2) ^ 2) * ‖F (Real.sqrt a • y)‖ₑ ^ 2)
          ≤ (ENNReal.ofReal ((Real.sqrt a ^ 2) ^ |m|) *
              ((B0579.density m (Real.sqrt a • y) : ℝ≥0) : ℝ≥0∞)) *
              (ENNReal.ofReal ((a ^ 2) ^ 2) * ‖F (Real.sqrt a • y)‖ₑ ^ 2) :=
            mul_le_mul_of_nonneg_right (density_le_dilate hR1 m y) zero_le
        _ = (ENNReal.ofReal ((Real.sqrt a ^ 2) ^ |m|) * ENNReal.ofReal ((a ^ 2) ^ 2)) *
              (((B0579.density m (Real.sqrt a • y) : ℝ≥0) : ℝ≥0∞) *
                ‖F (Real.sqrt a • y)‖ₑ ^ 2) := by ring
    · simp [Set.indicator_apply, hy]
  have hle : ∫⁻ y, (B0579.cell d).indicator (cw m (JscaleInv a F)) y ≤
      (ENNReal.ofReal ((Real.sqrt a ^ 2) ^ |m|) * ENNReal.ofReal ((a ^ 2) ^ 2)) *
        ∫⁻ y, (B0579.cell d).indicator (fun y => cw m F (Real.sqrt a • y)) y := by
    rw [← lintegral_const_mul' _ _ hC]
    exact lintegral_mono hpt
  have hsq : xNorm d m (JscaleInv a F) ^ 2 ≠ ⊤ := by
    rw [xNorm_sq_ind]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hC hI) hle
  intro h
  apply hsq
  rw [h]
  simp

/-- The duality step: for measurable `V` with `‖V‖_{X_{m,d}} < ∞`, and `W = V` a.e. on the
cell, `‖W‖_{X_{m,d}} ≤ sup_G |∫_{C_d} W G|` over `‖G‖_{X_{-m,d}} ≤ 1`, attained at
`G = conj(V) ⟨y⟩^{2m} / ‖V‖`. -/
lemma dual_core {d m : ℝ} {W V : ℝ × ℝ → ℂ} (hV : Measurable V)
    (hWV : W =ᵐ[volume.restrict (B0579.cell d)] V) (hfin : xNorm d m V ≠ ⊤) :
    xNorm d m W ≤ ⨆ (G : ℝ × ℝ → ℂ) (_ : MemLp G 2 (B0579.cellMeasure d (-m)))
      (_ : xNorm d (-m) G ≤ 1), ENNReal.ofReal ‖∫ y in B0579.cell d, W y * G y‖ := by
  have hxW : xNorm d m W = xNorm d m V :=
    eLpNorm_congr_ae ((B0579.cellMeasure_ac d m).ae_le hWV)
  rw [hxW]
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = (xNorm d m V).toReal := ⟨_, rfl⟩
  have hNn : xNorm d m V = ENNReal.ofReal n := by
    rw [hn, ENNReal.ofReal_toReal hfin]
  have hn_nn : 0 ≤ n := by rw [hn]; exact ENNReal.toReal_nonneg
  rcases eq_or_ne n 0 with hn0 | hn0
  · rw [hNn, hn0, ENNReal.ofReal_zero]
    exact zero_le
  obtain ⟨g, hg⟩ : ∃ g : ℝ × ℝ → ℝ, g = fun x => ‖V x‖ ^ 2 * B0579.jb x ^ m := ⟨_, rfl⟩
  have hgnn : ∀ x, 0 ≤ g x := by
    intro x
    rw [hg]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (B0579.jb_pos x).le _)
  have hgm : Measurable g := by
    rw [hg]
    exact (hV.norm.pow_const 2).mul (B0579.continuous_jb_rpow m).measurable
  have hlint : ∫⁻ x in B0579.cell d, ENNReal.ofReal (g x) = xNorm d m V ^ 2 := by
    rw [xNorm_sq_ind, lintegral_indicator (B0579.measurableSet_cell d)]
    refine setLIntegral_congr_fun (B0579.measurableSet_cell d) (fun x _ => ?_)
    simp only [cw, hg]
    rw [ENNReal.ofReal_mul (sq_nonneg _), mul_comm, ← ofReal_norm_eq_enorm,
      ← ENNReal.ofReal_pow (norm_nonneg _)]
    rfl
  have hlint' : ∫⁻ x in B0579.cell d, ENNReal.ofReal (g x) ≠ ⊤ := by
    rw [hlint]
    exact ENNReal.pow_ne_top hfin
  have hgi : Integrable g (volume.restrict (B0579.cell d)) := by
    have hm : AEMeasurable (fun x => ENNReal.ofReal (g x)) (volume.restrict (B0579.cell d)) :=
      (ENNReal.measurable_ofReal.comp hgm).aemeasurable
    refine (integrable_toReal_of_lintegral_ne_top hm hlint').congr
      (Filter.Eventually.of_forall fun x => ?_)
    exact ENNReal.toReal_ofReal (hgnn x)
  have hnum : ∫ x in B0579.cell d, g x = n ^ 2 := by
    have h := ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall hgnn)
    rw [hlint, hNn, ← ENNReal.ofReal_pow hn_nn] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg hgnn) (sq_nonneg n)).1 h
  obtain ⟨G, hG⟩ : ∃ G : ℝ × ℝ → ℂ,
      G = fun x => starRingEnd ℂ (V x) * ((B0579.jb x ^ m : ℝ) : ℂ) / (n : ℂ) := ⟨_, rfl⟩
  have hVG : ∀ x, V x * G x = ((g x / n : ℝ) : ℂ) := by
    intro x
    simp only [hG, hg]
    have h1 : V x * starRingEnd ℂ (V x) = ((‖V x‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    calc V x * (starRingEnd ℂ (V x) * ((B0579.jb x ^ m : ℝ) : ℂ) / (n : ℂ))
        = (V x * starRingEnd ℂ (V x)) * ((B0579.jb x ^ m : ℝ) : ℂ) / (n : ℂ) := by ring
      _ = ((‖V x‖ ^ 2 * B0579.jb x ^ m / n : ℝ) : ℂ) := by
          rw [h1]; push_cast; ring
  have hval : ∫ x in B0579.cell d, W x * G x = ((n : ℝ) : ℂ) := by
    have hae : (fun x => W x * G x) =ᵐ[volume.restrict (B0579.cell d)]
        (fun x => V x * G x) :=
      hWV.mono fun x hx => by simp only [hx]
    rw [integral_congr_ae hae]
    simp_rw [hVG]
    rw [show (∫ x in B0579.cell d, ((g x / n : ℝ) : ℂ)) =
      ((∫ x in B0579.cell d, g x / n : ℝ) : ℂ) from integral_ofReal, integral_div, hnum]
    congr 1
    rw [pow_two, mul_div_assoc, div_self hn0, mul_one]
  have hfinal : xNorm d m V = ENNReal.ofReal ‖∫ y in B0579.cell d, W y * G y‖ := by
    rw [hval, Complex.norm_real, Real.norm_of_nonneg hn_nn, hNn]
  have hGm : Measurable G := by
    rw [hG]
    have hjb : Measurable (fun x => ((B0579.jb x ^ m : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp (B0579.continuous_jb_rpow m).measurable
    exact ((Complex.continuous_conj.measurable.comp hV).mul hjb).div_const _
  have hsq : xNorm d (-m) G ^ 2 = 1 := by
    rw [xNorm_sq_ind, lintegral_indicator (B0579.measurableSet_cell d)]
    have hcongr : ∫⁻ x in B0579.cell d, cw (-m) G x =
        ∫⁻ x in B0579.cell d, ENNReal.ofReal (g x / n ^ 2) := by
      refine setLIntegral_congr_fun (B0579.measurableSet_cell d) (fun x _ => ?_)
      have hGx : ‖G x‖ = ‖V x‖ * B0579.jb x ^ m / n := by
        simp only [hG]
        rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _),
          Real.norm_of_nonneg hn_nn]
      show ENNReal.ofReal (B0579.jb x ^ (-m)) * ‖G x‖ₑ ^ 2 = ENNReal.ofReal (g x / n ^ 2)
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), hGx,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (B0579.jb_pos x).le _)]
      congr 1
      simp only [hg]
      have hjm : B0579.jb x ^ m ≠ 0 := (Real.rpow_pos_of_pos (B0579.jb_pos x) m).ne'
      rw [Real.rpow_neg (B0579.jb_pos x).le]
      field_simp
    rw [hcongr, ← ofReal_integral_eq_lintegral_ofReal (hgi.div_const _)
      (Filter.Eventually.of_forall fun x => div_nonneg (hgnn x) (sq_nonneg _))]
    rw [integral_div, hnum, div_self (pow_ne_zero 2 hn0), ENNReal.ofReal_one]
  have hL : ∫⁻ x, ‖G x‖ₑ ^ 2 ∂(B0579.cellMeasure d (-m)) = 1 :=
    (xNorm_sq d (-m) G).symm.trans hsq
  have hG1 : xNorm d (-m) G ≤ 1 := by
    have h1 : xNorm d (-m) G = 1 := by
      unfold xNorm
      rw [eLpNorm_two_eq_lintegral', hL, ENNReal.one_rpow]
    exact h1.le
  have hGmem : MemLp G 2 (B0579.cellMeasure d (-m)) :=
    ⟨hGm.aestronglyMeasurable, lt_of_le_of_lt hG1 ENNReal.one_lt_top⟩
  exact le_iSup_of_le G (le_iSup_of_le hGmem (le_iSup_of_le hG1 (le_of_eq hfinal)))

end XND

open XND

/-- **`XNormDuality`** (SP 2823-2827, 3036-3040, 3074): the weighted norm of the rescaled
linearised solution on the cell `d = c/√a` is bounded by the supremum of the duality pairings
with the cell test functions, for every `m`. -/
theorem xNormDuality (m : ℝ) : XNormDuality m := by
  unfold XNormDuality
  intro ν hν tr t s ht hts f hf w u hlin
  have hs0 : 0 ≤ s := le_trans ht hts
  have hνs : 0 ≤ ν * s := mul_nonneg hν.le hs0
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have ha : 1 ≤ clockA ν s := by unfold clockA; linarith
  have ha0 : 0 < clockA ν s := by linarith
  have hsq : 0 < Real.sqrt (clockA ν s) := Real.sqrt_pos.2 ha0
  have hd : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν s) := div_pos hc hsq
  have hdc : cellLen (ν ^ (-2 : ℝ)) (clockA ν s) * Real.sqrt (clockA ν s) = ν ^ (-2 : ℝ) := by
    unfold cellLen
    exact div_mul_cancel₀ _ hsq.ne'
  have hw : MemLp (w s) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) := hlin.memX s hts
  have hF0 : AEStronglyMeasurable (w s) (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) := hw.1
  have hFm : Measurable (hF0.mk (w s)) := hF0.stronglyMeasurable_mk.measurable
  have hae : w s =ᵐ[B0579.cellMeasure (ν ^ (-2 : ℝ)) m] hF0.mk (w s) := hF0.ae_eq_mk
  have hvol : w s =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))] hF0.mk (w s) :=
    (B0579.ac_cellMeasure _ m).ae_le hae
  have hWV : JscaleInv (clockA ν s) (w s) =ᵐ[volume.restrict
      (B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)))]
      JscaleInv (clockA ν s) (hF0.mk (w s)) :=
    (jscaleInv_ae_volume ha0 hd hdc hvol.symm).symm
  have hFin : xNorm (ν ^ (-2 : ℝ)) m (hF0.mk (w s)) ≠ ⊤ := by
    have h1 : xNorm (ν ^ (-2 : ℝ)) m (hF0.mk (w s)) = xNorm (ν ^ (-2 : ℝ)) m (w s) :=
      eLpNorm_congr_ae hae.symm
    rw [h1]
    exact hw.2.ne
  exact dual_core (measurable_jscaleInv _ hFm) hWV (xNorm_fin_of_scale ha hd hdc hFin)

end UnforcedLeray.Short.IIIa
