import UnforcedLeray.Short.PartIIIa.Targets

/-!
# T08: dual scaling bound for `J_a⁻¹` (SP 2986-2989)

Proves `UnforcedLeray.Short.IIIa.scalingJaInvDual` (the `Prop` `ScalingJaInvDual` of `Targets.lean`):
for `m ≥ 0`, `a ≥ 1`, `d` and any `f`,
`negNorm d m (JscaleInv a f) ≤ ofReal (a^(3/2)) * negNorm (d * √a) m f`.

Proof, with `R = √a ≥ 1` and the dilations `dilF R φ (x) = R⁻¹ φ(R⁻¹ x)`,
`dilG R g (x) = (R²)⁻¹ g(R⁻¹ x)`:
* `∫_{cell d} (J_a⁻¹ f) φ = a^{3/2} ∫_{cell (d R)} f (dilF R φ)` (change of variables `x = R y`).
* `(dilF R φ, dilG R g)` is admissible for the cell `d R`: the weak derivative identity is pulled
  back by the test function `y ↦ ψ(R y)`, which is a cylinder test for the cell `d`.
* `h1Norm (d R) m (dilF R φ) (dilG R g) ≤ h1Norm d m φ g`, since the weight satisfies
  `⟨R y⟩^{-2m} ≤ ⟨y⟩^{-2m}` for `m ≥ 0` and `R ≥ 1`.
Hence the supremum defining `negNorm d m (J_a⁻¹ f)` is at most `a^{3/2}` times `negNorm (d R) m f`.

Source of record: `the November 2 reference manuscript` (SP), lines 2986-2989.
Helpers live in the namespace `T08`; the cell and lintegral change-of-variables helpers are
self-contained copies of the T07 helpers, so this file does not depend on the T07 compile state.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIIa

namespace T08

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

/-- The density weight decreases under dilation by `R ≥ 1` for exponent `p ≤ 0`. -/
lemma density_dilate_le {R p : ℝ} (hR : 1 ≤ R) (hp : p ≤ 0) (y : ℝ × ℝ) :
    ((B0579.density p (R • y) : ℝ≥0) : ℝ≥0∞) ≤ ((B0579.density p y : ℝ≥0) : ℝ≥0∞) := by
  have hjb : B0579.jb y ≤ B0579.jb (R • y) := by
    unfold B0579.jb
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have hR2 : 1 ≤ R ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.2 hR2) (add_nonneg (sq_nonneg y.1) (sq_nonneg y.2))]
  show ENNReal.ofReal (B0579.jb (R • y) ^ p) ≤ ENNReal.ofReal (B0579.jb y ^ p)
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (B0579.jb_pos y) hjb hp)

/-- Scaling inequality for the weighted lintegral on the cell:
if `F (R y) = κ G(y)` then `∫⁻_{cell (dR)} ⟨x⟩^{2p}‖F‖² ≤ R² κ² ∫⁻_{cell d} ⟨y⟩^{2p}‖G‖²`. -/
lemma cellQ_scale_le {d R p κ : ℝ} (hR : 1 ≤ R) (hp : p ≤ 0) {F G : ℝ × ℝ → ℂ}
    (hFG : ∀ y, F (R • y) = (κ : ℂ) * G y) :
    ∫⁻ x, ‖F x‖ₑ ^ 2 ∂(B0579.cellMeasure (d * R) p) ≤
      ENNReal.ofReal (R ^ 2) * ENNReal.ofReal (κ ^ 2) *
        ∫⁻ y, ‖G y‖ₑ ^ 2 ∂(B0579.cellMeasure d p) := by
  have hR0 : 0 < R := by linarith
  have hpt : ∀ y : ℝ × ℝ, (B0579.cell d).indicator (fun y => cw p F (R • y)) y ≤
      ENNReal.ofReal (κ ^ 2) * (B0579.cell d).indicator (cw p G) y := by
    intro y
    by_cases hy : y ∈ B0579.cell d
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      unfold cw
      rw [hFG y, enorm_real_mul_sq]
      calc ((B0579.density p (R • y) : ℝ≥0) : ℝ≥0∞) * (ENNReal.ofReal (κ ^ 2) * ‖G y‖ₑ ^ 2)
          ≤ ((B0579.density p y : ℝ≥0) : ℝ≥0∞) * (ENNReal.ofReal (κ ^ 2) * ‖G y‖ₑ ^ 2) :=
            mul_le_mul_of_nonneg_right (density_dilate_le hR hp y) (zero_le)
        _ = ENNReal.ofReal (κ ^ 2) * (((B0579.density p y : ℝ≥0) : ℝ≥0∞) * ‖G y‖ₑ ^ 2) := by
            ring
    · rw [Set.indicator_of_notMem hy]
      exact zero_le
  rw [cellQ_eq, cellQ_eq, lintegral_cell_scale_ind hR0]
  calc ENNReal.ofReal (R ^ 2) * ∫⁻ y, (B0579.cell d).indicator (fun y => cw p F (R • y)) y
      ≤ ENNReal.ofReal (R ^ 2) *
          ∫⁻ y, ENNReal.ofReal (κ ^ 2) * (B0579.cell d).indicator (cw p G) y :=
        mul_le_mul_of_nonneg_left (lintegral_mono hpt) (zero_le)
    _ = ENNReal.ofReal (R ^ 2) * ENNReal.ofReal (κ ^ 2) *
          ∫⁻ y, (B0579.cell d).indicator (cw p G) y := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_assoc]

/-- Norm comparison under the dilation: `xNorm (dR) p F ^ 2 ≤ xNorm d p G ^ 2` whenever
`R² κ² ≤ 1` and `F (R·) = κ G`, for `p ≤ 0`, `R ≥ 1`. -/
lemma xNorm_dilate_le {d R p κ : ℝ} (hR : 1 ≤ R) (hp : p ≤ 0) {F G : ℝ × ℝ → ℂ}
    (hκ : R ^ 2 * κ ^ 2 ≤ 1) (hFG : ∀ y, F (R • y) = (κ : ℂ) * G y) :
    xNorm (d * R) p F ^ 2 ≤ xNorm d p G ^ 2 := by
  rw [xNorm_sq, xNorm_sq]
  refine (cellQ_scale_le hR hp hFG).trans ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg R)]
  exact mul_le_of_le_one_left (zero_le) (ENNReal.ofReal_le_one.2 hκ)

/-! ## Dilated functions and cylinder tests -/

/-- The dilated function `x ↦ R⁻¹ φ(R⁻¹ x)`, i.e. `φ(·/√a)/√a` (SP 2986). -/
def dilF (R : ℝ) (φ : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  fun x => ((R⁻¹ : ℝ) : ℂ) * φ (R⁻¹ • x)

/-- The dilated weak gradient `x ↦ (R²)⁻¹ g(R⁻¹ x)`, i.e. `a⁻¹ g(·/√a)`. -/
def dilG (R : ℝ) (gj : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  fun x => (((R ^ 2)⁻¹ : ℝ) : ℂ) * gj (R⁻¹ • x)

lemma dilF_smul {R : ℝ} (hR : 0 < R) (φ : ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    dilF R φ (R • y) = ((R⁻¹ : ℝ) : ℂ) * φ y := by
  unfold dilF
  rw [inv_smul_smul₀ hR.ne' y]

lemma dilG_smul {R : ℝ} (hR : 0 < R) (gj : ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    dilG R gj (R • y) = (((R ^ 2)⁻¹ : ℝ) : ℂ) * gj y := by
  unfold dilG
  rw [inv_smul_smul₀ hR.ne' y]

lemma sqrt_smul_eq' (a : ℝ) (y : ℝ × ℝ) :
    Real.sqrt a • y = (Real.sqrt a * y.1, Real.sqrt a * y.2) := by
  ext <;> simp

/-- `J_a⁻¹ f(y) = a² f(√a y)` (SP 2983). -/
lemma jscale_eq (a : ℝ) (f : ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    JscaleInv a f y = ((a ^ 2 : ℝ) : ℂ) * f (Real.sqrt a • y) := by
  unfold JscaleInv
  rw [sqrt_smul_eq']

/-- Pull-back of a cylinder test by a dilation: `y ↦ ψ(R y)` is a cylinder test for the cell
`d` when `ψ` is one for the cell `d R`. -/
lemma isCylTest_dilate {d R : ℝ} (hR : 0 < R) {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest (d * R) ψ) :
    B0579.IsCylTest d (fun z => ψ (R • z)) where
  smooth := hψ.smooth.comp (contDiff_id.const_smul R)
  periodic x := by
    show ψ (R • (x.1 + d, x.2)) = ψ (R • x)
    have e : R • ((x.1 + d, x.2) : ℝ × ℝ) = ((R • x).1 + d * R, (R • x).2) := by
      ext <;> simp [smul_eq_mul] <;> ring
    rw [e]
    exact hψ.periodic (R • x)
  band := by
    obtain ⟨R0, hR0⟩ := hψ.band
    refine ⟨R0 / R, fun x hx => ?_⟩
    show ψ (R • x) = 0
    apply hR0 (R • x)
    simp only [Prod.smul_snd, smul_eq_mul]
    rw [abs_mul, abs_of_pos hR]
    have := (div_lt_iff₀ hR).1 hx
    linarith

/-- Dilation of the classical partial derivative: `∂_j (ψ(R·))(y) = R (∂_j ψ)(R y)`. -/
lemma pd_dilate (j : Fin 2) {ψ : ℝ × ℝ → ℝ} (hψ : Differentiable ℝ ψ) (R : ℝ) (y : ℝ × ℝ) :
    B0579.pd j (fun z => ψ (R • z)) y = R * B0579.pd j ψ (R • y) := by
  have hS : HasFDerivAt (fun z : ℝ × ℝ => R • z) (R • ContinuousLinearMap.id ℝ (ℝ × ℝ)) y :=
    (hasFDerivAt_id y).const_smul R
  have hc := (hψ (R • y)).hasFDerivAt.comp y hS
  change fderiv ℝ (ψ ∘ fun z => R • z) y (B0579.dir j) = _
  rw [hc.fderiv]
  simp [B0579.pd, smul_eq_mul]

/-- Admissibility transfer: a weak gradient on the cell `d` gives one for the dilated pair on the
cell `d R`, with the dilated gradient. -/
lemma hasWeakCellDeriv_dilate {d R : ℝ} (hR : 1 ≤ R) (j : Fin 2) {φ gj : ℝ × ℝ → ℂ}
    (hw : HasWeakCellDerivC d j φ gj) :
    HasWeakCellDerivC (d * R) j (dilF R φ) (dilG R gj) := by
  have hR0 : 0 < R := by linarith
  have hR0' : R ≠ 0 := hR0.ne'
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR0'
  unfold HasWeakCellDerivC at hw ⊢
  refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · have hψ' : B0579.IsCylTest d (fun z => ψ (R • z)) := isCylTest_dilate hR0 hψ
    obtain ⟨hI1, hI2⟩ := hw.1 _ hψ'
    refine ⟨?_, ?_⟩
    · have h := integrableOn_cell_scale (R := R⁻¹) (inv_pos.2 hR0) hI1
      rw [div_inv_eq_mul] at h
      refine IntegrableOn.congr_fun (Integrable.const_mul h (((R ^ 2)⁻¹ : ℝ) : ℂ)) ?_
        (B0579.measurableSet_cell _)
      intro x _
      show (((R ^ 2)⁻¹ : ℝ) : ℂ) * (φ (R⁻¹ • x) *
          ((B0579.pd j (fun z => ψ (R • z)) (R⁻¹ • x) : ℝ) : ℂ)) =
        dilF R φ x * ((B0579.pd j ψ x : ℝ) : ℂ)
      rw [pd_dilate j hψ.differentiable R (R⁻¹ • x), smul_inv_smul₀ hR0' x]
      unfold dilF
      push_cast
      field_simp
    · have h := integrableOn_cell_scale (R := R⁻¹) (inv_pos.2 hR0) hI2
      rw [div_inv_eq_mul] at h
      refine IntegrableOn.congr_fun (Integrable.const_mul h (((R ^ 2)⁻¹ : ℝ) : ℂ)) ?_
        (B0579.measurableSet_cell _)
      intro x _
      show (((R ^ 2)⁻¹ : ℝ) : ℂ) * (gj (R⁻¹ • x) * ((ψ (R • (R⁻¹ • x)) : ℝ) : ℂ)) =
        dilG R gj x * ((ψ x : ℝ) : ℂ)
      rw [smul_inv_smul₀ hR0' x]
      unfold dilG
      ring
  · have hψ' : B0579.IsCylTest d (fun z => ψ (R • z)) := isCylTest_dilate hR0 hψ
    have hL := hw.2 _ hψ'
    have hdiff : Differentiable ℝ ψ := hψ.differentiable
    have e1 : ∀ y : ℝ × ℝ, dilF R φ (R • y) * ((B0579.pd j ψ (R • y) : ℝ) : ℂ) =
        (((R ^ 2)⁻¹ : ℝ) : ℂ) * (φ y * ((B0579.pd j (fun z => ψ (R • z)) y : ℝ) : ℂ)) := by
      intro y
      rw [dilF_smul hR0 φ y, pd_dilate j hdiff R y]
      push_cast
      field_simp
    have hI1 : ∫ y in B0579.cell d, dilF R φ (R • y) * ((B0579.pd j ψ (R • y) : ℝ) : ℂ) =
        (((R ^ 2)⁻¹ : ℝ) : ℂ) *
          ∫ y in B0579.cell d, φ y * ((B0579.pd j (fun z => ψ (R • z)) y : ℝ) : ℂ) := by
      rw [← integral_const_mul]
      congr 1
      funext y
      exact e1 y
    have hI2 : ∫ y in B0579.cell d, dilG R gj (R • y) * ((ψ (R • y) : ℝ) : ℂ) =
        (((R ^ 2)⁻¹ : ℝ) : ℂ) * ∫ y in B0579.cell d, gj y * ((ψ (R • y) : ℝ) : ℂ) := by
      rw [← integral_const_mul]
      congr 1
      funext y
      rw [dilG_smul hR0 gj y]
      ring
    have hS1 : ∫ x in B0579.cell (d * R), dilF R φ x * ((B0579.pd j ψ x : ℝ) : ℂ) =
        ((R ^ 2 : ℝ) : ℂ) *
          ∫ y in B0579.cell d, dilF R φ (R • y) * ((B0579.pd j ψ (R • y) : ℝ) : ℂ) :=
      integral_cell_scale hR0 (fun x => dilF R φ x * ((B0579.pd j ψ x : ℝ) : ℂ))
    have hS2 : ∫ x in B0579.cell (d * R), dilG R gj x * ((ψ x : ℝ) : ℂ) =
        ((R ^ 2 : ℝ) : ℂ) * ∫ y in B0579.cell d, dilG R gj (R • y) * ((ψ (R • y) : ℝ) : ℂ) :=
      integral_cell_scale hR0 (fun x => dilG R gj x * ((ψ x : ℝ) : ℂ))
    rw [hS1, hS2, hI1, hI2, hL]
    ring

/-- The `h1Norm` bound under the dilation: the weights satisfy `⟨Ry⟩^{-2m} ≤ ⟨y⟩^{-2m}` for
`m ≥ 0`, `R ≥ 1`, and the gradient factor `(R²)⁻¹ ≤ 1`. -/
lemma h1Norm_dilate_le {d R m : ℝ} (hR : 1 ≤ R) (hm : 0 ≤ m) (φ : ℝ × ℝ → ℂ)
    (g : Fin 2 → ℝ × ℝ → ℂ) :
    h1Norm (d * R) m (dilF R φ) (fun j => dilG R (g j)) ≤ h1Norm d m φ g := by
  have hp : -m ≤ 0 := by linarith
  have hR0 : 0 < R := by linarith
  have hR0' : R ≠ 0 := hR0.ne'
  have hR2 : 1 ≤ R ^ 2 := by nlinarith
  have hκ1 : R ^ 2 * (R⁻¹) ^ 2 ≤ 1 := by
    have e : R ^ 2 * (R⁻¹) ^ 2 = 1 := by
      rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 hR0')]
    exact e.le
  have hκ2 : R ^ 2 * ((R ^ 2)⁻¹) ^ 2 ≤ 1 := by
    calc R ^ 2 * ((R ^ 2)⁻¹) ^ 2 = (R ^ 2)⁻¹ * (R ^ 2 * (R ^ 2)⁻¹) := by ring
      _ = (R ^ 2)⁻¹ := by rw [mul_inv_cancel₀ (pow_ne_zero 2 hR0'), mul_one]
      _ ≤ 1 := inv_le_one_of_one_le₀ hR2
  have hbase : xNorm (d * R) (-m) (dilF R φ) ^ 2 +
      ∑ j, xNorm (d * R) (-m) (dilG R (g j)) ^ 2 ≤
      xNorm d (-m) φ ^ 2 + ∑ j, xNorm d (-m) (g j) ^ 2 := by
    refine add_le_add ?_ (Finset.sum_le_sum fun j _ => ?_)
    · exact xNorm_dilate_le hR hp hκ1 (fun y => dilF_smul hR0 φ y)
    · exact xNorm_dilate_le hR hp hκ2 (fun y => dilG_smul hR0 (g j) y)
  unfold h1Norm
  exact ENNReal.rpow_le_rpow hbase (by norm_num)

end T08

open T08

/-- **`ScalingJaInvDual`** (SP 2986-2989): `‖J_a⁻¹ f‖_{(H^1_{-m,d})^*} ≤ a^{3/2}‖f‖_{(H^1_{-m,c})^*}`,
`c = √a d`, for `m ≥ 0`, `a ≥ 1`, `d` and any `f`. -/
theorem scalingJaInvDual : UnforcedLeray.Short.IIIa.ScalingJaInvDual := by
  unfold ScalingJaInvDual
  intro m hm a d ha _hd f _hf
  have ha0 : 0 < a := by linarith
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, Real.sqrt a = R := ⟨_, rfl⟩
  have hR2 : R ^ 2 = a := by rw [← hRdef]; exact Real.sq_sqrt ha0.le
  have hR1 : 1 ≤ R := by rw [← hRdef]; exact Real.one_le_sqrt.2 ha
  have hR0 : 0 < R := by linarith
  have hR0' : R ≠ 0 := hR0.ne'
  have hJ : ∀ y : ℝ × ℝ, JscaleInv a f y = ((a ^ 2 : ℝ) : ℂ) * f (R • y) := fun y => by
    rw [jscale_eq, hRdef]
  have h32 : a ^ (3 / 2 : ℝ) = a * R := by
    rw [← hRdef, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ha0, Real.rpow_one,
      Real.sqrt_eq_rpow]
  have hreal : a ^ 2 = a ^ (3 / 2 : ℝ) * R ^ 2 * R⁻¹ := by
    rw [h32, hR2, show a * R * a * R⁻¹ = a ^ 2 * (R * R⁻¹) by ring,
      mul_inv_cancel₀ hR0', mul_one]
  have hsc : ((a ^ 2 : ℝ) : ℂ) =
      ((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) * ((R ^ 2 : ℝ) : ℂ) * ((R⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← hreal]
  rw [hRdef]
  refine iSup_le fun φ => iSup_le fun g => iSup_le fun hw => iSup_le fun hh => ?_
  have hw₀ : ∀ j, HasWeakCellDerivC (d * R) j (dilF R φ) ((fun j => dilG R (g j)) j) :=
    fun j => hasWeakCellDeriv_dilate hR1 j (hw j)
  have hh₀ : h1Norm (d * R) m (dilF R φ) (fun j => dilG R (g j)) ≤ 1 :=
    le_trans (h1Norm_dilate_le hR1 hm φ g) hh
  have hI' : ENNReal.ofReal ‖∫ x in B0579.cell (d * R), f x * dilF R φ x‖ ≤
      negNorm (d * R) m f := by
    unfold negNorm
    exact le_iSup_of_le (dilF R φ) (le_iSup_of_le (fun j => dilG R (g j))
      (le_iSup_of_le hw₀ (le_iSup_of_le hh₀ le_rfl)))
  have hkey : ∫ x in B0579.cell d, JscaleInv a f x * φ x =
      ((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) * ∫ x in B0579.cell (d * R), f x * dilF R φ x := by
    have h1 : ∫ x in B0579.cell (d * R), f x * dilF R φ x =
        ((R ^ 2 : ℝ) : ℂ) * ∫ y in B0579.cell d, f (R • y) * dilF R φ (R • y) :=
      integral_cell_scale hR0 (fun x => f x * dilF R φ x)
    have h2 : ∫ y in B0579.cell d, f (R • y) * dilF R φ (R • y) =
        ((R⁻¹ : ℝ) : ℂ) * ∫ y in B0579.cell d, f (R • y) * φ y := by
      rw [← integral_const_mul]
      congr 1
      funext y
      rw [dilF_smul hR0 φ y]
      ring
    have h3 : ∫ x in B0579.cell d, JscaleInv a f x * φ x =
        ((a ^ 2 : ℝ) : ℂ) * ∫ y in B0579.cell d, f (R • y) * φ y := by
      rw [← integral_const_mul]
      congr 1
      funext y
      rw [hJ y]
      ring
    rw [h1, h2, h3, hsc]
    ring
  rw [hkey, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg ha0.le _),
    ENNReal.ofReal_mul (Real.rpow_nonneg ha0.le _)]
  exact mul_le_mul_of_nonneg_left hI' (zero_le)

end UnforcedLeray.Short.IIIa
