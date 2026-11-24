import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.XNormDuality
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2_1_F1.ChangeVar

/-!
# Dilation helpers for the four `InteractionRescale` leaves (SP 2875-2896, 3052-3057)

Dilation by `√a` maps the cell `cellLen c a = c/√a` onto `cell c`. Helpers:
* test functions are transported by dilations (`isCylTest_dilate`, `isCylTest_div`);
* `pd` of a dilated function (`pd_dilate`);
* the cell-measure pushforward under `x ↦ √a⁻¹ • x` (`map_dilate_restrict`);
* the weighted lintegral comparison for `cellMeasure` under dilation
  (`lintegral_cellMeasure_dilate`), with the density comparison
  `⟨y/√a⟩^{-m} ≤ C ⟨y⟩^{-m}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIIa.E0.RsDil

lemma cellLen_mul_sqrt {c a : ℝ} (ha : 0 < a) :
    UnforcedLeray.Short.IIIa.cellLen c a * Real.sqrt a = c := by
  unfold UnforcedLeray.Short.IIIa.cellLen
  have hs : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  field_simp

lemma smul_sqrt_eq (a : ℝ) (y : ℝ × ℝ) :
    Real.sqrt a • y = (Real.sqrt a * y.1, Real.sqrt a * y.2) := by
  ext <;> simp

/-- Dilation `z ↦ φ(R z)` of a cylinder test of the cell `c` is a test of the cell `c/R`. -/
lemma isCylTest_dilate {c R : ℝ} (hR : 0 < R) {φ : ℝ × ℝ → ℝ}
    (hφ : B0579.IsCylTest c φ) :
    B0579.IsCylTest (c / R) (fun z : ℝ × ℝ => φ (R * z.1, R * z.2)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hφ.smooth.comp ((contDiff_const.mul contDiff_fst).prodMk (contDiff_const.mul contDiff_snd))
  · intro x
    have h : R * (x.1 + c / R) = R * x.1 + c := by field_simp
    show φ (R * (x.1 + c / R), R * x.2) = φ (R * x.1, R * x.2)
    rw [h]
    exact hφ.periodic (R * x.1, R * x.2)
  · obtain ⟨Rb, hb⟩ := hφ.band
    refine ⟨Rb / R, fun x hx => ?_⟩
    have h1 := (div_lt_iff₀ hR).1 hx
    apply hb
    show Rb < |R * x.2|
    rw [abs_mul, abs_of_pos hR]
    linarith [mul_comm R |x.2|]

/-- Dilation by `s⁻¹` written with divisions: `ψ(x/s)` is a test of the cell `c` when `ψ` is a
test of the cell `c/s`. -/
lemma isCylTest_div {c s : ℝ} (hs : 0 < s) {ψ : ℝ × ℝ → ℝ}
    (h : B0579.IsCylTest (c / s) ψ) :
    B0579.IsCylTest c (fun x : ℝ × ℝ => ψ (x.1 / s, x.2 / s)) := by
  have h' := isCylTest_dilate (inv_pos.2 hs) h
  have e : c / s / s⁻¹ = c := by field_simp
  rw [e] at h'
  simp only [div_eq_inv_mul]
  exact h'

/-- `pd` of a dilated function. -/
lemma pd_dilate (s : ℝ) (j : Fin 2) (φ : ℝ × ℝ → ℝ) (hφ : Differentiable ℝ φ) (y : ℝ × ℝ) :
    B0579.pd j (fun z : ℝ × ℝ => φ (s * z.1, s * z.2)) y =
      s * B0579.pd j φ (s * y.1, s * y.2) := by
  obtain ⟨L, hL⟩ : ∃ L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ), ∀ z : ℝ × ℝ, L z = (s * z.1, s * z.2) :=
    ⟨s • ContinuousLinearMap.id ℝ (ℝ × ℝ), fun z => by ext <;> simp⟩
  have hfun : (fun z : ℝ × ℝ => φ (s * z.1, s * z.2)) = φ ∘ L :=
    funext fun z => by simp [hL]
  have h1 : L (B0579.dir j) = s • B0579.dir j := by
    rw [hL]; ext <;> simp
  have hd : HasFDerivAt (φ ∘ L) ((fderiv ℝ φ (L y)).comp L) y :=
    (hφ (L y)).hasFDerivAt.comp y L.hasFDerivAt
  unfold B0579.pd
  rw [hfun, hd.fderiv, ContinuousLinearMap.comp_apply, h1, map_smul, smul_eq_mul, ← hL y]

/-- The horizontal map `z ↦ √a⁻¹ • z` sends the cell `cellLen c a` back to... precisely: a point `z`
lies in `cell (cellLen c a)` iff `√a⁻¹ • z`... see `smul_inv_mem_cell_iff`. -/
lemma smul_inv_mem_cell_iff {c a : ℝ} (ha : 0 < a) (x : ℝ × ℝ) :
    (Real.sqrt a)⁻¹ • x ∈ B0579.cell (UnforcedLeray.Short.IIIa.cellLen c a) ↔
      x ∈ B0579.cell c := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  rw [UnforcedLeray.Short.IIIa.XND.smul_mem_cell_iff_div (inv_pos.2 hs)]
  rw [show UnforcedLeray.Short.IIIa.cellLen c a / (Real.sqrt a)⁻¹ = c from by
    rw [div_inv_eq_mul, UnforcedLeray.Short.IIIa.cellLen, div_mul_cancel₀ c hs.ne']]

/-- Pushforward of the restricted Lebesgue measure on `cell c` under `z ↦ √a⁻¹ • z`. -/
lemma map_dilate_restrict {c a : ℝ} (ha : 0 < a) :
    Measure.map (fun z : ℝ × ℝ => (Real.sqrt a)⁻¹ • z) (volume.restrict (B0579.cell c)) =
      ENNReal.ofReal a • volume.restrict (B0579.cell (UnforcedLeray.Short.IIIa.cellLen c a)) := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hT : Measurable (fun z : ℝ × ℝ => (Real.sqrt a)⁻¹ • z) := measurable_const_smul _
  have hfin : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp [Module.finrank_prod]
  ext S hS
  rw [Measure.map_apply hT hS, Measure.smul_apply, Measure.restrict_apply (hT hS),
    Measure.restrict_apply hS, smul_eq_mul]
  have hset : (fun z : ℝ × ℝ => (Real.sqrt a)⁻¹ • z) ⁻¹' S ∩ B0579.cell c =
      (fun z : ℝ × ℝ => (Real.sqrt a)⁻¹ • z) ⁻¹' (S ∩ B0579.cell (UnforcedLeray.Short.IIIa.cellLen c a)) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    rw [← smul_inv_mem_cell_iff ha x]
  rw [hset, Measure.addHaar_preimage_smul _ (inv_ne_zero hs.ne'), hfin]
  congr 1
  have h2 : ((Real.sqrt a)⁻¹) ^ 2 = a⁻¹ := by rw [inv_pow, Real.sq_sqrt ha.le]
  rw [h2, inv_inv, abs_of_pos ha]

/-- Absolute continuity of an image measure, from null sets. -/
lemma ac_of_preimage {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {ν : Measure α}
    {μ : Measure β} {T : α → β} (hT : Measurable T)
    (h : ∀ S : Set β, MeasurableSet S → μ S = 0 → ν (T ⁻¹' S) = 0) :
    Measure.map T ν ≪ μ := by
  intro S hS
  have hS' := measurableSet_toMeasurable μ S
  have h0 : μ (toMeasurable μ S) = 0 := by rw [measure_toMeasurable]; exact hS
  have hm : Measure.map T ν S ≤ Measure.map T ν (toMeasurable μ S) :=
    measure_mono (subset_toMeasurable μ S)
  rw [Measure.map_apply hT hS'] at hm
  exact le_antisymm (hm.trans (le_of_eq (h _ hS' h0))) zero_le

lemma jb_dilate_eq {a : ℝ} (ha : 0 < a) (x : ℝ × ℝ) :
    B0579.jb ((Real.sqrt a)⁻¹ • x) = 1 + a⁻¹ * (x.1 ^ 2 + x.2 ^ 2) := by
  have hs2 : ((Real.sqrt a)⁻¹) ^ 2 = a⁻¹ := by rw [inv_pow, Real.sq_sqrt ha.le]
  unfold B0579.jb
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [← hs2]
  ring

lemma jb_dilate_bounds {a : ℝ} (ha : 0 < a) (x : ℝ × ℝ) :
    min 1 a⁻¹ * B0579.jb x ≤ B0579.jb ((Real.sqrt a)⁻¹ • x) ∧
      B0579.jb ((Real.sqrt a)⁻¹ • x) ≤ max 1 a⁻¹ * B0579.jb x := by
  rw [jb_dilate_eq ha]
  have hj : B0579.jb x = 1 + (x.1 ^ 2 + x.2 ^ 2) := by unfold B0579.jb; ring
  rw [hj]
  have ht : 0 ≤ x.1 ^ 2 + x.2 ^ 2 := by positivity
  constructor
  · nlinarith [min_le_left 1 a⁻¹, min_le_right 1 a⁻¹, mul_le_mul_of_nonneg_right (min_le_right 1 a⁻¹) ht]
  · nlinarith [le_max_left 1 a⁻¹, le_max_right 1 a⁻¹, mul_le_mul_of_nonneg_right (le_max_right 1 a⁻¹) ht]

lemma rpow_jb_dilate_le {a : ℝ} (ha : 0 < a) (p : ℝ) (x : ℝ × ℝ) :
    B0579.jb ((Real.sqrt a)⁻¹ • x) ^ p ≤
      ((min 1 a⁻¹) ^ p + (max 1 a⁻¹) ^ p) * B0579.jb x ^ p := by
  obtain ⟨hlo, hhi⟩ := jb_dilate_bounds ha x
  have hlo0 : 0 < min 1 a⁻¹ := lt_min one_pos (inv_pos.2 ha)
  have hhi0 : 0 < max 1 a⁻¹ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hj0 : 0 < B0579.jb x := B0579.jb_pos x
  have hjd : 0 < B0579.jb ((Real.sqrt a)⁻¹ • x) := B0579.jb_pos _
  have hpos_p : 0 ≤ B0579.jb x ^ p := Real.rpow_nonneg hj0.le p
  have hlo_p : 0 ≤ (min 1 a⁻¹) ^ p := Real.rpow_nonneg hlo0.le p
  have hhi_p : 0 ≤ (max 1 a⁻¹) ^ p := Real.rpow_nonneg hhi0.le p
  rcases le_total 0 p with hp | hp
  · calc B0579.jb ((Real.sqrt a)⁻¹ • x) ^ p ≤ (max 1 a⁻¹ * B0579.jb x) ^ p :=
          Real.rpow_le_rpow hjd.le hhi hp
      _ = (max 1 a⁻¹) ^ p * B0579.jb x ^ p := Real.mul_rpow hhi0.le hj0.le
      _ ≤ _ := by nlinarith [mul_nonneg hlo_p hpos_p, mul_nonneg hhi_p hpos_p]
  · calc B0579.jb ((Real.sqrt a)⁻¹ • x) ^ p ≤ (min 1 a⁻¹ * B0579.jb x) ^ p :=
          Real.rpow_le_rpow_of_nonpos (mul_pos hlo0 hj0) hlo hp
      _ = (min 1 a⁻¹) ^ p * B0579.jb x ^ p := Real.mul_rpow hlo0.le hj0.le
      _ ≤ _ := by nlinarith [mul_nonneg hlo_p hpos_p, mul_nonneg hhi_p hpos_p]

lemma density_dilate_le {a : ℝ} (ha : 0 < a) (p : ℝ) (x : ℝ × ℝ) :
    ((B0579.density p ((Real.sqrt a)⁻¹ • x) : ℝ≥0) : ℝ≥0∞) ≤
      ENNReal.ofReal ((min 1 a⁻¹) ^ p + (max 1 a⁻¹) ^ p) *
        ((B0579.density p x : ℝ≥0) : ℝ≥0∞) := by
  have hC : 0 ≤ (min 1 a⁻¹) ^ p + (max 1 a⁻¹) ^ p := by positivity
  have e : ∀ z : ℝ × ℝ, ((B0579.density p z : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (B0579.jb z ^ p) :=
    fun z => rfl
  rw [e, e, ← ENNReal.ofReal_mul hC]
  exact ENNReal.ofReal_le_ofReal (rpow_jb_dilate_le ha p x)

/-- Weighted lintegral comparison under dilation, for the `cellMeasure` of the moving cell
`cellLen c a` against the fixed cell `c`. -/
lemma lintegral_cellMeasure_dilate {a c : ℝ} (hc : 0 < c) (ha : 0 < a) (p : ℝ)
    (F : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ y, F (Real.sqrt a • y) ∂(B0579.cellMeasure (UnforcedLeray.Short.IIIa.cellLen c a) p) ≤
      ENNReal.ofReal a⁻¹ * (ENNReal.ofReal ((min 1 a⁻¹) ^ p + (max 1 a⁻¹) ^ p) *
        ∫⁻ x, F x ∂(B0579.cellMeasure c p)) := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hs0 : Real.sqrt a ≠ 0 := hs.ne'
  have hC : 0 ≤ (min 1 a⁻¹) ^ p + (max 1 a⁻¹) ^ p := by positivity
  -- the integrand `K` on the fixed cell
  set K : ℝ × ℝ → ℝ≥0∞ := fun x => ((B0579.density p ((Real.sqrt a)⁻¹ • x) : ℝ≥0) : ℝ≥0∞) * F x
    with hK
  have hKs : ∀ y : ℝ × ℝ, K (Real.sqrt a • y) =
      ((B0579.density p y : ℝ≥0) : ℝ≥0∞) * F (Real.sqrt a • y) := by
    intro y
    simp only [hK, inv_smul_smul₀ hs0]
  have hscale := UnforcedLeray.Short.IIIa.XND.lintegral_cell_scale_ind
    (d := UnforcedLeray.Short.IIIa.cellLen c a) (R := Real.sqrt a) hs K
  rw [cellLen_mul_sqrt ha, Real.sq_sqrt ha.le] at hscale
  have hL : ∫⁻ y, F (Real.sqrt a • y) ∂(B0579.cellMeasure (UnforcedLeray.Short.IIIa.cellLen c a) p) =
      ENNReal.ofReal a⁻¹ * ∫⁻ x, (B0579.cell c).indicator K x := by
    rw [UnforcedLeray.Short.IIIa.XND.lintegral_cellMeasure_eq, hscale, ← mul_assoc,
      ← ENNReal.ofReal_mul (inv_nonneg.2 ha.le), inv_mul_cancel₀ ha.ne', ENNReal.ofReal_one,
      one_mul]
    congr 1
    funext y
    simp only [hKs]
  rw [hL]
  have hpt : ∀ x : ℝ × ℝ, (B0579.cell c).indicator K x ≤
      ENNReal.ofReal ((min 1 a⁻¹) ^ p + (max 1 a⁻¹) ^ p) *
        (B0579.cell c).indicator (fun x => ((B0579.density p x : ℝ≥0) : ℝ≥0∞) * F x) x := by
    intro x
    by_cases hx : x ∈ B0579.cell c
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      simp only [hK]
      calc ((B0579.density p ((Real.sqrt a)⁻¹ • x) : ℝ≥0) : ℝ≥0∞) * F x
          ≤ (ENNReal.ofReal ((min 1 a⁻¹) ^ p + (max 1 a⁻¹) ^ p) *
              ((B0579.density p x : ℝ≥0) : ℝ≥0∞)) * F x :=
            by gcongr; exact density_dilate_le ha p x
        _ = ENNReal.ofReal ((min 1 a⁻¹) ^ p + (max 1 a⁻¹) ^ p) *
              (((B0579.density p x : ℝ≥0) : ℝ≥0∞) * F x) := mul_assoc _ _ _
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      exact zero_le
  have hint : ∫⁻ x, (B0579.cell c).indicator K x ≤
      ENNReal.ofReal ((min 1 a⁻¹) ^ p + (max 1 a⁻¹) ^ p) *
        ∫⁻ x, (B0579.cell c).indicator (fun x => ((B0579.density p x : ℝ≥0) : ℝ≥0∞) * F x) x := by
    calc ∫⁻ x, (B0579.cell c).indicator K x
        ≤ ∫⁻ x, ENNReal.ofReal ((min 1 a⁻¹) ^ p + (max 1 a⁻¹) ^ p) *
            (B0579.cell c).indicator (fun x => ((B0579.density p x : ℝ≥0) : ℝ≥0∞) * F x) x :=
          lintegral_mono hpt
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [UnforcedLeray.Short.IIIa.XND.lintegral_cellMeasure_eq c p F]
  gcongr

end UnforcedLeray.Short.IIIa.E0.RsDil
