import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PositiveKernel

/-!
# The `L¹` tail of `|x|^{-4}` on `ℝ³` (source 3999-4000)

Proves `tailL1_holds : TailL1` (defined in `Sub/PositiveKernel.lean`).
Route: dilation `∫ K(l z) dz = l^{-3} ∫ K` with `l = d` applied to the indicator of
`{d ≤ ‖x‖}`, which turns the tail into `d^{-1}` times the tail above radius `1`; the tail above
radius `1` is bounded by `16` times the finite integral of `(1 + ‖x‖)^{-4}` (Japanese bracket).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- Dilation of a lower Lebesgue integral on `ℝ³`: `∫ K(l z) dz = (l³)⁻¹ ∫ K`. -/
private lemma tl_dil (l : ℝ) (hl : 0 < l) (K : UnforcedLeray.Space → ℝ≥0∞) (hK : Measurable K) :
    ∫⁻ z, K (l • z) = ENNReal.ofReal ((l ^ 3)⁻¹) * ∫⁻ w, K w := by
  have hmap := Measure.map_addHaar_smul (μ := (volume : Measure UnforcedLeray.Space)) hl.ne'
  have hm : Measurable (fun z : UnforcedLeray.Space => l • z) :=
    (continuous_const_smul l).measurable
  have h1 : ∫⁻ z, K (l • z) =
      ∫⁻ w, K w ∂(Measure.map (fun z : UnforcedLeray.Space => l • z) volume) :=
    (lintegral_map hK hm).symm
  rw [h1, hmap, lintegral_smul_measure, finrank_euclideanSpace_fin]
  congr 1
  rw [abs_of_nonneg (by positivity)]

/-- `m^{-4} = (m^4)⁻¹` for `m ≥ 0`. -/
private lemma tl_rpow_neg_four (m : ℝ) (hm : 0 ≤ m) : m ^ (-4 : ℝ) = (m ^ 4)⁻¹ := by
  rw [Real.rpow_neg hm, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- **The `L¹` tail** (source 3999-4000). -/
theorem tailL1_holds : TailL1 := by
  -- finiteness of the Japanese-bracket integral on `ℝ³`
  have hint : Integrable (fun x : UnforcedLeray.Space => (1 + ‖x‖) ^ (-(4 : ℝ))) :=
    integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; norm_num)
  obtain ⟨J, hJdef⟩ : ∃ J : ℝ≥0∞,
      J = ∫⁻ w : UnforcedLeray.Space, ENNReal.ofReal ((1 + ‖w‖) ^ (-(4 : ℝ))) := ⟨_, rfl⟩
  have hJfin : J < ⊤ := by
    rw [hJdef]
    exact hint.lintegral_lt_top
  obtain ⟨Jr, hJr0, hJr⟩ : ∃ r : ℝ, 0 ≤ r ∧ J = ENNReal.ofReal r :=
    ⟨J.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hJfin.ne).symm⟩
  refine ⟨16 * Jr, by positivity, ?_⟩
  intro d hd
  -- the tail and the radius-one tail as indicators
  set S : Set UnforcedLeray.Space := {x : UnforcedLeray.Space | d ≤ ‖x‖} with hSdef
  have hSmeas : MeasurableSet S := measurableSet_le measurable_const measurable_norm
  set F : UnforcedLeray.Space → ℝ≥0∞ :=
    S.indicator (fun x => ENNReal.ofReal (‖x‖ ^ (-4 : ℝ))) with hF
  set T : Set UnforcedLeray.Space := {x : UnforcedLeray.Space | 1 ≤ ‖x‖} with hTdef
  have hTmeas : MeasurableSet T := measurableSet_le measurable_const measurable_norm
  set G : UnforcedLeray.Space → ℝ≥0∞ :=
    T.indicator (fun x => ENNReal.ofReal (‖x‖ ^ (-4 : ℝ))) with hG
  have hnormpow : Measurable (fun x : UnforcedLeray.Space => ENNReal.ofReal (‖x‖ ^ (-4 : ℝ))) :=
    ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)
  have hFmeas : Measurable F := hnormpow.indicator hSmeas
  have hGmeas : Measurable G := hnormpow.indicator hTmeas
  have hLHS : ∫⁻ x in S, ENNReal.ofReal (‖x‖ ^ (-4 : ℝ)) = ∫⁻ x, F x := by
    rw [hF, lintegral_indicator hSmeas]
  -- pointwise dilation identity `F(d z) = d^{-4} G(z)`
  have hpt : ∀ z : UnforcedLeray.Space, F (d • z) = ENNReal.ofReal (d ^ (-4 : ℝ)) * G z := by
    intro z
    by_cases hz : 1 ≤ ‖z‖
    · have hmem1 : d • z ∈ S := by
        show d ≤ ‖d • z‖
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd]
        exact le_mul_of_one_le_right hd.le hz
      have hmem2 : z ∈ T := hz
      rw [hF, hG, Set.indicator_of_mem hmem1, Set.indicator_of_mem hmem2]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _), Real.mul_rpow hd.le (norm_nonneg z)]
    · have hnmem1 : d • z ∉ S := by
        show ¬ (d ≤ ‖d • z‖)
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd]
        exact not_le.mpr (mul_lt_of_lt_one_right hd (not_le.mp hz))
      have hnmem2 : z ∉ T := hz
      rw [hF, hG, Set.indicator_of_notMem hnmem1, Set.indicator_of_notMem hnmem2, mul_zero]
  -- dilation: `(d^3)⁻¹ ∫F = d^{-4} ∫G`
  have h1 : ∫⁻ z, F (d • z) = ENNReal.ofReal ((d ^ 3)⁻¹) * ∫⁻ w, F w :=
    tl_dil d hd F hFmeas
  have h2 : ∫⁻ z, F (d • z) = ENNReal.ofReal (d ^ (-4 : ℝ)) * ∫⁻ z, G z := by
    calc ∫⁻ z, F (d • z) = ∫⁻ z, ENNReal.ofReal (d ^ (-4 : ℝ)) * G z :=
          lintegral_congr fun z => hpt z
      _ = ENNReal.ofReal (d ^ (-4 : ℝ)) * ∫⁻ z, G z := lintegral_const_mul _ hGmeas
  have hkey : ENNReal.ofReal ((d ^ 3)⁻¹) * ∫⁻ w, F w = ENNReal.ofReal (d ^ (-4 : ℝ)) * ∫⁻ z, G z :=
    h1.symm.trans h2
  have hcancel : ∫⁻ w, F w =
      ENNReal.ofReal (d ^ 3) * (ENNReal.ofReal ((d ^ 3)⁻¹) * ∫⁻ w, F w) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ d ^ 3),
      mul_inv_cancel₀ (by positivity : d ^ 3 ≠ 0), ENNReal.ofReal_one, one_mul]
  -- the radius-one tail is at most `16 ∫ (1 + |x|)^{-4}`
  have hpt16 : ∀ x : UnforcedLeray.Space,
      G x ≤ ENNReal.ofReal 16 * ENNReal.ofReal ((1 + ‖x‖) ^ (-(4 : ℝ))) := by
    intro x
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
    by_cases hx : 1 ≤ ‖x‖
    · have hmem : x ∈ T := hx
      rw [hG, Set.indicator_of_mem hmem]
      apply ENNReal.ofReal_le_ofReal
      have hn0 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
      have hn1 : (1 : ℝ) ≤ ‖x‖ := hx
      rw [tl_rpow_neg_four ‖x‖ hn0, tl_rpow_neg_four (1 + ‖x‖) (by positivity)]
      have hp : (1 + ‖x‖) ^ 4 ≤ 16 * ‖x‖ ^ 4 := by
        calc (1 + ‖x‖) ^ 4 ≤ (2 * ‖x‖) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
          _ = 16 * ‖x‖ ^ 4 := by ring
      have hpos : 0 < (1 + ‖x‖) ^ 4 := by positivity
      have hinv : (16 * ‖x‖ ^ 4)⁻¹ ≤ ((1 + ‖x‖) ^ 4)⁻¹ := inv_anti₀ hpos hp
      have h16 : (‖x‖ ^ 4)⁻¹ = 16 * (16 * ‖x‖ ^ 4)⁻¹ := by
        rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (by norm_num : (16 : ℝ) ≠ 0), one_mul]
      rw [h16]
      exact mul_le_mul_of_nonneg_left hinv (by norm_num)
    · have hnmem : x ∉ T := hx
      rw [hG, Set.indicator_of_notMem hnmem]
      exact zero_le
  have hGJ : ∫⁻ z, G z ≤ ENNReal.ofReal 16 * J := by
    rw [hJdef]
    calc ∫⁻ z, G z ≤ ∫⁻ z, ENNReal.ofReal 16 *
            ENNReal.ofReal ((1 + ‖z‖) ^ (-(4 : ℝ))) := lintegral_mono hpt16
      _ = ENNReal.ofReal 16 * ∫⁻ w : UnforcedLeray.Space,
            ENNReal.ofReal ((1 + ‖w‖) ^ (-(4 : ℝ))) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- assemble
  have hrhs : ENNReal.ofReal (d ^ 3) * (ENNReal.ofReal (d ^ (-4 : ℝ)) *
      (ENNReal.ofReal 16 * ENNReal.ofReal Jr)) = ENNReal.ofReal (16 * Jr / d) := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ d ^ 3)]
    congr 1
    rw [tl_rpow_neg_four d hd.le]
    field_simp
  rw [hLHS]
  calc ∫⁻ x, F x = ENNReal.ofReal (d ^ 3) * (ENNReal.ofReal ((d ^ 3)⁻¹) * ∫⁻ w, F w) := hcancel
    _ = ENNReal.ofReal (d ^ 3) * (ENNReal.ofReal (d ^ (-4 : ℝ)) * ∫⁻ z, G z) := by rw [hkey]
    _ ≤ ENNReal.ofReal (d ^ 3) * (ENNReal.ofReal (d ^ (-4 : ℝ)) *
          (ENNReal.ofReal 16 * ENNReal.ofReal Jr)) := by
        gcongr
        rw [← hJr]
        exact hGJ
    _ = ENNReal.ofReal (16 * Jr / d) := hrhs

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
