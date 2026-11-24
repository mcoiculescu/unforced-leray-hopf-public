import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.TerminalBound

/-!
# `PartIII-a:T21/2/2/3/6`, leaf `AdjChiWeights`: the weighted gradient bound (SP 3044-3047)

Source of record: `the November 2 reference manuscript` lines 3044-3047 (the
periodic weight `p_d` is equivalent to `⟨y⟩^{2m}` on the cell). Let `P(y) = 1 + y₂² + (d/π)² sin²(πy₁/d)`,
so `periodicWeight (-m) d y = P(y)^{-m}`.

On the cell `|y₁| ≤ d/2`, Jordan's inequality `|sin u| ≥ (2/π)|u|` for `|u| ≤ π/2` gives
`P(y) ≥ (4/π²) jb(y)`, hence for `m ≥ 0`,
`p_d⁻¹(y) ≤ (π²/4)^m jb(y)^{-m}` on the cell. The a.e. equality `∂_kχ = g'_k` transfers
`∫ p_d⁻¹|∂_kχ|²` to `∫ p_d⁻¹|g'_k|²`, which is controlled by the finite `h1Norm` of `(χ', g')`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.AdjE1

/-- On the cell, `P(y) ≥ (4/π²) jb(y)` (Jordan's inequality and `|y₁| ≤ d/2`). -/
theorem adjChi_P_ge {d : ℝ} (hd : 0 < d) (y : ℝ × ℝ) (hy : y ∈ B0579.cell d) :
    4 / Real.pi ^ 2 * B0579.jb y ≤
      1 + y.2 ^ 2 + (d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2 := by
  have hcell := hy
  simp only [B0579.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true] at hcell
  have hd0 : d ≠ 0 := hd.ne'
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hu_abs : |Real.pi * y.1 / d| ≤ Real.pi / 2 := by
    rw [abs_le]
    constructor
    · rw [le_div_iff₀ hd]
      nlinarith [Real.pi_pos, mul_nonneg Real.pi_pos.le (by linarith [hcell.1] : (0:ℝ) ≤ y.1 + d / 2)]
    · rw [div_le_iff₀ hd]
      nlinarith [Real.pi_pos, mul_nonneg Real.pi_pos.le (by linarith [hcell.2] : (0:ℝ) ≤ d / 2 - y.1)]
  have hjor := Real.mul_le_sin (abs_nonneg (Real.pi * y.1 / d)) hu_abs
  have hsinabs : Real.sin |Real.pi * y.1 / d| ^ 2 = Real.sin (Real.pi * y.1 / d) ^ 2 := by
    rcases abs_choice (Real.pi * y.1 / d) with h | h <;> simp [h, Real.sin_neg]
  have hsq : (2 / Real.pi * |Real.pi * y.1 / d|) ^ 2 ≤ Real.sin |Real.pi * y.1 / d| ^ 2 := by
    gcongr
  have hsq2 : (2 / Real.pi * |Real.pi * y.1 / d|) ^ 2 = 4 / Real.pi ^ 2 * (Real.pi * y.1 / d) ^ 2 := by
    rw [mul_pow, sq_abs]
    ring
  have hs2 : 4 / Real.pi ^ 2 * (Real.pi * y.1 / d) ^ 2 ≤ Real.sin (Real.pi * y.1 / d) ^ 2 := by
    rw [hsq2, hsinabs] at hsq
    exact hsq
  have hkey : (d / Real.pi) ^ 2 * (4 / Real.pi ^ 2 * (Real.pi * y.1 / d) ^ 2) = 4 / Real.pi ^ 2 * y.1 ^ 2 := by
    field_simp
  have hmul : (d / Real.pi) ^ 2 * (4 / Real.pi ^ 2 * (Real.pi * y.1 / d) ^ 2) ≤
      (d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2 :=
    mul_le_mul_of_nonneg_left hs2 (sq_nonneg _)
  rw [hkey] at hmul
  have h4 : 4 / Real.pi ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hcomb : 4 / Real.pi ^ 2 * B0579.jb y ≤ 1 + y.2 ^ 2 + 4 / Real.pi ^ 2 * y.1 ^ 2 := by
    unfold B0579.jb
    nlinarith [mul_nonneg (sub_nonneg.2 h4) (by positivity : (0:ℝ) ≤ 1 + y.2 ^ 2)]
  linarith

/-- The cell weight comparison `p_d⁻¹ ≤ (π²/4)^m jb^{-m}` on the cell, for `m ≥ 0`. -/
theorem adjChi_weight_le {m d : ℝ} (hm : 0 ≤ m) (hd : 0 < d) (y : ℝ × ℝ) (hy : y ∈ B0579.cell d) :
    periodicWeight (-m) d y ≤ (Real.pi ^ 2 / 4) ^ m * B0579.jb y ^ (-m) := by
  have hP := adjChi_P_ge hd y hy
  have hpos : 0 < 4 / Real.pi ^ 2 * B0579.jb y := by
    have := B0579.jb_pos y
    positivity
  unfold periodicWeight
  have h1 := Real.rpow_le_rpow_of_nonpos hpos hP (neg_nonpos.2 hm)
  have hK : (4 / Real.pi ^ 2) ^ (-m) = (Real.pi ^ 2 / 4) ^ m := by
    rw [show (4 / Real.pi ^ 2 : ℝ) = (Real.pi ^ 2 / 4)⁻¹ by rw [inv_div],
      Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv]
  refine h1.trans (le_of_eq ?_)
  rw [Real.mul_rpow (by positivity) (B0579.jb_pos y).le, hK]

/-- **Leaf `AdjChiWeights`** (SP 3044-3047): for `m ≥ 0`, if `∂_kχ = g'_k` a.e. on the cell and
`h1Norm (χ', g') ≤ C √E_0`, then `∫ p_d⁻¹ |∂_kχ|²` is integrable on the cell for each `k` and
`Σ_k ∫ p_d⁻¹|∂_kχ|² ≤ (π²/4)^m C² E_0`. -/
theorem adjChiWeights (m : ℝ) : UnforcedLeray.Short.IIIa.AdjE1.AdjChiWeights m := by
  unfold AdjChiWeights
  intro hm d C E0 χ χ' g' hd hC hE0 hae hh
  have hK0 : (0 : ℝ) ≤ (Real.pi ^ 2 / 4) ^ m := by positivity
  have hmeasP : ∀ k, Measurable (pdCx k χ) := fun k =>
    measurable_fderiv_apply_const ℝ χ (B0579.dir k)
  -- pointwise cell bound of the integrand against the weight `jb^{-m}`
  have hpt : ∀ k, ∀ᵐ y ∂(volume.restrict (B0579.cell d)),
      periodicWeight (-m) d y * ‖g' k y‖ ^ 2 ≤
        (Real.pi ^ 2 / 4) ^ m * (B0579.jb y ^ (-m) * ‖g' k y‖ ^ 2) := by
    intro k
    filter_upwards [ae_restrict_mem (B0579.measurableSet_cell d)] with y hy
    have := adjChi_weight_le hm hd y hy
    calc periodicWeight (-m) d y * ‖g' k y‖ ^ 2
        ≤ ((Real.pi ^ 2 / 4) ^ m * B0579.jb y ^ (-m)) * ‖g' k y‖ ^ 2 :=
          mul_le_mul_of_nonneg_right this (sq_nonneg _)
      _ = (Real.pi ^ 2 / 4) ^ m * (B0579.jb y ^ (-m) * ‖g' k y‖ ^ 2) := by ring
  -- transfer of the a.e. equality to the weighted measure, and measurability
  have hae' : ∀ j, g' j =ᵐ[B0579.cellMeasure d (-m)] pdCx j χ := fun j =>
    (Filter.Eventually.filter_mono (Measure.ae_le_iff_absolutelyContinuous.2 (B0579.cellMeasure_ac d (-m)))
      (hae j)).mono fun y hy => hy.symm
  -- finiteness of the `X_{-m,d}` norms
  have hpow : ∀ a : ℝ≥0∞, (a ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = a := by
    intro a
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hBsq : (ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt E0)) ^ (2 : ℕ) =
      ENNReal.ofReal (C ^ 2 * E0) := by
    rw [mul_pow, ← ENNReal.ofReal_pow hC, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
      Real.sq_sqrt hE0, ← ENNReal.ofReal_mul (by positivity)]
  have hh' : (xNorm d (-m) χ' ^ 2 + ∑ j, xNorm d (-m) (g' j) ^ 2) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt E0) := hh
  have hA_le : xNorm d (-m) χ' ^ 2 + ∑ j, xNorm d (-m) (g' j) ^ 2 ≤
      ENNReal.ofReal (C ^ 2 * E0) := by
    calc xNorm d (-m) χ' ^ 2 + ∑ j, xNorm d (-m) (g' j) ^ 2
        = ((xNorm d (-m) χ' ^ 2 + ∑ j, xNorm d (-m) (g' j) ^ 2) ^ (1 / 2 : ℝ)) ^ (2 : ℕ) :=
          (hpow _).symm
      _ ≤ (ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt E0)) ^ (2 : ℕ) := by gcongr
      _ = ENNReal.ofReal (C ^ 2 * E0) := hBsq
  have hxg : ∀ j, xNorm d (-m) (g' j) ≠ ⊤ := by
    intro j
    have hsum : xNorm d (-m) (g' j) ^ 2 ≤ ∑ i, xNorm d (-m) (g' i) ^ 2 :=
      Finset.single_le_sum (f := fun i => xNorm d (-m) (g' i) ^ 2)
        (fun _ _ => zero_le) (Finset.mem_univ j)
    have hle : xNorm d (-m) (g' j) ^ 2 ≤ ENNReal.ofReal (C ^ 2 * E0) :=
      le_trans (le_trans hsum le_add_self) hA_le
    intro htop
    rw [htop] at hle
    simp [ENNReal.ofReal_ne_top] at hle
  have hmemg : ∀ j, MemLp (g' j) 2 (B0579.cellMeasure d (-m)) := fun j =>
    ⟨((hmeasP j).aestronglyMeasurable).congr (hae' j).symm, lt_top_iff_ne_top.2 (hxg j)⟩
  -- integrability of the weighted square of `g'` on the cell
  have hcont : Continuous (fun y : ℝ × ℝ => periodicWeight (-m) d y) := by
    unfold periodicWeight
    refine Continuous.rpow_const (by fun_prop) (fun y => Or.inl ?_)
    have : 0 < 1 + y.2 ^ 2 + (d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2 := by positivity
    exact this.ne'
  have hint : ∀ k, Integrable (fun y => periodicWeight (-m) d y * ‖g' k y‖ ^ 2)
      (volume.restrict (B0579.cell d)) := by
    intro k
    have hgm : AEStronglyMeasurable (g' k) (volume.restrict (B0579.cell d)) :=
      ((hmeasP k).aestronglyMeasurable).congr (hae k)
    refine Integrable.mono' ((tb_integrable (hmemg k)).const_mul ((Real.pi ^ 2 / 4) ^ m)) ?_ ?_
    · exact hcont.aestronglyMeasurable.mul (hgm.norm.pow 2)
    · filter_upwards [hpt k] with y hy
      rw [Real.norm_of_nonneg (mul_nonneg (periodicWeight_nonneg _ _ _) (sq_nonneg _))]
      exact hy
  have hintχ : ∀ k, IntegrableOn (fun y => periodicWeight (-m) d y * ‖pdCx k χ y‖ ^ 2)
      (B0579.cell d) := fun k =>
    (hint k).congr (by
      filter_upwards [hae k] with y hy
      rw [hy])
  -- comparison of the integrals
  have hcongr : ∀ k, ∫ y in B0579.cell d, periodicWeight (-m) d y * ‖pdCx k χ y‖ ^ 2 =
      ∫ y in B0579.cell d, periodicWeight (-m) d y * ‖g' k y‖ ^ 2 := by
    intro k
    refine integral_congr_ae ?_
    filter_upwards [hae k] with y hy
    rw [hy]
  have hsum_k : ∀ k, ∫ y in B0579.cell d, periodicWeight (-m) d y * ‖g' k y‖ ^ 2 ≤
      (Real.pi ^ 2 / 4) ^ m * (xNorm d (-m) (g' k)).toReal ^ 2 := by
    intro k
    rw [tb_sq_xNorm (hmemg k), ← integral_const_mul]
    exact integral_mono_ae (hint k) ((tb_integrable (hmemg k)).const_mul _) (hpt k)
  have hsumreal : ∑ k : Fin 2, (xNorm d (-m) (g' k)).toReal ^ 2 ≤ C ^ 2 * E0 := by
    have h2 : ∑ k : Fin 2, (xNorm d (-m) (g' k)).toReal ^ 2 =
        (∑ k : Fin 2, xNorm d (-m) (g' k) ^ 2).toReal := by
      rw [ENNReal.toReal_sum (fun k _ => ENNReal.pow_ne_top (hxg k))]
      simp [ENNReal.toReal_pow]
    rw [h2]
    apply ENNReal.toReal_le_of_le_ofReal (mul_nonneg (sq_nonneg C) hE0)
    exact le_trans le_add_self hA_le
  refine ⟨hintχ, ?_⟩
  calc ∑ k : Fin 2, ∫ y in B0579.cell d, periodicWeight (-m) d y * ‖pdCx k χ y‖ ^ 2
      = ∑ k : Fin 2, ∫ y in B0579.cell d, periodicWeight (-m) d y * ‖g' k y‖ ^ 2 :=
        Finset.sum_congr rfl fun k _ => hcongr k
    _ ≤ ∑ k : Fin 2, (Real.pi ^ 2 / 4) ^ m * (xNorm d (-m) (g' k)).toReal ^ 2 :=
        Finset.sum_le_sum fun k _ => hsum_k k
    _ = (Real.pi ^ 2 / 4) ^ m * ∑ k : Fin 2, (xNorm d (-m) (g' k)).toReal ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ (Real.pi ^ 2 / 4) ^ m * (C ^ 2 * E0) := mul_le_mul_of_nonneg_left hsumreal hK0
    _ = (Real.pi ^ 2 / 4) ^ m * C ^ 2 * E0 := by ring

end UnforcedLeray.Short.IIIa.AdjE1
