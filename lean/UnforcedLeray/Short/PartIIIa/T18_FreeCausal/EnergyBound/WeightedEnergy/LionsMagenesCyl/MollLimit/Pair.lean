import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_3

/-!
# Part III-a, `PartIII-a:T18/3/1/3/3/4` (`MollLimit`): the real pairing is continuous in `L²(cell)`

Source of record: `the November 2 reference manuscript` lines 3427-3440 and
3541-3552. For `H` and `T_k → T₀` in `L²(cell)` (columnwise in `j`), the integrals of
`∑ᵢⱼ (Re H_ij Re T_ij + Im H_ij Im T_ij)` converge.

Proof: the difference is a pairing of `H` with `T_k - T₀`. Pointwise, for `l > 0`,
`2 l |⟨h, d⟩| ≤ l² |h|² + |d|²` (a sum of squares), so after integration
`2 l |I_k| ≤ l² ∫|H|² + ∫∑ⱼ∑ᵢ |d_ij|²`; choose `l` in terms of `ε`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The real pairing `∑ᵢⱼ (Re H Re S + Im H Im S)` of two tensor fields. -/
def lmP_pair (H S : ℝ × ℝ → Fin 2 → Fin 2 → ℂ) (x : ℝ × ℝ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, ((H x i j).re * (S x i j).re + (H x i j).im * (S x i j).im)

lemma lmP_sq_integrable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : MemLp f 2 μ) : Integrable (fun x => ‖f x‖ ^ 2) μ := by
  have h := hf.integrable_norm_rpow (p := 2) two_ne_zero (by norm_num)
  simpa [Real.rpow_two] using h

lemma lmP_norm_sq_eq (z : ℂ) : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
  rw [Complex.sq_norm, Complex.normSq_apply]

/-- Two-dimensional Young inequality for the real pairing of complex numbers. -/
lemma lmP_term_bound (h t : ℂ) (l : ℝ) (hl : 0 < l) :
    2 * l * |h.re * t.re + h.im * t.im| ≤ l ^ 2 * ‖h‖ ^ 2 + ‖t‖ ^ 2 := by
  rw [lmP_norm_sq_eq h, lmP_norm_sq_eq t]
  have h1 : 2 * l * (h.re * t.re + h.im * t.im) ≤
      l ^ 2 * (h.re * h.re + h.im * h.im) + (t.re * t.re + t.im * t.im) := by
    nlinarith [sq_nonneg (l * h.re - t.re), sq_nonneg (l * h.im - t.im)]
  have h2 : -(2 * l * (h.re * t.re + h.im * t.im)) ≤
      l ^ 2 * (h.re * h.re + h.im * h.im) + (t.re * t.re + t.im * t.im) := by
    nlinarith [sq_nonneg (l * h.re + t.re), sq_nonneg (l * h.im + t.im)]
  have habs : 2 * l * |h.re * t.re + h.im * t.im| = |2 * l * (h.re * t.re + h.im * t.im)| := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * l)]
  rw [habs]
  exact abs_le.mpr ⟨by linarith [h2], h1⟩

/-- Integrability of the pointwise pairing of two `L²` tensor fields (one component pair). -/
lemma lmP_mul_integrable {α : Type*} [MeasurableSpace α] {μ : Measure α} {h t : α → ℂ}
    (hh : MemLp h 2 μ) (ht : MemLp t 2 μ) :
    Integrable (fun x => (h x).re * (t x).re + (h x).im * (t x).im) μ := by
  refine Integrable.mono' (((lmP_sq_integrable hh).add (lmP_sq_integrable ht)).div_const 2) ?_ ?_
  · have h1 := Complex.continuous_re.comp_aestronglyMeasurable hh.aestronglyMeasurable
    have h2 := Complex.continuous_im.comp_aestronglyMeasurable hh.aestronglyMeasurable
    have h3 := Complex.continuous_re.comp_aestronglyMeasurable ht.aestronglyMeasurable
    have h4 := Complex.continuous_im.comp_aestronglyMeasurable ht.aestronglyMeasurable
    exact (h1.mul h3).add (h2.mul h4)
  · refine Eventually.of_forall (fun x => ?_)
    have := lmP_term_bound (h x) (t x) 1 one_pos
    rw [Real.norm_eq_abs]
    norm_num at this
    show |(h x).re * (t x).re + (h x).im * (t x).im| ≤ (‖h x‖ ^ 2 + ‖t x‖ ^ 2) / 2
    linarith

/-- Pointwise bound of the difference of two pairings. -/
lemma lmP_pt_bound (H T S : Fin 2 → Fin 2 → ℂ) (l : ℝ) (hl : 0 < l) :
    2 * l * |∑ i : Fin 2, ∑ j : Fin 2, ((H i j).re * (T i j).re + (H i j).im * (T i j).im) -
        ∑ i : Fin 2, ∑ j : Fin 2, ((H i j).re * (S i j).re + (H i j).im * (S i j).im)| ≤
      l ^ 2 * ∑ i : Fin 2, ∑ j : Fin 2, ‖H i j‖ ^ 2 +
        ∑ j : Fin 2, ∑ i : Fin 2, ‖T i j - S i j‖ ^ 2 := by
  have hdiff : ∑ i : Fin 2, ∑ j : Fin 2, ((H i j).re * (T i j).re + (H i j).im * (T i j).im) -
        ∑ i : Fin 2, ∑ j : Fin 2, ((H i j).re * (S i j).re + (H i j).im * (S i j).im) =
      ∑ i : Fin 2, ∑ j : Fin 2, ((H i j).re * (T i j - S i j).re + (H i j).im * (T i j - S i j).im) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  rw [hdiff]
  have h1 : |∑ i : Fin 2, ∑ j : Fin 2, ((H i j).re * (T i j - S i j).re +
      (H i j).im * (T i j - S i j).im)| ≤
      ∑ i : Fin 2, ∑ j : Fin 2, |(H i j).re * (T i j - S i j).re +
        (H i j).im * (T i j - S i j).im| :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
  have h2 : ∀ i j, 2 * l * |(H i j).re * (T i j - S i j).re + (H i j).im * (T i j - S i j).im| ≤
      l ^ 2 * ‖H i j‖ ^ 2 + ‖T i j - S i j‖ ^ 2 :=
    fun i j => lmP_term_bound _ _ l hl
  have hc : ∑ i : Fin 2, ∑ j : Fin 2, ‖T i j - S i j‖ ^ 2 =
      ∑ j : Fin 2, ∑ i : Fin 2, ‖T i j - S i j‖ ^ 2 := Finset.sum_comm
  calc 2 * l * |∑ i : Fin 2, ∑ j : Fin 2, ((H i j).re * (T i j - S i j).re +
          (H i j).im * (T i j - S i j).im)|
      ≤ 2 * l * ∑ i : Fin 2, ∑ j : Fin 2, |(H i j).re * (T i j - S i j).re +
          (H i j).im * (T i j - S i j).im| :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = ∑ i : Fin 2, ∑ j : Fin 2, 2 * l * |(H i j).re * (T i j - S i j).re +
          (H i j).im * (T i j - S i j).im| := by
        simp only [Finset.mul_sum]
    _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, (l ^ 2 * ‖H i j‖ ^ 2 + ‖T i j - S i j‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h2 i j
    _ = l ^ 2 * ∑ i : Fin 2, ∑ j : Fin 2, ‖H i j‖ ^ 2 +
          ∑ j : Fin 2, ∑ i : Fin 2, ‖T i j - S i j‖ ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
        rw [hc]

/-- Abstract integral estimate: `2 l |∫F - ∫G| ≤ l² ∫A + ∫D` when `2 l |F - G| ≤ l² A + D`. -/
lemma lmP_abs_integral_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α} (F G A D : α → ℝ)
    (l : ℝ) (hl : 0 < l) (hF : Integrable F μ) (hG : Integrable G μ) (hA : Integrable A μ)
    (hD : Integrable D μ) (hpt : ∀ x, 2 * l * |F x - G x| ≤ l ^ 2 * A x + D x) :
    2 * l * |∫ x, F x ∂μ - ∫ x, G x ∂μ| ≤ l ^ 2 * ∫ x, A x ∂μ + ∫ x, D x ∂μ := by
  rw [← integral_sub hF hG]
  have h1 : |∫ x, (F x - G x) ∂μ| ≤ ∫ x, |F x - G x| ∂μ := abs_integral_le_integral_abs
  have h2 : 2 * l * |∫ x, (F x - G x) ∂μ| ≤ 2 * l * ∫ x, |F x - G x| ∂μ :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  have h3 : ∫ x, 2 * l * |F x - G x| ∂μ ≤ ∫ x, (l ^ 2 * A x + D x) ∂μ :=
    integral_mono ((hF.sub hG).abs.const_mul _) ((hA.const_mul _).add hD) hpt
  rw [integral_const_mul] at h3
  rw [integral_add (hA.const_mul _) hD, integral_const_mul] at h3
  exact h2.trans h3

/-- **Continuity of the real pairing** (SP 3427-3440, 3541-3552): if `T_k → T₀` columnwise in
`L²(cell)` and `H` is columnwise in `L²(cell)`, the integrals of the pairings converge. -/
theorem lm_tendsto_tpair {c : ℝ} {T : ℕ → ℝ × ℝ → Fin 2 → Fin 2 → ℂ} {T₀ H : ℝ × ℝ → Fin 2 → Fin 2 → ℂ}
    (hT : ∀ k j, LMCellL2 c (fun x i => T k x i j)) (hT₀ : ∀ j, LMCellL2 c (fun x i => T₀ x i j))
    (hH : ∀ j, LMCellL2 c (fun x i => H x i j))
    (h : ∀ j, Tendsto (fun k : ℕ => ∫ x in B0579.cell c, ∑ i : Fin 2, ‖T k x i j - T₀ x i j‖ ^ 2) atTop
      (𝓝 0)) :
    Tendsto (fun k : ℕ => ∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
        ((H x i j).re * (T k x i j).re + (H x i j).im * (T k x i j).im)) atTop
      (𝓝 (∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
        ((H x i j).re * (T₀ x i j).re + (H x i j).im * (T₀ x i j).im))) := by
  have hPint : ∀ S : ℝ × ℝ → Fin 2 → Fin 2 → ℂ, (∀ j, LMCellL2 c (fun x i => S x i j)) →
      Integrable (lmP_pair H S) (volume.restrict (B0579.cell c)) := by
    intro S hS
    exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      lmP_mul_integrable (h := fun x => H x i j) (t := fun x => S x i j) (hH j i) (hS j i)))
  have hAint : Integrable (fun x => ∑ i : Fin 2, ∑ j : Fin 2, ‖H x i j‖ ^ 2)
      (volume.restrict (B0579.cell c)) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      lmP_sq_integrable (f := fun x => H x i j) (hH j i)))
  have hDj : ∀ k j, Integrable (fun x => ∑ i : Fin 2, ‖T k x i j - T₀ x i j‖ ^ 2)
      (volume.restrict (B0579.cell c)) := fun k j =>
    integrable_finsetSum _ (fun i _ =>
      lmP_sq_integrable (f := fun x => T k x i j - T₀ x i j) ((hT k j i).sub (hT₀ j i)))
  have hDsum : ∀ k, ∫ x in B0579.cell c, ∑ j : Fin 2, ∑ i : Fin 2, ‖T k x i j - T₀ x i j‖ ^ 2 =
      ∑ j : Fin 2, ∫ x in B0579.cell c, ∑ i : Fin 2, ‖T k x i j - T₀ x i j‖ ^ 2 := fun k =>
    integral_finset_sum _ (fun j _ => hDj k j)
  have hDint : ∀ k, Integrable (fun x => ∑ j : Fin 2, ∑ i : Fin 2, ‖T k x i j - T₀ x i j‖ ^ 2)
      (volume.restrict (B0579.cell c)) := fun k => integrable_finsetSum _ (fun j _ => hDj k j)
  have hDlim : Tendsto (fun k : ℕ => ∫ x in B0579.cell c, ∑ j : Fin 2, ∑ i : Fin 2,
      ‖T k x i j - T₀ x i j‖ ^ 2) atTop (𝓝 0) := by
    have hs := tendsto_finset_sum (Finset.univ : Finset (Fin 2)) (fun j (_ : j ∈ Finset.univ) => h j)
    simp only [Finset.sum_const_zero] at hs
    exact Tendsto.congr (fun k => (hDsum k).symm) hs
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2, ‖H x i j‖ ^ 2 :=
    ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hM]
    apply integral_nonneg
    intro x
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = ε / (2 * (M + 1)) := ⟨_, rfl⟩
  have hM1 : M + 1 ≠ 0 := ne_of_gt (by linarith)
  have hlpos : 0 < l := by
    rw [hl]
    exact div_pos hε (by linarith)
  have hlM : l * M ≤ ε / 2 := by
    have e : ε = 2 * (l * M) + 2 * l := by
      rw [hl]
      field_simp
    linarith
  filter_upwards [hDlim.eventually (gt_mem_nhds (mul_pos hlpos hε))] with k hk
  have key : 2 * l * |(∫ x in B0579.cell c, lmP_pair H (T k) x) -
      (∫ x in B0579.cell c, lmP_pair H T₀ x)| ≤
      l ^ 2 * M + (∫ x in B0579.cell c, ∑ j : Fin 2, ∑ i : Fin 2, ‖T k x i j - T₀ x i j‖ ^ 2) := by
    rw [hM]
    exact lmP_abs_integral_sub_le (lmP_pair H (T k)) (lmP_pair H T₀)
      (fun x => ∑ i : Fin 2, ∑ j : Fin 2, ‖H x i j‖ ^ 2)
      (fun x => ∑ j : Fin 2, ∑ i : Fin 2, ‖T k x i j - T₀ x i j‖ ^ 2) l hlpos
      (hPint (T k) (hT k)) (hPint T₀ hT₀) hAint (hDint k)
      (fun x => lmP_pt_bound (H x) (T k x) (T₀ x) l hlpos)
  have h3 : l ^ 2 * M ≤ l * ε / 2 := by
    calc l ^ 2 * M = l * (l * M) := by ring
      _ ≤ l * (ε / 2) := mul_le_mul_of_nonneg_left hlM hlpos.le
      _ = l * ε / 2 := by ring
  have hpos : 0 < l * ε := mul_pos hlpos hε
  have h4 : 2 * l * |(∫ x in B0579.cell c, lmP_pair H (T k) x) -
      (∫ x in B0579.cell c, lmP_pair H T₀ x)| < 2 * l * ε := by
    linarith [hpos]
  rw [Real.dist_eq]
  exact lt_of_mul_lt_mul_left h4 (by linarith)

end UnforcedLeray.Short.IIIa
