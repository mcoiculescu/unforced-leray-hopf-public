import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_3

/-!
# Part III-a, `PartIII-a:T18/3/1/3/3/2` (`MollLimit`): convergence of squared `L²(cell)` norms

Source of record: `the November 2 reference manuscript` lines 3427-3440 and
3541-3552. If `a_k → a₀` in `L²(cell)` (in the sense `∫_cell ∑ᵢ ‖a_k - a₀‖² → 0`), then
`∫_cell |a_k|² → ∫_cell |a₀|²`.

Proof: pointwise `|‖u‖² - ‖v‖²| ≤ (1+t)‖u - v‖² + ‖v‖²/t` for every `t > 0` (reverse triangle
inequality and Young's inequality), integrate, and choose `t` in terms of `ε`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- `|v|² = ∑ᵢ |vᵢ|²` for the vector norm `vnorm2`. -/
lemma lmV_vnorm2_sq (v : Fin 2 → ℂ) : vnorm2 v ^ 2 = ∑ i : Fin 2, ‖v i‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))

/-- Pointwise: `|‖u‖² - ‖v‖²| ≤ ‖u - v‖² + 2‖u - v‖‖v‖`. -/
lemma lmV_abs_norm_sq_sub_le (u v : ℂ) :
    |‖u‖ ^ 2 - ‖v‖ ^ 2| ≤ ‖u - v‖ ^ 2 + 2 * ‖u - v‖ * ‖v‖ := by
  have hab : |‖u‖ - ‖v‖| ≤ ‖u - v‖ := abs_norm_sub_norm_le u v
  have hu : ‖u‖ ≤ ‖u - v‖ + ‖v‖ := by
    have := norm_add_le (u - v) v
    simpa using this
  have h1 : ‖u‖ + ‖v‖ ≤ ‖u - v‖ + 2 * ‖v‖ := by linarith
  have hsum : 0 ≤ ‖u‖ + ‖v‖ := by positivity
  have hd : ‖u‖ ^ 2 - ‖v‖ ^ 2 = (‖u‖ - ‖v‖) * (‖u‖ + ‖v‖) := by ring
  rw [hd, abs_mul, abs_of_nonneg hsum]
  have h2 : |‖u‖ - ‖v‖| * (‖u‖ + ‖v‖) ≤ ‖u - v‖ * (‖u - v‖ + 2 * ‖v‖) :=
    mul_le_mul hab h1 hsum (norm_nonneg _)
  nlinarith [h2]

/-- Young's inequality with a free parameter: `2 d v ≤ t d² + v²/t` for `t > 0`. -/
lemma lmV_young (d v t : ℝ) (ht : 0 < t) : 2 * d * v ≤ t * d ^ 2 + v ^ 2 / t := by
  have h : 0 ≤ (t * d - v) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
  have e : (t * d - v) ^ 2 / t = t * d ^ 2 - 2 * d * v + v ^ 2 / t := by
    field_simp
    ring
  linarith

/-- Pointwise bound on the difference of the squared vector norms. -/
lemma lmV_pt_bound (u v : Fin 2 → ℂ) (t : ℝ) (ht : 0 < t) :
    |∑ i : Fin 2, ‖u i‖ ^ 2 - ∑ i : Fin 2, ‖v i‖ ^ 2| ≤
      (1 + t) * ∑ i : Fin 2, ‖u i - v i‖ ^ 2 + (∑ i : Fin 2, ‖v i‖ ^ 2) / t := by
  rw [← Finset.sum_sub_distrib]
  calc |∑ i : Fin 2, (‖u i‖ ^ 2 - ‖v i‖ ^ 2)|
      ≤ ∑ i : Fin 2, |‖u i‖ ^ 2 - ‖v i‖ ^ 2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 2, ((1 + t) * ‖u i - v i‖ ^ 2 + ‖v i‖ ^ 2 / t) := by
        apply Finset.sum_le_sum
        intro i _
        have h1 := lmV_abs_norm_sq_sub_le (u i) (v i)
        have h2 := lmV_young (‖u i - v i‖) (‖v i‖) t ht
        nlinarith [h1, h2]
    _ = (1 + t) * ∑ i : Fin 2, ‖u i - v i‖ ^ 2 + (∑ i : Fin 2, ‖v i‖ ^ 2) / t := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_div]

/-- Integrability of `‖f x‖²` for an `L²` function with complex values. -/
lemma lmV_sq_integrable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : MemLp f 2 μ) : Integrable (fun x => ‖f x‖ ^ 2) μ := by
  have h := hf.integrable_norm_rpow (p := 2) two_ne_zero (by norm_num)
  simpa [Real.rpow_two] using h

/-- Integral of an absolute difference, against an integrable majorant. -/
lemma lmV_abs_integral_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α} (F g D : α → ℝ)
    (t : ℝ) (ht : 0 < t) (hF : Integrable F μ) (hg : Integrable g μ) (hD : Integrable D μ)
    (hpt : ∀ x, |F x - g x| ≤ (1 + t) * D x + g x / t) :
    |∫ x, F x ∂μ - ∫ x, g x ∂μ| ≤ (1 + t) * ∫ x, D x ∂μ + (∫ x, g x ∂μ) / t := by
  rw [← integral_sub hF hg]
  refine (abs_integral_le_integral_abs).trans ?_
  have hint : Integrable (fun x => (1 + t) * D x + g x / t) μ :=
    (hD.const_mul _).add (hg.div_const _)
  calc ∫ x, |F x - g x| ∂μ ≤ ∫ x, ((1 + t) * D x + g x / t) ∂μ :=
        integral_mono (hF.sub hg).abs hint hpt
    _ = (1 + t) * ∫ x, D x ∂μ + (∫ x, g x ∂μ) / t := by
        rw [integral_add (hD.const_mul _) (hg.div_const _), integral_const_mul, integral_div]

/-- The squared-norm integral is continuous along `L²(cell)`-convergent sequences. -/
lemma lmV_sq_integral_tendsto {c : ℝ} {a : ℕ → LMSpField} {a₀ : LMSpField}
    (ha : ∀ k, LMCellL2 c (a k)) (ha₀ : LMCellL2 c a₀)
    (h : Tendsto (fun k : ℕ => ∫ x in B0579.cell c, ∑ i : Fin 2, ‖a k x i - a₀ x i‖ ^ 2) atTop
      (𝓝 0)) :
    Tendsto (fun k : ℕ => ∫ x in B0579.cell c, ∑ i : Fin 2, ‖a k x i‖ ^ 2) atTop
      (𝓝 (∫ x in B0579.cell c, ∑ i : Fin 2, ‖a₀ x i‖ ^ 2)) := by
  have hG0 : 0 ≤ ∫ x in B0579.cell c, ∑ i : Fin 2, ‖a₀ x i‖ ^ 2 := by
    apply integral_nonneg
    intro x
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  rw [Metric.tendsto_nhds]
  intro ε hε
  set G : ℝ := ∫ x in B0579.cell c, ∑ i : Fin 2, ‖a₀ x i‖ ^ 2 with hG
  set t : ℝ := 2 * (G + 1) / ε with ht_def
  have ht : 0 < t := by
    rw [ht_def]
    apply div_pos _ hε
    linarith
  have hGt : G / t < ε / 2 := by
    rw [div_lt_iff₀ ht]
    have e : ε / 2 * t = G + 1 := by
      rw [ht_def]
      field_simp
    linarith
  have hD' : ∀ᶠ k : ℕ in atTop, (1 + t) * ∫ x in B0579.cell c,
      ∑ i : Fin 2, ‖a k x i - a₀ x i‖ ^ 2 < ε / 2 := by
    have hlim : Tendsto (fun k : ℕ => (1 + t) * ∫ x in B0579.cell c,
        ∑ i : Fin 2, ‖a k x i - a₀ x i‖ ^ 2) atTop (𝓝 ((1 + t) * 0)) :=
      h.const_mul _
    rw [mul_zero] at hlim
    exact hlim.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hD'] with k hk
  rw [Real.dist_eq]
  have hFi : Integrable (fun x => ∑ i : Fin 2, ‖a k x i‖ ^ 2) (volume.restrict (B0579.cell c)) :=
    integrable_finset_sum _ (fun i _ => lmV_sq_integrable ((ha k) i))
  have hgi : Integrable (fun x => ∑ i : Fin 2, ‖a₀ x i‖ ^ 2) (volume.restrict (B0579.cell c)) :=
    integrable_finset_sum _ (fun i _ => lmV_sq_integrable ((ha₀) i))
  have hDi : Integrable (fun x => ∑ i : Fin 2, ‖a k x i - a₀ x i‖ ^ 2)
      (volume.restrict (B0579.cell c)) :=
    integrable_finset_sum _ (fun i _ => lmV_sq_integrable (((ha k) i).sub ((ha₀) i)))
  have key := lmV_abs_integral_sub_le (fun x => ∑ i : Fin 2, ‖a k x i‖ ^ 2)
    (fun x => ∑ i : Fin 2, ‖a₀ x i‖ ^ 2) (fun x => ∑ i : Fin 2, ‖a k x i - a₀ x i‖ ^ 2) t ht
    hFi hgi hDi (fun x => lmV_pt_bound (a k x) (a₀ x) t ht)
  rw [← hG] at key
  refine lt_of_le_of_lt key ?_
  linarith [hk, hGt]

/-- **Convergence of squared `L²` norms** (SP 3427-3440, 3541-3552): if `a_k → a₀` in `L²(cell)`,
then `∫_cell |a_k|² → ∫_cell |a₀|²`. -/
theorem lm_tendsto_vsq {c : ℝ} {a : ℕ → LMSpField} {a₀ : LMSpField} (ha : ∀ k, LMCellL2 c (a k))
    (ha₀ : LMCellL2 c a₀)
    (h : Tendsto (fun k : ℕ => ∫ x in B0579.cell c, ∑ i : Fin 2, ‖a k x i - a₀ x i‖ ^ 2) atTop
      (𝓝 0)) :
    Tendsto (fun k : ℕ => ∫ x in B0579.cell c, vnorm2 (a k x) ^ 2) atTop
      (𝓝 (∫ x in B0579.cell c, vnorm2 (a₀ x) ^ 2)) := by
  simp only [lmV_vnorm2_sq]
  exact lmV_sq_integral_tendsto ha ha₀ h

end UnforcedLeray.Short.IIIa
