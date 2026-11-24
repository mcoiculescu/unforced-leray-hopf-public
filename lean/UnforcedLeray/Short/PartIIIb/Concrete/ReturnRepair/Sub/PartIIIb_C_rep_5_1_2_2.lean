import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2Org
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineFields

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem binT_sq (f : Chart → Merid) (ν : Measure Chart) :
    eLpNorm f 2 ν ^ (2 : ℝ) = ∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂ν := by
  have := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := ν) (p := 2) (by norm_num)
  simpa using this

theorem binT_sq_tsum (x : ℕ → ℝ≥0∞) : ∑' j, x j ^ (2 : ℝ) ≤ (∑' j, x j) ^ (2 : ℝ) := by
  have h2 : (∑' j, x j) ^ (2 : ℝ) = (∑' j, x j) * (∑' j, x j) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast, pow_two]
  rw [h2]
  calc ∑' j, x j ^ (2 : ℝ) = ∑' j, x j * x j := by
        congr 1; ext j
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast, pow_two]
    _ ≤ ∑' j, x j * ∑' i, x i :=
        ENNReal.tsum_le_tsum fun j => by gcongr; exact ENNReal.le_tsum j
    _ = _ := by rw [ENNReal.tsum_mul_right]

theorem binT_cover (S h : ℝ) (hh : 0 < h) (p : Chart) (hp : 0 < p.1) :
    p ∈ (⋃ j : ℕ, binSet S h j) ∪ {q : Chart | S < q.1} := by
  by_cases hS : S < p.1
  · exact Or.inr hS
  · left
    rw [not_lt] at hS
    have hS0 : 0 < S := lt_of_lt_of_le hp hS
    have hex : ∃ j : ℕ, binUpper S h (j + 1) < p.1 := by
      obtain ⟨m, hm⟩ := exists_nat_gt (S / (p.1 * h))
      refine ⟨m, ?_⟩
      unfold binUpper
      have h1 : S / p.1 < h * ((m + 1 : ℕ) : ℝ) := by
        have : S / p.1 / h < m := by rw [div_div]; exact hm
        rw [div_lt_iff₀ hh] at this
        push_cast
        nlinarith
      have h2 : S / p.1 < Real.exp (h * ((m + 1 : ℕ) : ℝ)) :=
        h1.trans_le (by linarith [Real.add_one_le_exp (h * ((m + 1 : ℕ) : ℝ))])
      rw [Real.exp_neg, mul_inv_lt_iff₀ (Real.exp_pos _)]
      rw [div_lt_iff₀ hp] at h2
      linarith
    classical
    let j := Nat.find hex
    have hj : binUpper S h (j + 1) < p.1 := Nat.find_spec hex
    have hj2 : p.1 ≤ binUpper S h j := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · rw [h0]; simpa [binUpper] using hS
      · have := Nat.find_min hex (show j - 1 < j by omega)
        have e : j - 1 + 1 = j := by omega
        rw [e] at this
        exact not_lt.1 this
    exact mem_iUnion.2 ⟨j, hj, hj2⟩

theorem binTriangle : BinTriangle := by
  intro c γ ν S h hh φ hsupp B hB hbd
  set μ := bodyMeasure c γ ν with hμ
  set g : Chart → ℝ≥0∞ := fun p => ‖(φ : Chart → Merid) p‖ₑ ^ (2 : ℝ) with hg
  set x : ℕ → ℝ≥0∞ := fun j => eLpNorm (φ : Chart → Merid) 2 (μ.restrict (binSet S h j)) with hx
  have hB0 : ∀ j, 0 ≤ B j := fun j =>
    le_trans (ENNReal.toReal_nonneg) (hbd j)
  have hxB : ∀ j, x j ≤ ENNReal.ofReal (B j) := by
    intro j
    have hfin : x j ≠ ∞ := by
      refine ne_top_of_le_ne_top (Lp.eLpNorm_ne_top φ) ?_
      exact eLpNorm_mono_measure _ Measure.restrict_le_self
    rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal (hbd j)
  have hpos := ae_bodyMeasure_fst_pos c γ ν
  have hcov : ∀ᵐ p ∂μ, p ∈ (⋃ j : ℕ, binSet S h j) ∪ {q : Chart | S < q.1} := by
    filter_upwards [hpos] with p hp using binT_cover S h hh p hp
  have hW : ∫⁻ p in {q : Chart | S < q.1}, g p ∂μ = 0 := by
    have : ∀ᵐ p ∂(μ.restrict {q : Chart | S < q.1}), g p = 0 := by
      rw [ae_restrict_iff' (measurableSet_lt measurable_const measurable_fst)]
      filter_upwards [hsupp] with p hp hpW
      simp [g, hp hpW]
    exact (lintegral_congr_ae this).trans lintegral_zero
  have hmain : eLpNorm (φ : Chart → Merid) 2 μ ^ (2 : ℝ) ≤ ∑' j, x j ^ (2 : ℝ) := by
    rw [binT_sq]
    have e1 : ∫⁻ p, ‖(φ : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂μ = ∫⁻ p, g p ∂μ := rfl
    rw [e1]
    calc ∫⁻ p, g p ∂μ
        = ∫⁻ p in (⋃ j : ℕ, binSet S h j) ∪ {q : Chart | S < q.1}, g p ∂μ := by
          rw [Measure.restrict_eq_self_of_ae_mem hcov]
      _ ≤ ∫⁻ p in (⋃ j : ℕ, binSet S h j), g p ∂μ + ∫⁻ p in {q : Chart | S < q.1}, g p ∂μ :=
          lintegral_union_le _ _ _
      _ ≤ ∑' j, ∫⁻ p in binSet S h j, g p ∂μ + 0 := by
          rw [hW]; exact by gcongr; exact lintegral_iUnion_le (fun j : ℕ => binSet S h j) g
      _ = ∑' j, x j ^ (2 : ℝ) := by
          rw [add_zero]
          congr 1; ext j
          simp only [hx]
          rw [binT_sq]
  have h1 : eLpNorm (φ : Chart → Merid) 2 μ ≤ ∑' j, x j := by
    have := hmain.trans (binT_sq_tsum x)
    exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).1 this
  have h2 : ∑' j, x j ≤ ENNReal.ofReal (∑' j, B j) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hB0 hB]
    exact ENNReal.tsum_le_tsum hxB
  rw [Lp.norm_def]
  exact ENNReal.toReal_le_of_le_ofReal (tsum_nonneg hB0) (h1.trans h2)

end UnforcedLeray.Short.PartIIIb.Concrete
