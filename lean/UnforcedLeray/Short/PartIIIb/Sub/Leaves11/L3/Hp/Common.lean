import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_11_3
import UnforcedLeray.Short.PartIIIb.Sub.Leaves.CellSumPointwise
import UnforcedLeray.Short.PartIIIb.Sub.Leaves.CellUnfold
import UnforcedLeray.Short.PartIIIb.Sub.Leaves.CellGauss
import UnforcedLeray.Short.PartIIIb.Sub.Leaves.CellLattice
import UnforcedLeray.Short.PartIIIb.Sub.Leaves.CellTerm
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Order.Filter.AtTopBot.Interval
import Mathlib.Order.Interval.Finset.Box

/-!
# `PartIII-b:C/inst/11/3/1`, `/2` helpers: generic lattice-sum cell bound (source 4973-4975, 5063-5079)

Generic form of the Gaussian-lattice argument of `Sub/Leaves/EAcSumPointwise.lean` and
`Sub/PartIII-b_C_inst_10_3.lean` for a normed-space valued family `t j` with
`‖t j‖ ≤ M (1+|x_j|²)² e^{-|x_j|²/(4a)}`, plus measurability of a `ℤ`-indexed `tsum`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- A `ℤ`-indexed `tsum` of measurable functions with values in a normed space is measurable. -/
theorem l3_measurable_ztsum {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (F : ℤ → X → E) (hF : ∀ k, Measurable (F k)) : Measurable (fun x => ∑' k : ℤ, F k x) := by
  classical
  have hE : Measurable (fun x => ∑' k : ℤ, (‖F k x‖₊ : ENNReal)) :=
    Measurable.ennreal_tsum (fun k => (hF k).nnnorm.coe_nnreal_ennreal)
  have hS : MeasurableSet {x | Summable (fun k : ℤ => F k x)} := by
    have : {x | Summable (fun k : ℤ => F k x)} =
        {x | (∑' k : ℤ, (‖F k x‖₊ : ENNReal)) ≠ ⊤} := by
      ext x
      simp only [mem_setOf_eq]
      rw [ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
      exact summable_norm_iff.symm
    rw [this]
    exact hE (measurableSet_singleton ⊤).compl
  let g : ℕ → X → E := fun n x =>
    {x | Summable (fun k : ℤ => F k x)}.indicator
      (fun x => ∑ k ∈ Finset.Icc (-(n : ℤ)) n, F k x) x
  refine measurable_of_tendsto_metrizable (f := g) (fun n => ?_) ?_
  · exact (Finset.measurable_sum _ (fun k _ => hF k)).indicator hS
  · rw [tendsto_pi_nhds]
    intro x
    by_cases hx : Summable (fun k : ℤ => F k x)
    · have h1 : Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc (-(n : ℤ)) n, F k x) atTop
          (𝓝 (∑' k : ℤ, F k x)) :=
        hx.hasSum.comp (Finset.tendsto_Icc_neg_atTop_atTop.comp tendsto_natCast_atTop_atTop)
      refine h1.congr (fun n => ?_)
      simp [g, hx]
    · have h0 : ∑' k : ℤ, F k x = 0 := tsum_eq_zero_of_not_summable hx
      rw [h0]
      refine tendsto_const_nhds.congr (fun n => ?_)
      simp [g, hx]

/-- Pointwise square bound of a Gaussian lattice sum (Cauchy-Schwarz over `j` with weights
`e^{-(x₁-jc)²/(8a)}`). -/
theorem l3_lattice_sq {E : Type*} [NormedAddCommGroup E] (C1 : ℝ)
    (hC1 : ∀ c t a : ℝ, 1 ≤ c → 1 ≤ a → a ≤ 21 / 10 →
      (∑' j : ℤ, Real.exp (-((t - j * c) ^ 2) / (8 * a))) ≤ C1)
    (ν s : ℝ) (x : ℝ × ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1) (hs : 0 < s) (hsT : s ≤ (11 / 10) / ν)
    (t : ℤ → E) (M : ℝ) (hM : 0 ≤ M)
    (hT : ∀ j : ℤ, ‖t j‖ ≤ M * (1 + sq2 (xj ν j x)) ^ 2 *
        Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))) :
    ‖∑' j : ℤ, t j‖ ^ 2 ≤ max C1 0 * M ^ 2 * ∑' j : ℤ, fAcG (ageA ν s) (xj ν j x) := by
  have hνs : ν * s ≤ 11 / 10 := by
    rw [le_div_iff₀ hν] at hsT
    linarith [mul_comm ν s]
  have ha0 : 0 < ageA ν s := by unfold ageA; linarith [mul_pos hν hs]
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; linarith [mul_pos hν hs]
  have ha2 : ageA ν s ≤ 21 / 10 := by unfold ageA; linarith
  have hc0 : 0 < cOf ν := by unfold cOf; exact inv_pos.mpr (pow_pos hν 2)
  have hc1 : 1 ≤ cOf ν := by
    unfold cOf
    rw [one_le_inv₀ (pow_pos hν 2)]
    nlinarith
  have hq : ∀ j : ℤ, (x.1 - (j : ℝ) * cOf ν) ^ 2 ≤ sq2 (xj ν j x) := fun j => by
    show (x.1 - (j : ℝ) * cOf ν) ^ 2 ≤ (x.1 - (j : ℝ) * cOf ν) ^ 2 + x.2 ^ 2
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hq0 : ∀ j : ℤ, 0 ≤ sq2 (xj ν j x) := fun j => by unfold sq2; positivity
  have hGnn : ∀ j : ℤ, 0 ≤ fAcG (ageA ν s) (xj ν j x) := fun j => by
    unfold fAcG; have := hq0 j; positivity
  have hwS : Summable (fun j : ℤ => fAcWt ν s x j) := by
    have hα : 0 < 1 / (8 * ageA ν s) := div_pos one_pos (by linarith)
    refine (gp_gauss_summable x.1 (1 / (8 * ageA ν s)) (cOf ν) hα hc0).congr (fun j => ?_)
    unfold fAcWt
    congr 1
    ring
  have hGS : Summable (fun j : ℤ => fAcG (ageA ν s) (xj ν j x)) := by
    have hα : 0 < 1 / (16 * ageA ν s) := div_pos one_pos (by linarith)
    refine Summable.of_nonneg_of_le hGnn (fun j => ?_)
      ((gp_gauss_summable x.1 (1 / (16 * ageA ν s)) (cOf ν) hα hc0).mul_left
        ((64 * ageA ν s / 5) ^ 4))
    unfold fAcG
    exact fAc_G_le (ageA ν s) (sq2 (xj ν j x)) (x.1 - (j : ℝ) * cOf ν) ha1 (hq0 j) (hq j)
  have hkey : ∀ j : ℤ, ‖t j‖ ^ 2 / fAcWt ν s x j
      ≤ M ^ 2 * fAcG (ageA ν s) (xj ν j x) := by
    intro j
    have h := fAc_term_sq_div M (ageA ν s) (sq2 (xj ν j x))
      (x.1 - (j : ℝ) * cOf ν) ‖t j‖ (fAcWt ν s x j) ha0 (hq j)
      (norm_nonneg _) (hT j) rfl
    unfold fAcG
    exact h
  have hmle : ∀ j : ℤ, ‖t j‖ ≤ (M ^ 2 * fAcG (ageA ν s) (xj ν j x) + fAcWt ν s x j) / 2 := by
    intro j
    have hw0 : 0 < fAcWt ν s x j := by unfold fAcWt; exact Real.exp_pos _
    have hwne : fAcWt ν s x j ≠ 0 := hw0.ne'
    have h1 := hkey j
    have h2 : ‖t j‖ ^ 2 / fAcWt ν s x j + fAcWt ν s x j - 2 * ‖t j‖
        = (‖t j‖ - fAcWt ν s x j) ^ 2 / fAcWt ν s x j := by
      field_simp
      ring
    have h3 : 0 ≤ (‖t j‖ - fAcWt ν s x j) ^ 2 / fAcWt ν s x j :=
      div_nonneg (sq_nonneg _) hw0.le
    linarith
  have hmS : Summable (fun j : ℤ => ‖t j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hmle
      (((hGS.mul_left (M ^ 2)).add hwS).div_const 2)
  have hfAB_bound : ‖∑' j : ℤ, t j‖ ≤ ∑' j, ‖t j‖ := by
    by_cases hf : Summable (fun j : ℤ => t j)
    · exact norm_tsum_le_tsum_norm hmS
    · rw [tsum_eq_zero_of_not_summable hf, norm_zero]
      exact tsum_nonneg (fun j => norm_nonneg _)
  have hWle : ∑' j : ℤ, fAcWt ν s x j ≤ C1 := hC1 (cOf ν) x.1 (ageA ν s) hc1 ha1 ha2
  have hFin : ∀ F : Finset ℤ, (∑ j ∈ F, ‖t j‖) ^ 2
      ≤ max C1 0 * (M ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x)) := by
    intro F
    have hsq : (∑ j ∈ F, ‖t j‖) ^ 2
        ≤ (∑ j ∈ F, ‖t j‖ ^ 2 / fAcWt ν s x j) * ∑ j ∈ F, fAcWt ν s x j := by
      rcases F.eq_empty_or_nonempty with rfl | hne
      · simp
      · have hgpos : 0 < ∑ j ∈ F, fAcWt ν s x j :=
          Finset.sum_pos (fun j _ => by unfold fAcWt; exact Real.exp_pos _) hne
        have h := Finset.sq_sum_div_le_sum_sq_div F (fun j => ‖t j‖)
          (g := fun j => fAcWt ν s x j) (fun j _ => by unfold fAcWt; exact Real.exp_pos _)
        exact (div_le_iff₀ hgpos).mp h
    have hQ : ∑ j ∈ F, ‖t j‖ ^ 2 / fAcWt ν s x j
        ≤ M ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x) := by
      calc ∑ j ∈ F, ‖t j‖ ^ 2 / fAcWt ν s x j
          ≤ ∑ j ∈ F, M ^ 2 * fAcG (ageA ν s) (xj ν j x) :=
            Finset.sum_le_sum (fun j _ => hkey j)
        _ = M ^ 2 * ∑ j ∈ F, fAcG (ageA ν s) (xj ν j x) := by rw [Finset.mul_sum]
        _ ≤ M ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x) :=
            mul_le_mul_of_nonneg_left (sum_le_hasSum F (fun j _ => hGnn j) hGS.hasSum)
              (sq_nonneg _)
    have hSg : ∑ j ∈ F, fAcWt ν s x j ≤ max C1 0 := by
      have h1 : ∑ j ∈ F, fAcWt ν s x j ≤ ∑' j, fAcWt ν s x j :=
        sum_le_hasSum F (fun j _ => by unfold fAcWt; positivity) hwS.hasSum
      exact le_trans (h1.trans hWle) (le_max_left _ _)
    have hSgnn : 0 ≤ ∑ j ∈ F, fAcWt ν s x j :=
      Finset.sum_nonneg (fun j _ => by unfold fAcWt; positivity)
    have hTnn : 0 ≤ M ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x) :=
      mul_nonneg (sq_nonneg _) (tsum_nonneg hGnn)
    calc (∑ j ∈ F, ‖t j‖) ^ 2
        ≤ (∑ j ∈ F, ‖t j‖ ^ 2 / fAcWt ν s x j) * ∑ j ∈ F, fAcWt ν s x j := hsq
      _ ≤ (M ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x)) * max C1 0 :=
          mul_le_mul hQ hSg hSgnn hTnn
      _ = max C1 0 * (M ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x)) := mul_comm _ _
  have hX : 0 ≤ max C1 0 * (M ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x)) :=
    mul_nonneg (le_max_right _ _) (mul_nonneg (sq_nonneg _) (tsum_nonneg hGnn))
  have hS : ∑' j, ‖t j‖
      ≤ Real.sqrt (max C1 0 * (M ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x))) :=
    Real.tsum_le_of_sum_le (fun j => norm_nonneg _)
      (fun F => le_trans (le_abs_self _) (Real.abs_le_sqrt (hFin F)))
  have h1 : ‖∑' j : ℤ, t j‖
      ≤ Real.sqrt (max C1 0 * (M ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x))) :=
    hfAB_bound.trans hS
  calc ‖∑' j : ℤ, t j‖ ^ 2
      ≤ (Real.sqrt (max C1 0 * (M ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x)))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = max C1 0 * (M ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x)) := Real.sq_sqrt hX
    _ = max C1 0 * M ^ 2 * ∑' j : ℤ, fAcG (ageA ν s) (xj ν j x) := by ring

/-- Cell integral of a function whose square is bounded by `Q ∑_j G_a(x_j)`. -/
theorem l3_cell_bound : ∃ K2 : ℝ, 0 ≤ K2 ∧
    ∀ (ν s : ℝ), 0 < ν → ν ≤ 1 → 0 < s → s ≤ (11 / 10) / ν →
    ∀ (G : ℝ × ℝ → ℝ) (Q : ℝ), 0 ≤ Q →
      (∀ x, G x ^ 2 ≤ Q * ∑' j : ℤ, fAcG (ageA ν s) (xj ν j x)) →
      ∫⁻ x, ENNReal.ofReal (G x ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
        ≤ ENNReal.ofReal (Q * K2) := by
  obtain ⟨K2, hK2, hG⟩ := fAcGaussInt
  refine ⟨K2, hK2, ?_⟩
  intro ν s hν hν1 hs hsT G Q hQ hP
  have hc1 : 1 ≤ cOf ν := by
    unfold cOf
    rw [one_le_inv₀ (by positivity)]
    nlinarith
  have hc0 : 0 < cOf ν := by linarith
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have ha2 : ageA ν s ≤ 21 / 10 := by
    unfold ageA
    have : ν * s ≤ 11 / 10 := by
      rw [le_div_iff₀ hν] at hsT; linarith
    linarith
  have hnn : ∀ y, 0 ≤ fAcG (ageA ν s) y := by
    intro y
    unfold fAcG sq2
    positivity
  have hmeas : Measurable (fAcG (ageA ν s)) := by
    unfold fAcG sq2
    fun_prop
  calc ∫⁻ x, ENNReal.ofReal (G x ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
      ≤ ∫⁻ x, ENNReal.ofReal Q *
          ENNReal.ofReal (∑' j : ℤ, fAcG (ageA ν s) (xj ν j x))
          ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_mul hQ]
        exact ENNReal.ofReal_le_ofReal (hP x)
    _ = ENNReal.ofReal Q *
          ∫⁻ x, ENNReal.ofReal (∑' j : ℤ, fAcG (ageA ν s) (xj ν j x))
          ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal Q * (ENNReal.ofReal (cOf ν)⁻¹ * ENNReal.ofReal K2) := by
        gcongr
        calc _ ≤ ENNReal.ofReal (cOf ν)⁻¹ *
              ∫⁻ y, ENNReal.ofReal (fAcG (ageA ν s) y) ∂volume :=
            fAcCellUnfold (cOf ν) (fAcG (ageA ν s)) hc0 hmeas hnn
          _ ≤ _ := by gcongr; exact hG _ ha1 ha2
    _ ≤ ENNReal.ofReal Q * (ENNReal.ofReal 1 * ENNReal.ofReal K2) := by
        gcongr
        exact inv_le_one_of_one_le₀ hc1
    _ = ENNReal.ofReal (Q * K2) := by
        rw [ENNReal.ofReal_one, one_mul, ← ENNReal.ofReal_mul hQ]

end UnforcedLeray.Short.PartIIIb.Concrete

end
