import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04.Defs

/-!


Source of record: `the November 2 reference manuscript`,
lines 1737–1751 and 1800–1846.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226
open UnforcedLeray.Short.PartIIIb.NearInst.Masked

namespace ObsBoxS1Aux

/-- For `0 < σ ≤ s`, `s ^ (-(3 / 2 : ℝ)) ≤ (1 + σ⁻¹ + H1 + L1) ^ 2` when `σ ≤ H1` and `0 ≤ L1`. -/
lemma rpow_neg_three_halves_le {σ H1 L1 s : ℝ} (hσ : 0 < σ) (hσH1 : σ ≤ H1) (hL1 : 0 ≤ L1)
    (hs : σ ≤ s) :
    s ^ (-(3 / 2 : ℝ)) ≤ (1 + σ⁻¹ + H1 + L1) ^ 2 := by
  have hH1 : 0 ≤ H1 := hσ.le.trans hσH1
  have hσ_inv : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ.le
  have hs_le : s ^ (-(3 / 2 : ℝ)) ≤ σ ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hσ hs (by norm_num)
  have hσ_le : σ ^ (-(3 / 2 : ℝ)) ≤ (1 + σ⁻¹) ^ 2 := by
    rcases le_total σ 1 with hσ1 | h1σ
    · have hr := Real.rpow_le_rpow_of_exponent_ge hσ hσ1 (show (-2 : ℝ) ≤ -(3 / 2 : ℝ) by norm_num)
      have h2 : σ ^ (-2 : ℝ) = (σ⁻¹) ^ 2 := by
        rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hσ.le, Real.rpow_natCast,
          inv_pow]
      rw [h2] at hr
      nlinarith
    · have hr := Real.rpow_le_one_of_one_le_of_nonpos h1σ (show -(3 / 2 : ℝ) ≤ 0 by norm_num)
      nlinarith
  have hA : 1 + σ⁻¹ ≤ 1 + σ⁻¹ + H1 + L1 := by linarith
  have hA2 : (1 + σ⁻¹) ^ 2 ≤ (1 + σ⁻¹ + H1 + L1) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hA 2
  exact hs_le.trans (hσ_le.trans hA2)

/-- Norm of the unit vector `(1, 0, 0)` in `Profile = ℝ × ℝ × ℝ`. -/
lemma norm_eS_eq_one : ‖((1 : ℝ), (0 : ℝ), (0 : ℝ))‖ = 1 := by
  simp [Prod.norm_def]

/-- Vanishing of `z` and `opS z` outside the closed support band `dtdBand σ H1 L1`. -/
lemma opS_iter_eq_zero_of_not_mem_band {σ H1 L1 : ℝ} {z : Profile → MeridC}
    (hsupp : ∀ p, z p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) (a : ℕ) (ha : a < 2)
    {p : Profile} (hp : p ∉ dtdBand σ H1 L1) :
    (opS^[a] z) p = 0 := by
  have hev : ∀ᶠ y in nhds p, z y = 0 := by
    filter_upwards [(dtdBand_closed σ H1 L1).isOpen_compl.mem_nhds hp] with y hy
    by_contra hne
    exact hy (hsupp y hne)
  interval_cases a
  · exact hev.self_of_nhds
  · simp only [Function.iterate_one, opS, pdS]
    have hfd : fderiv ℝ z p = 0 := by
      have h' : z =ᶠ[nhds p] fun _ => (0 : MeridC) := hev
      rw [h'.fderiv_eq]
      simp
    simp [hfd]

/-- Pointwise bound on `(|p.2.2| ^ j) ^ 2 * ‖(opS^[a] z) p‖ ^ 2` on `dtdBand σ H1 L1`. -/
lemma band_pointwise_bound {σ H1 L1 : ℝ} (hσ : 0 < σ) (hσH1 : σ ≤ H1) (hL1 : 0 ≤ L1)
    (z : Profile → MeridC) (a j : ℕ) (ha : a < 2) (hj : j < 2) {p : Profile}
    (hp : p ∈ dtdBand σ H1 L1) :
    p.1 ^ (-(3 / 2 : ℝ)) * ((|p.2.2| ^ j) ^ 2 * ‖(opS^[a] z) p‖ ^ 2) ≤
      (1 + σ⁻¹ + H1 + L1) ^ 6 * ‖iteratedFDeriv ℝ a z p‖ ^ 2 := by
  obtain ⟨hp1, hp2, hp3⟩ := hp
  set A : ℝ := 1 + σ⁻¹ + H1 + L1
  have hH1 : 0 ≤ H1 := hσ.le.trans hσH1
  have hσ_inv : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ.le
  have hA1 : 1 ≤ A := by change 1 ≤ 1 + σ⁻¹ + H1 + L1; linarith
  have hAH1 : H1 ≤ A := by change H1 ≤ 1 + σ⁻¹ + H1 + L1; linarith
  have hAL1 : L1 ≤ A := by change L1 ≤ 1 + σ⁻¹ + H1 + L1; linarith
  have hA0 : 0 ≤ A := zero_le_one.trans hA1
  have hw : p.1 ^ (-(3 / 2 : ℝ)) ≤ A ^ 2 := rpow_neg_three_halves_le hσ hσH1 hL1 hp1
  have heta : |p.2.2| ^ j ≤ A := by
    interval_cases j
    · simp [hA1]
    · simpa using hp3.trans hAL1
  have heta_sq : (|p.2.2| ^ j) ^ 2 ≤ A ^ 2 :=
    pow_le_pow_left₀ (by positivity) heta 2
  have hopS : ‖(opS^[a] z) p‖ ≤ A * ‖iteratedFDeriv ℝ a z p‖ := by
    interval_cases a
    · simp only [Function.iterate_zero, id_eq, norm_iteratedFDeriv_zero]
      exact le_mul_of_one_le_left (norm_nonneg _) hA1
    · simp only [Function.iterate_one, opS, pdS, norm_iteratedFDeriv_one, norm_smul,
        Real.norm_eq_abs, abs_of_pos (hσ.trans_le hp1)]
      have hfd : ‖fderiv ℝ z p (1, 0, 0)‖ ≤ ‖fderiv ℝ z p‖ := by
        calc ‖fderiv ℝ z p (1, 0, 0)‖
            ≤ ‖fderiv ℝ z p‖ * ‖((1 : ℝ), (0 : ℝ), (0 : ℝ))‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ = ‖fderiv ℝ z p‖ := by rw [norm_eS_eq_one, mul_one]
      have hpA : p.1 ≤ A := hp2.trans hAH1
      exact mul_le_mul hpA hfd (norm_nonneg _) hA0
  have hopS_sq : ‖(opS^[a] z) p‖ ^ 2 ≤ A ^ 2 * ‖iteratedFDeriv ℝ a z p‖ ^ 2 := by
    calc ‖(opS^[a] z) p‖ ^ 2
        ≤ (A * ‖iteratedFDeriv ℝ a z p‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hopS 2
      _ = A ^ 2 * ‖iteratedFDeriv ℝ a z p‖ ^ 2 := mul_pow _ _ 2
  have hprod1 : (|p.2.2| ^ j) ^ 2 * ‖(opS^[a] z) p‖ ^ 2 ≤
      A ^ 2 * (A ^ 2 * ‖iteratedFDeriv ℝ a z p‖ ^ 2) :=
    mul_le_mul heta_sq hopS_sq (sq_nonneg _) (sq_nonneg A)
  calc p.1 ^ (-(3 / 2 : ℝ)) * ((|p.2.2| ^ j) ^ 2 * ‖(opS^[a] z) p‖ ^ 2)
      ≤ A ^ 2 * (A ^ 2 * (A ^ 2 * ‖iteratedFDeriv ℝ a z p‖ ^ 2)) :=
        mul_le_mul hw hprod1 (by positivity) (sq_nonneg A)
    _ = A ^ 6 * ‖iteratedFDeriv ℝ a z p‖ ^ 2 := by ring

/-- Global pointwise bound on `cell c`. -/
lemma cell_pointwise_bound {σ H1 L1 : ℝ} (hσ : 0 < σ) (hσH1 : σ ≤ H1) (hL1 : 0 ≤ L1)
    (z : Profile → MeridC) (hsupp : ∀ p, z p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    (a j : ℕ) (ha : a < 2) (hj : j < 2) (p : Profile) :
    p.1 ^ (-(3 / 2 : ℝ)) * ((|p.2.2| ^ j) ^ 2 * ‖(opS^[a] z) p‖ ^ 2) ≤
      (1 + σ⁻¹ + H1 + L1) ^ 6 * ‖iteratedFDeriv ℝ a z p‖ ^ 2 := by
  by_cases hp : p ∈ dtdBand σ H1 L1
  · exact band_pointwise_bound hσ hσH1 hL1 z a j ha hj hp
  · rw [opS_iter_eq_zero_of_not_mem_band hsupp a ha hp]
    have hH1 : 0 ≤ H1 := hσ.le.trans hσH1
    have hσ_inv : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ.le
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    positivity

/-- Continuity of `opS^[a] z` for `a < 2` when `z` is smooth. -/
lemma continuous_opS_iter {z : Profile → MeridC} (hz : ContDiff ℝ ∞ z) (a : ℕ) (ha : a < 2) :
    Continuous (opS^[a] z) := by
  interval_cases a
  · exact hz.continuous
  · simp only [Function.iterate_one]
    unfold opS pdS
    exact continuous_fst.smul ((hz.continuous_fderiv (by simp)).clm_apply continuous_const)

/-- Integrability of the weighted `opS^[a] z` integrand on `cell c`. -/
lemma integrableOn_weighted_opS (c σ H1 L1 : ℝ) (hσ : 0 < σ)
    {z : Profile → MeridC} (hz : IsMeridTest c z)
    (hsupp : ∀ p, z p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    (a j : ℕ) (ha : a < 2) :
    IntegrableOn
      (fun p : Profile => p.1 ^ (-(3 / 2 : ℝ)) * ((|p.2.2| ^ j) ^ 2 * ‖(opS^[a] z) p‖ ^ 2))
      (cell c) := by
  refine IntegrableOn.of_forall_sdiff_eq_zero (s := dtdBox σ H1 c L1) ?_
    (measurableSet_cell c) fun p hp => ?_
  · refine ContinuousOn.integrableOn_compact (dtdBox_compact σ H1 c L1) ?_
    refine ContinuousOn.mul ?_ ?_
    · refine ContinuousOn.rpow_const continuous_fst.continuousOn fun p hp => Or.inl ?_
      have hp1 : σ ≤ p.1 := hp.1.1
      linarith
    · refine Continuous.continuousOn ?_
      have h1 : Continuous fun p : Profile => (|p.2.2| ^ j) ^ 2 := by fun_prop
      have h2 : Continuous fun p : Profile => ‖(opS^[a] z) p‖ ^ 2 :=
        ((continuous_opS_iter hz.smooth a ha).norm).pow 2
      exact h1.mul h2
  · obtain ⟨hpcell, hpnot⟩ := hp
    have hnotband : p ∉ dtdBand σ H1 L1 := by
      intro hB
      apply hpnot
      exact ⟨⟨hB.1, hB.2.1⟩, ⟨hpcell.2.1.1.le, hpcell.2.1.2⟩, abs_le.mp hB.2.2⟩
    rw [opS_iter_eq_zero_of_not_mem_band hsupp a ha hnotband]
    simp

/-- Integrability of `‖iteratedFDeriv ℝ a z p‖ ^ 2` on `cell c`. -/
lemma integrableOn_iteratedFDeriv_sq (c σ H1 L1 : ℝ)
    {z : Profile → MeridC} (hz : IsMeridTest c z)
    (hsupp : ∀ p, z p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) (a : ℕ) :
    IntegrableOn (fun p : Profile => ‖iteratedFDeriv ℝ a z p‖ ^ 2) (cell c) := by
  refine IntegrableOn.of_forall_sdiff_eq_zero (s := dtdBox σ H1 c L1) ?_
    (measurableSet_cell c) fun p hp => ?_
  · refine ContinuousOn.integrableOn_compact (dtdBox_compact σ H1 c L1) ?_
    exact (((hz.smooth.continuous_iteratedFDeriv (by simp)).norm).pow 2).continuousOn
  · obtain ⟨hpcell, hpnot⟩ := hp
    have hnotband : p ∉ dtdBand σ H1 L1 := by
      intro hB
      apply hpnot
      exact ⟨⟨hB.1, hB.2.1⟩, ⟨hpcell.2.1.1.le, hpcell.2.1.2⟩, abs_le.mp hB.2.2⟩
    have hev : z =ᶠ[nhds p] fun _ => (0 : MeridC) := by
      filter_upwards [(dtdBand_closed σ H1 L1).isOpen_compl.mem_nhds hnotband] with y hy
      by_contra hne
      exact hy (hsupp y hne)
    have hzero : iteratedFDeriv ℝ a z p = 0 := by
      rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev a).self_of_nhds]
      simp
    simp [hzero]

/-- Bound for a single `(a, j)` term by `(1 + σ⁻¹ + H1 + L1) ^ 3 * h6Norm c z`. -/
lemma single_term_le (c σ H1 L1 : ℝ) (hσ : 0 < σ) (hσH1 : σ ≤ H1) (hL1 : 0 ≤ L1)
    {z : Profile → MeridC} (hz : IsMeridTest c z)
    (hsupp : ∀ p, z p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    {a j : ℕ} (ha : a ∈ Finset.range 2) (hj : j ∈ Finset.range 2) :
    (∫ p, (|p.2.2| ^ j) ^ 2 * ‖(opS^[a] z) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) ≤
      (1 + σ⁻¹ + H1 + L1) ^ 3 * h6Norm c z := by
  have ha' : a < 2 := Finset.mem_range.mp ha
  have hj' : j < 2 := Finset.mem_range.mp hj
  set A : ℝ := 1 + σ⁻¹ + H1 + L1
  have hH1 : 0 ≤ H1 := hσ.le.trans hσH1
  have hσ_inv : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ.le
  have hA0 : 0 ≤ A := by change 0 ≤ 1 + σ⁻¹ + H1 + L1; positivity
  have hrew : ∫ p, (|p.2.2| ^ j) ^ 2 * ‖(opS^[a] z) p‖ ^ 2 ∂(measureH c) =
      ∫ p in cell c, p.1 ^ (-(3 / 2 : ℝ)) * ((|p.2.2| ^ j) ^ 2 * ‖(opS^[a] z) p‖ ^ 2) := by
    rw [measureH, integral_withDensity_eq_integral_toReal_smul measurable_weightH
      (ae_weightH_lt_top c), cellMeasure]
    refine setIntegral_congr_fun (measurableSet_cell c) fun p hp => ?_
    have hp1 : 0 < p.1 := hp.1
    simp only [weightH, ENNReal.toReal_ofReal (Real.rpow_nonneg hp1.le _), smul_eq_mul]
  have hint1 := integrableOn_weighted_opS c σ H1 L1 hσ hz hsupp a j ha'
  have hint2 := (integrableOn_iteratedFDeriv_sq c σ H1 L1 hz hsupp a).const_mul (A ^ 6)
  have hint_le : ∫ p, (|p.2.2| ^ j) ^ 2 * ‖(opS^[a] z) p‖ ^ 2 ∂(measureH c) ≤
      A ^ 6 * ∫ p, ‖iteratedFDeriv ℝ a z p‖ ^ 2 ∂(cellMeasure c) := by
    rw [hrew, cellMeasure, ← integral_const_mul]
    exact setIntegral_mono hint1 hint2 (cell_pointwise_bound hσ hσH1 hL1 z hsupp a j ha' hj')
  have h0_lhs : 0 ≤ ∫ p, (|p.2.2| ^ j) ^ 2 * ‖(opS^[a] z) p‖ ^ 2 ∂(measureH c) :=
    integral_nonneg fun _ => by positivity
  have h0_int : 0 ≤ ∫ p, ‖iteratedFDeriv ℝ a z p‖ ^ 2 ∂(cellMeasure c) :=
    integral_nonneg fun _ => sq_nonneg _
  have hrpow : (∫ p, (|p.2.2| ^ j) ^ 2 * ‖(opS^[a] z) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) ≤
      A ^ 3 * (∫ p, ‖iteratedFDeriv ℝ a z p‖ ^ 2 ∂(cellMeasure c)) ^ (1 / 2 : ℝ) := by
    calc (∫ p, (|p.2.2| ^ j) ^ 2 * ‖(opS^[a] z) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ)
        ≤ (A ^ 6 * ∫ p, ‖iteratedFDeriv ℝ a z p‖ ^ 2 ∂(cellMeasure c)) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow h0_lhs hint_le (by norm_num)
      _ = (A ^ 6) ^ (1 / 2 : ℝ) *
          (∫ p, ‖iteratedFDeriv ℝ a z p‖ ^ 2 ∂(cellMeasure c)) ^ (1 / 2 : ℝ) :=
          Real.mul_rpow (by positivity) h0_int
      _ = A ^ 3 * (∫ p, ‖iteratedFDeriv ℝ a z p‖ ^ 2 ∂(cellMeasure c)) ^ (1 / 2 : ℝ) := by
          congr 1
          rw [show A ^ 6 = (A ^ 3) ^ (2 : ℝ) by
            rw [Real.rpow_two]
            ring, ← Real.rpow_mul (by positivity)]
          norm_num
  have ha7 : a ∈ Finset.range 7 := Finset.mem_range.mpr (by omega)
  have hle_h6 : (∫ p, ‖iteratedFDeriv ℝ a z p‖ ^ 2 ∂(cellMeasure c)) ^ (1 / 2 : ℝ) ≤
      h6Norm c z := by
    unfold h6Norm
    exact Finset.single_le_sum
      (f := fun k => (∫ p, ‖iteratedFDeriv ℝ k z p‖ ^ 2 ∂(cellMeasure c)) ^ (1 / 2 : ℝ))
      (fun k _ => Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _) ha7
  exact hrpow.trans (mul_le_mul_of_nonneg_left hle_h6 (by positivity))

end ObsBoxS1Aux

open ObsBoxS1Aux in
/-- **Observation-box `S^1` bound (`ObsBoxS1Bound`, task `PartII-a:N04/1`).** -/
theorem obsBoxS1Bound : ObsBoxS1Bound := by
  intro c σ H1 L1 _ hσ hσH1 hL1 z hz hsupp
  have hH1 : 0 ≤ H1 := hσ.le.trans hσH1
  have hσ_inv : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ.le
  calc ∑ a ∈ Finset.range 2, ∑ j ∈ Finset.range 2,
        (∫ p, (|p.2.2| ^ j) ^ 2 * ‖(opS^[a] z) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ)
      ≤ ∑ _a ∈ Finset.range 2, ∑ _j ∈ Finset.range 2,
          ((1 + σ⁻¹ + H1 + L1) ^ 3 * h6Norm c z) := by
        refine Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun j hj => ?_
        exact single_term_le c σ H1 L1 hσ hσH1 hL1 hz hsupp ha hj
    _ = 4 * (1 + σ⁻¹ + H1 + L1) ^ 3 * h6Norm c z := by
        simp [Finset.sum_const]
        ring

end UnforcedLeray.Short.PartIIa
