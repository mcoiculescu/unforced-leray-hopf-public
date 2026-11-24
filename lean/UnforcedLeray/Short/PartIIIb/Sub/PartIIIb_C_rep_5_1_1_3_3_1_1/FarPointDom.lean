import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_1_3_3_1_1.FarPointDomKer

/-!
# `PartIII-b:C/rep/5/1/1/3/3/1/1/1`: pointwise domination of the masked far response

Source `the November 2 reference manuscript` 3604-3621 (`|∇K_t(x)| ≤ C|x|^{-4}`),
3905-3912, 5588-5589 (mask `t > e^δ s` gives `ϱ(z) < θ ϱ(y)`, `θ = e^{-δ/2}`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem fpd_varrho_le_norm (x : Space) : ϱ x ≤ ‖x‖ := by
  unfold ϱ
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp [Fin.sum_univ_three]
  nlinarith [sq_nonneg (x 2)]

theorem fpd_varrho_add (a b : Space) : ϱ (a + b) ≤ ϱ a + ϱ b := by
  have h : (a 0 * b 0 + a 1 * b 1) ^ 2 ≤ (ϱ a * ϱ b) ^ 2 := by
    rw [mul_pow, ϱ_sq, ϱ_sq]; nlinarith [sq_nonneg (a 0 * b 1 - a 1 * b 0)]
  have h2 := (abs_le_of_sq_le_sq' h (mul_nonneg (ϱ_nonneg a) (ϱ_nonneg b))).2
  unfold ϱ at *
  rw [Real.sqrt_le_left (by positivity)]
  have := ϱ_sq a
  have := ϱ_sq b
  unfold ϱ at *
  simp only [PiLp.add_apply]
  nlinarith [Real.sq_sqrt (show 0 ≤ a 0 ^ 2 + a 1 ^ 2 by positivity),
    Real.sq_sqrt (show 0 ≤ b 0 ^ 2 + b 1 ^ 2 by positivity)]

/-- Step (2): the radial gap. -/
theorem fpd_gap {y z : Space} {l θ : ℝ} (hl0 : 0 < l) (hl1 : l < 1)
    (hz : ϱ z < θ * ϱ y) : (1 - θ) * ϱ y ≤ ‖y - l • z‖ := by
  have h1 : ϱ (l • z) ≤ ϱ z := by
    rw [ϱ_smul, abs_of_pos hl0]
    nlinarith [ϱ_nonneg z]
  have h2 : ϱ y ≤ ϱ (y - l • z) + ϱ (l • z) := by
    have := fpd_varrho_add (y - l • z) (l • z)
    simpa using this
  have := fpd_varrho_le_norm (y - l • z)
  nlinarith

/-- Step (1): the mask gives the radial gap. -/
theorem fpd_mask {R δ s : ℝ} {z : Space} (hR : 0 < R) (hs : 0 < s)
    (hm : Real.exp δ * s < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2)) :
    ϱ z < Real.exp (-(δ / 2)) * (R / Real.sqrt s) := by
  have hq : 0 < z 0 ^ 2 + z 1 ^ 2 := by
    by_contra hq
    have : z 0 ^ 2 + z 1 ^ 2 = 0 := le_antisymm (not_lt.mp hq) (by positivity)
    rw [this] at hm
    simp at hm
    exact absurd hm (not_lt.mpr (by positivity))
  rw [lt_div_iff₀ hq] at hm
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hb : 0 < Real.exp (-(δ / 2)) * (R / Real.sqrt s) := by positivity
  apply lt_of_pow_lt_pow_left₀ 2 hb.le
  rw [ϱ_sq, mul_pow, div_pow, Real.sq_sqrt hs.le, ← Real.exp_nat_mul]
  have e1 : Real.exp (↑(2 : ℕ) * -(δ / 2)) * Real.exp δ = 1 := by
    rw [← Real.exp_add, show (↑(2 : ℕ) * -(δ / 2)) + δ = 0 by push_cast; ring, Real.exp_zero]
  have : (z 0 ^ 2 + z 1 ^ 2) * (Real.exp δ * s) < R ^ 2 := by linarith
  rw [show Real.exp (↑(2 : ℕ) * -(δ / 2)) * (R ^ 2 / s)
      = (R ^ 2 * Real.exp (↑(2 : ℕ) * -(δ / 2)) / s) by ring]
  rw [lt_div_iff₀ hs]
  have e2 := e1
  nlinarith [Real.exp_pos (↑(2 : ℕ) * -(δ / 2)), Real.exp_pos δ]

theorem fpd_entry_le (M : Matrix (Fin 3) (Fin 3) ℝ) (j k : Fin 3) :
    |M j k| ≤ UnforcedLeray.Short.IIIa.tensorNorm M := by
  unfold UnforcedLeray.Short.IIIa.tensorNorm
  apply Real.abs_le_sqrt
  calc M j k ^ 2 ≤ ∑ k', M j k' ^ 2 :=
        Finset.single_le_sum (f := fun k' => M j k' ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ k)
    _ ≤ ∑ j', ∑ k', M j' k' ^ 2 :=
        Finset.single_le_sum (f := fun j' => ∑ k', M j' k' ^ 2)
          (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity)) (Finset.mem_univ j)

theorem fpd_integrand_le {C ν R δ s l τ : ℝ} (hC : FarKerDeriv C) (hν : 0 < ν) (hR : 0 < R)
    (hδ : 0 < δ) (hs : 0 < s) (hl0 : 0 < l) (hl1 : l < 1)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (y : Space) (hy : ϱ y = R / Real.sqrt s)
    (i : Fin 3) (z : Space) :
    ‖∑ j : Fin 3, ∑ k : Fin 3,
      ((fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x) (y - l • z)
        (coordinateVector k) : ℝ) : ℂ) *
      (((fun (τ' : ℝ) (z : Space) =>
          if Real.exp δ * s < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) then T τ' z else 0)
        (τ + 2 * Real.log l) z j k : ℝ) : ℂ)‖ₑ ≤
    {z : Space | ϱ z < Real.exp (-(δ / 2)) * ϱ y}.indicator
      (fun z => ENNReal.ofReal (9 * |C|) *
        (ENNReal.ofReal ((‖y - l • z‖ ^ 4)⁻¹) *
          UnforcedLeray.Short.IIIa.srcNorm T (τ + 2 * Real.log l) z)) z := by
  by_cases hm : Real.exp δ * s < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2)
  · have hz : ϱ z < Real.exp (-(δ / 2)) * ϱ y := by rw [hy]; exact fpd_mask hR hs hm
    rw [Set.indicator_of_mem (show z ∈ _ from hz)]
    have hθ1 : Real.exp (-(δ / 2)) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
    have hys : 0 < ϱ y := by rw [hy]; positivity
    have hpos : 0 < ‖y - l • z‖ :=
      lt_of_lt_of_le (mul_pos (sub_pos.2 hθ1) hys) (fpd_gap hl0 hl1 hz)
    have hne : y - l • z ≠ 0 := norm_pos_iff.mp hpos
    have ht : 0 < ν * (1 - l ^ 2) := mul_pos hν (by nlinarith)
    have hw : 0 ≤ (‖y - l • z‖ ^ 4)⁻¹ := by positivity
    have htn : 0 ≤ UnforcedLeray.Short.IIIa.tensorNorm (T (τ + 2 * Real.log l) z) :=
      Real.sqrt_nonneg _
    simp only [if_pos hm]
    have hb : ∀ j k : Fin 3,
        ‖((fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x)
            (y - l • z) (coordinateVector k) : ℝ) : ℂ) *
          ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ)‖ ≤
        |C| * (‖y - l • z‖ ^ 4)⁻¹ *
          UnforcedLeray.Short.IIIa.tensorNorm (T (τ + 2 * Real.log l) z) := by
      intro j k
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 := hC _ ht _ hne i j k
      rw [Real.norm_eq_abs] at h1
      exact mul_le_mul (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hw))
        (fpd_entry_le _ j k) (abs_nonneg _) (by positivity)
    have hsum : ‖∑ j : Fin 3, ∑ k : Fin 3,
        ((fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x)
            (y - l • z) (coordinateVector k) : ℝ) : ℂ) *
          ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ)‖ ≤
        9 * |C| * ((‖y - l • z‖ ^ 4)⁻¹ *
          UnforcedLeray.Short.IIIa.tensorNorm (T (τ + 2 * Real.log l) z)) := by
      calc _ ≤ ∑ j : Fin 3, ‖∑ k : Fin 3,
              ((fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x)
                (y - l • z) (coordinateVector k) : ℝ) : ℂ) *
              ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ j : Fin 3, ∑ k : Fin 3, ‖((fderiv ℝ (fun x =>
              UnforcedLeray.Short.IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x)
                (y - l • z) (coordinateVector k) : ℝ) : ℂ) *
              ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ)‖ :=
            Finset.sum_le_sum (fun j _ => norm_sum_le _ _)
        _ ≤ ∑ j : Fin 3, ∑ k : Fin 3, |C| * (‖y - l • z‖ ^ 4)⁻¹ *
              UnforcedLeray.Short.IIIa.tensorNorm (T (τ + 2 * Real.log l) z) :=
            Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => hb j k))
        _ = 9 * |C| * ((‖y - l • z‖ ^ 4)⁻¹ *
              UnforcedLeray.Short.IIIa.tensorNorm (T (τ + 2 * Real.log l) z)) := by
            simp; ring
    rw [← ofReal_norm_eq_enorm]
    refine (ENNReal.ofReal_le_ofReal hsum).trans (le_of_eq ?_)
    unfold UnforcedLeray.Short.IIIa.srcNorm
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hw]
  · simp [hm]

theorem fpd_sepWfar_le {C ν μ R δ s τ : ℝ} (hC : FarKerDeriv C) (hν : 0 < ν)
    (hμ : -(1 / 4) < μ) (hR : 0 < R) (hδ : 0 < δ) (hs : 0 < s)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (y : Space) (hy : ϱ y = R / Real.sqrt s)
    (i : Fin 3) :
    ‖NearInst.sepWfar ν (μ : ℂ) R δ s T y τ i‖ₑ ≤
      ENNReal.ofReal (18 * |C|) *
        ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z in {z : Space | ϱ z < Real.exp (-(δ / 2)) * ϱ y},
          ENNReal.ofReal ((‖y - l • z‖ ^ 4)⁻¹) *
            UnforcedLeray.Short.IIIa.srcNorm T (τ + 2 * Real.log l) z := by
  have hS : MeasurableSet {z : Space | ϱ z < Real.exp (-(δ / 2)) * ϱ y} :=
    measurableSet_lt measurable_ϱ measurable_const
  unfold NearInst.sepWfar UnforcedLeray.Short.IIIa.sepW
  rw [enorm_mul]
  have h2 : ‖(-2 : ℂ)‖ₑ = 2 := by
    rw [← ofReal_norm_eq_enorm]; simp
  rw [h2]
  calc 2 * ‖∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * (μ : ℂ) + 2) * _‖ₑ
      ≤ 2 * ∫⁻ l in Ioo (0 : ℝ) 1, ‖(l : ℂ) ^ (2 * (μ : ℂ) + 2) * _‖ₑ := by
        gcongr; exact enorm_integral_le_lintegral_enorm _
    _ ≤ 2 * ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (9 * |C|) *
          ∫⁻ z in {z : Space | ϱ z < Real.exp (-(δ / 2)) * ϱ y},
            ENNReal.ofReal ((‖y - l • z‖ ^ 4)⁻¹) *
              UnforcedLeray.Short.IIIa.srcNorm T (τ + 2 * Real.log l) z := by
        gcongr 2 * ?_
        refine setLIntegral_mono' measurableSet_Ioo (fun l hl => ?_)
        rw [enorm_mul]
        have hn : ‖(l : ℂ) ^ (2 * (μ : ℂ) + 2)‖ₑ ≤ 1 := by
          rw [← ofReal_norm_eq_enorm, Complex.norm_cpow_eq_rpow_re_of_pos hl.1]
          have : (2 * (μ : ℂ) + 2).re = 2 * μ + 2 := by simp
          rw [this]
          have := Real.rpow_le_one hl.1.le hl.2.le (show 0 ≤ 2 * μ + 2 by linarith)
          simpa using this
        calc ‖(l : ℂ) ^ (2 * (μ : ℂ) + 2)‖ₑ * ‖∫ z : Space, _‖ₑ
            ≤ 1 * ∫⁻ z, ‖_‖ₑ := by
              gcongr; exact enorm_integral_le_lintegral_enorm _
          _ ≤ ∫⁻ z, {z : Space | ϱ z < Real.exp (-(δ / 2)) * ϱ y}.indicator
                (fun z => ENNReal.ofReal (9 * |C|) *
                  (ENNReal.ofReal ((‖y - l • z‖ ^ 4)⁻¹) *
                    UnforcedLeray.Short.IIIa.srcNorm T (τ + 2 * Real.log l) z)) z := by
              rw [one_mul]
              exact lintegral_mono (fun z =>
                fpd_integrand_le hC hν hR hδ hs hl.1 hl.2 T y hy i z)
          _ = _ := by
              rw [lintegral_indicator hS, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
          show (2 : ℝ≥0∞) * ENNReal.ofReal (9 * |C|) = ENNReal.ofReal (18 * |C|) by
            rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
            ring_nf]

theorem fpd_merRe_enorm_le (w : Fin 3 → ℂ) :
    ‖NearInst.merRe w‖ₑ ≤ ‖w 0‖ₑ + ‖w 2‖ₑ := by
  have h : ‖NearInst.merRe w‖ ≤ ‖w 0‖ + ‖w 2‖ := by
    unfold NearInst.merRe
    rw [EuclideanSpace.norm_eq]
    have h0 := Complex.abs_re_le_norm (w 0)
    have h2 := Complex.abs_re_le_norm (w 2)
    rw [Real.sqrt_le_left (by positivity)]
    simp [Fin.sum_univ_two]
    nlinarith [abs_nonneg (w 0).re, abs_nonneg (w 2).re, sq_abs (w 0).re, sq_abs (w 2).re,
      mul_nonneg (norm_nonneg (w 0)) (norm_nonneg (w 2)),
      mul_le_mul h0 h0 (abs_nonneg _) (norm_nonneg _),
      mul_le_mul h2 h2 (abs_nonneg _) (norm_nonneg _)]
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
    ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal h

theorem farPointDom_exists : ∃ C : ℝ, UnforcedLeray.Short.PartIIIb.Concrete.FarPointDom C := by
  obtain ⟨C0, hC0⟩ := farKerDeriv_exists
  refine ⟨36 * |C0|, fun ν μ R c δ hν hR hμ hδ f p hp => ?_⟩
  have hsq : 0 < Real.sqrt p.1 := Real.sqrt_pos.mpr hp
  have hy : ϱ (NearInst.chartY R p) = R / Real.sqrt p.1 := by
    unfold ϱ NearInst.chartY
    simp only [WithLp.ofLp_toLp]
    rw [show (![R / Real.sqrt p.1, 0, p.2.2 / Real.sqrt p.1] : Fin 3 → ℝ) 0 = R / Real.sqrt p.1
      from rfl, show (![R / Real.sqrt p.1, 0, p.2.2 / Real.sqrt p.1] : Fin 3 → ℝ) 1 = 0 from rfl]
    rw [zero_pow (by norm_num), add_zero, Real.sqrt_sq (by positivity)]
  have hB := fun i => fpd_sepWfar_le (τ := NearInst.chartTau R p) hC0 hν hμ hR hδ hp
    (NearInst.cartLift R c f) (NearInst.chartY R p) hy i
  have hK : wardYChartMaj R c (Real.exp (-(δ / 2))) f p =
      ENNReal.ofReal (Real.sqrt p.1)⁻¹ *
        ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z in {z : Space | ϱ z < Real.exp (-(δ / 2)) * ϱ (NearInst.chartY R p)},
          ENNReal.ofReal ((‖NearInst.chartY R p - l • z‖ ^ 4)⁻¹) *
            UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c f)
              (NearInst.chartTau R p + 2 * Real.log l) z := rfl
  rw [hK, enorm_smul]
  have h1 : ‖(Real.sqrt p.1)⁻¹‖ₑ = ENNReal.ofReal (Real.sqrt p.1)⁻¹ := by
    rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (by positivity)]
  rw [h1]
  set K := ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z in {z : Space | ϱ z < Real.exp (-(δ / 2)) * ϱ (NearInst.chartY R p)},
          ENNReal.ofReal ((‖NearInst.chartY R p - l • z‖ ^ 4)⁻¹) *
            UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c f)
              (NearInst.chartTau R p + 2 * Real.log l) z with hKdef
  calc ENNReal.ofReal (Real.sqrt p.1)⁻¹ * ‖NearInst.merRe (-NearInst.sepWfar ν (μ : ℂ) R δ p.1
          (NearInst.cartLift R c f) (NearInst.chartY R p) (NearInst.chartTau R p))‖ₑ
      ≤ ENNReal.ofReal (Real.sqrt p.1)⁻¹ * (ENNReal.ofReal (18 * |C0|) * K + ENNReal.ofReal (18 * |C0|) * K) := by
        gcongr
        refine (fpd_merRe_enorm_le _).trans ?_
        simp only [Pi.neg_apply, enorm_neg]
        exact add_le_add (hB 0) (hB 2)
    _ = _ := by
        rw [← two_mul, ← mul_assoc (2 : ℝ≥0∞), show (2 : ℝ≥0∞) * ENNReal.ofReal (18 * |C0|)
          = ENNReal.ofReal (36 * |C0|) by
            rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
            ring_nf]
        ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
