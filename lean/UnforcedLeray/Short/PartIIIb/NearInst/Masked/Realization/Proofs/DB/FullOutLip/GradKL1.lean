import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_1_2_3.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_1_2_3.L2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L2
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# `GradKL1` (source 3604-3610)

Heat scaling `K_t(x) = t^{-3/2} K_1(x/√t)` (`HeatLerayScale`) gives
`∇K_t(x) = t^{-2} (∇K_1)(x/√t)`, and `∫|∇K_t| = t^{-1/2} ∫|∇K_1|`. The integral
`∫|∇K_1| < ∞` uses that `K_1` is `C³` (`HeatLerayKSmooth`) and the decay
`|∇K_1(x)| ≤ C|x|^{-4}` (`SepKernelBounds`, `j = 0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal

open UnforcedLeray
open UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

/-- Real form of `gradKNorm` (the sum of absolute values). -/
def gk1Sum (t : ℝ) (w : Space) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
    |fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK t i j x) w (coordinateVector k)|

theorem gk1_gradKNorm_eq (t : ℝ) (w : Space) : gradKNorm t w = ENNReal.ofReal (gk1Sum t w) := rfl

theorem gk1_norm_cv (k : Fin 3) : ‖(coordinateVector k : Space)‖ = 1 := by
  simp [coordinateVector]

theorem gk1_abs_apply_le (L : Space →L[ℝ] ℝ) (k : Fin 3) :
    |L (coordinateVector k)| ≤ ‖L‖ := by
  have h := L.le_opNorm (coordinateVector k)
  rw [gk1_norm_cv k, mul_one, Real.norm_eq_abs] at h
  exact h

theorem gk1_rpow_neg_four (r : ℝ) (hr : 0 < r) : r ^ (-4 : ℝ) = (r ^ 4)⁻¹ := by
  rw [show (-4 : ℝ) = ((-4 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
  simp [zpow_neg]

theorem gk1_decay :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : Space, w ≠ 0 → gk1Sum 1 w ≤ C * (‖w‖ ^ 4)⁻¹ := by
  obtain ⟨C0, hC0⟩ := UnforcedLeray.Short.IIIa.sepKernelBounds 0
  refine ⟨27 * |C0|, by positivity, fun w hw => ?_⟩
  have hr : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hterm : ∀ i j k : Fin 3,
      |fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK 1 i j x) w (coordinateVector k)|
        ≤ |C0| * (‖w‖ ^ 4)⁻¹ := by
    intro i j k
    have h := ((hC0 w hw i j).1) 1 one_pos
    change ‖iteratedFDeriv ℝ 1 (fun y => UnforcedLeray.Short.IIIa.heatLerayK 1 i j y) w‖
      ≤ C0 * ‖w‖ ^ (-4 - ((0 : ℕ) : ℝ)) at h
    rw [norm_iteratedFDeriv_one, Nat.cast_zero, sub_zero] at h
    rw [gk1_rpow_neg_four _ hr] at h
    have h2 := gk1_abs_apply_le
      (fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK 1 i j x) w) k
    exact h2.trans (h.trans (mul_le_mul_of_nonneg_right (le_abs_self C0) (by positivity)))
  unfold gk1Sum
  calc _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, |C0| * (‖w‖ ^ 4)⁻¹ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          Finset.sum_le_sum fun k _ => hterm i j k
    _ = 27 * |C0| * (‖w‖ ^ 4)⁻¹ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

theorem gk1_cont : Continuous (gk1Sum 1) := by
  unfold gk1Sum
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_finsetSum _ fun k _ => ?_
  have hd : Continuous (fun w : Space =>
      fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK 1 i j x) w) :=
    (UnforcedLeray.Short.PartIIIb.Concrete.heatLerayKSmooth 1 one_pos i j).continuous_fderiv
      (by norm_num)
  exact continuous_abs.comp (hd.clm_apply continuous_const)

theorem gk1_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ w : Space, gk1Sum 1 w ≤ K * ((1 + ‖w‖) ^ 4)⁻¹ := by
  obtain ⟨C, hC, hdec⟩ := gk1_decay
  obtain ⟨M, hM⟩ :=
    (isCompact_closedBall (0 : Space) 1).exists_bound_of_continuousOn gk1_cont.continuousOn
  refine ⟨16 * |M| + 16 * C, by positivity, fun w => ?_⟩
  have hpos : 0 < (1 + ‖w‖) ^ 4 := by positivity
  rcases le_total ‖w‖ 1 with h1 | h1
  · have hq : (1 + ‖w‖) ^ 4 ≤ 16 := by
      have h0 : 0 ≤ 1 + ‖w‖ := by positivity
      have h2 : 1 + ‖w‖ ≤ 2 := by linarith
      have := pow_le_pow_left₀ h0 h2 4
      norm_num at this
      linarith
    have hgw : gk1Sum 1 w ≤ |M| := by
      have h := hM w (mem_closedBall_zero_iff.2 h1)
      rw [Real.norm_eq_abs] at h
      exact (le_abs_self _).trans (h.trans (le_abs_self M))
    have key : gk1Sum 1 w ≤ (16 * |M| + 16 * C) * ((1 + ‖w‖) ^ 4)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hpos]
      nlinarith [abs_nonneg M, mul_nonneg hC hpos.le]
    exact key
  · have hw : w ≠ 0 := by
      intro h
      rw [h, norm_zero] at h1
      linarith
    have hr : 0 < ‖w‖ := by linarith
    have hr4 : 0 < ‖w‖ ^ 4 := by positivity
    have h4 : (1 + ‖w‖) ^ 4 ≤ 16 * ‖w‖ ^ 4 := by
      have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1 + ‖w‖)
        (show 1 + ‖w‖ ≤ 2 * ‖w‖ by linarith) 4
      nlinarith [h]
    have key1 : gk1Sum 1 w ≤ C * (‖w‖ ^ 4)⁻¹ := hdec w hw
    have key2 : C * (‖w‖ ^ 4)⁻¹ ≤ (16 * C) * ((1 + ‖w‖) ^ 4)⁻¹ := by
      rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ hr4 hpos]
      nlinarith [mul_le_mul_of_nonneg_left h4 hC]
    have key3 : (16 * C) * ((1 + ‖w‖) ^ 4)⁻¹ ≤ (16 * |M| + 16 * C) * ((1 + ‖w‖) ^ 4)⁻¹ := by
      apply mul_le_mul_of_nonneg_right _ (inv_nonneg.2 hpos.le)
      nlinarith [abs_nonneg M]
    exact key1.trans (key2.trans key3)

theorem gk1_lintegral_lt_top : ∫⁻ w : Space, ENNReal.ofReal (gk1Sum 1 w) < ⊤ := by
  obtain ⟨K, hK, hb⟩ := gk1_bound
  have hint : Integrable (fun w : Space => ((1 + ‖w‖) ^ 4)⁻¹) := by
    refine (integrable_one_add_norm (μ := volume) (r := 4) ?_).congr
      (Filter.Eventually.of_forall fun w => ?_)
    · rw [finrank_euclideanSpace_fin]; norm_num
    · show (1 + ‖w‖) ^ (-4 : ℝ) = _
      rw [gk1_rpow_neg_four _ (by positivity : (0:ℝ) < 1 + ‖w‖)]
  calc ∫⁻ w : Space, ENNReal.ofReal (gk1Sum 1 w)
      ≤ ∫⁻ w : Space, ENNReal.ofReal K * ENNReal.ofReal (((1 + ‖w‖) ^ 4)⁻¹) := by
        refine lintegral_mono fun w => ?_
        rw [← ENNReal.ofReal_mul hK]
        exact ENNReal.ofReal_le_ofReal (hb w)
    _ = ENNReal.ofReal K * ∫⁻ w : Space, ENNReal.ofReal (((1 + ‖w‖) ^ 4)⁻¹) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint.lintegral_lt_top

theorem gk1_rpow_three_halves (t : ℝ) (ht : 0 < t) :
    t ^ (-(3 / 2 : ℝ)) = ((Real.sqrt t)⁻¹) ^ 3 := by
  have hA : (t ^ (1 / 2 : ℝ)) ^ 3 = t ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
  rw [Real.sqrt_eq_rpow, inv_pow, hA, Real.rpow_neg ht.le]

theorem gk1_rpow_half (t : ℝ) (ht : 0 < t) : t ^ (-(1 / 2 : ℝ)) = (Real.sqrt t)⁻¹ := by
  rw [Real.rpow_neg ht.le, Real.sqrt_eq_rpow]

theorem gk1_fderiv_scale (t : ℝ) (ht : 0 < t) (i j : Fin 3) (w : Space) (k : Fin 3) :
    fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK t i j x) w (coordinateVector k)
      = (((Real.sqrt t)⁻¹) ^ 3 * (Real.sqrt t)⁻¹) *
        fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK 1 i j x)
          ((Real.sqrt t)⁻¹ • w) (coordinateVector k) := by
  have hS := UnforcedLeray.Short.PartIIIb.Concrete.heatLerayScale_of
    UnforcedLeray.Short.PartIIIb.Concrete.heatGTailScale
  unfold UnforcedLeray.Short.PartIIIb.Concrete.HeatLerayScale at hS
  have hfun : (fun x => UnforcedLeray.Short.IIIa.heatLerayK t i j x)
      = fun x => ((Real.sqrt t)⁻¹) ^ 3 *
          UnforcedLeray.Short.IIIa.heatLerayK 1 i j ((Real.sqrt t)⁻¹ • x) := by
    funext x
    rw [hS t ht i j x, gk1_rpow_three_halves t ht]
  have hK1 : Differentiable ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK 1 i j x) :=
    (UnforcedLeray.Short.PartIIIb.Concrete.heatLerayKSmooth 1 one_pos i j).differentiable
      (by norm_num)
  have hL : HasFDerivAt (fun x : Space => (Real.sqrt t)⁻¹ • x)
      ((Real.sqrt t)⁻¹ • ContinuousLinearMap.id ℝ Space) w :=
    ((Real.sqrt t)⁻¹ • ContinuousLinearMap.id ℝ Space).hasFDerivAt
  have hc := ((hK1 ((Real.sqrt t)⁻¹ • w)).hasFDerivAt.comp w hL).const_mul
    (((Real.sqrt t)⁻¹) ^ 3)
  have hc' := hc.fderiv
  rw [hfun]
  rw [show (fun x : Space => ((Real.sqrt t)⁻¹) ^ 3 *
      UnforcedLeray.Short.IIIa.heatLerayK 1 i j ((Real.sqrt t)⁻¹ • x))
      = fun y => ((Real.sqrt t)⁻¹) ^ 3 *
        ((fun x => UnforcedLeray.Short.IIIa.heatLerayK 1 i j x) ∘ fun x => (Real.sqrt t)⁻¹ • x) y
      from rfl, hc']
  simp [ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul]
  ring

theorem gk1_gsum_scale (t : ℝ) (ht : 0 < t) (w : Space) :
    gk1Sum t w = (((Real.sqrt t)⁻¹) ^ 3 * (Real.sqrt t)⁻¹) * gk1Sum 1 ((Real.sqrt t)⁻¹ • w) := by
  have hpos : 0 ≤ ((Real.sqrt t)⁻¹) ^ 3 * (Real.sqrt t)⁻¹ := by
    have : 0 < (Real.sqrt t)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 ht)
    positivity
  unfold gk1Sum
  simp only [gk1_fderiv_scale t ht, abs_mul, abs_of_nonneg hpos, Finset.mul_sum]

theorem gk1_lintegral_comp_smul (s : ℝ) (hs : 0 < s) (F : Space → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ w : Space, F (s • w) = ENNReal.ofReal ((s ^ 3)⁻¹) * ∫⁻ v : Space, F v := by
  rw [← lintegral_map hF (measurable_const_smul s), Measure.map_addHaar_smul volume hs.ne',
    lintegral_smul_measure, finrank_euclideanSpace_fin,
    abs_of_pos (inv_pos.2 (pow_pos hs 3)), smul_eq_mul]

/-- **`GradKL1`** (source 3604-3610): `∫ Σ|∂_k (K_t)_{ij}| ≤ C t^{-1/2}`. -/
theorem gradKL1 : UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.GradKL1 := by
  refine ⟨(∫⁻ w : Space, ENNReal.ofReal (gk1Sum 1 w)).toReal, ENNReal.toReal_nonneg,
    fun t ht => ?_⟩
  rw [ENNReal.ofReal_toReal gk1_lintegral_lt_top.ne]
  have hs : 0 < (Real.sqrt t)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 ht)
  have h1 : ∫⁻ w : Space, gradKNorm t w
      = ∫⁻ w : Space, ENNReal.ofReal (((Real.sqrt t)⁻¹) ^ 3 * (Real.sqrt t)⁻¹) *
          ENNReal.ofReal (gk1Sum 1 ((Real.sqrt t)⁻¹ • w)) := by
    refine lintegral_congr fun w => ?_
    rw [gk1_gradKNorm_eq, gk1_gsum_scale t ht w,
      ENNReal.ofReal_mul (by positivity)]
  have hmeas : Measurable (fun v : Space => ENNReal.ofReal (gk1Sum 1 v)) :=
    ENNReal.measurable_ofReal.comp gk1_cont.measurable
  have h2 : ∫⁻ w : Space, ENNReal.ofReal (gk1Sum 1 ((Real.sqrt t)⁻¹ • w))
      = ENNReal.ofReal (((Real.sqrt t)⁻¹ ^ 3)⁻¹) *
          ∫⁻ v : Space, ENNReal.ofReal (gk1Sum 1 v) :=
    gk1_lintegral_comp_smul _ hs (fun v => ENNReal.ofReal (gk1Sum 1 v)) hmeas
  rw [h1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, h2, gk1_rpow_half t ht]
  have hal : ((Real.sqrt t)⁻¹) ^ 3 * (Real.sqrt t)⁻¹ * ((((Real.sqrt t)⁻¹) ^ 3)⁻¹)
      = (Real.sqrt t)⁻¹ := by
    field_simp
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hal, mul_comm]
