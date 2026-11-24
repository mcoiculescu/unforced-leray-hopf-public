import UnforcedLeray.Short.PartIIb.Sub.T12_1_3_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.MollApprox.CylLocInt.Cover
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.MollApprox.CylMollSmoothPeriodic

/-!
# Leaf `T12/1/3/1/c`: the mollification `ρ * D` is bounded

Proves `cylMollBounded : CylMollBounded` (SP 1923-1926).

* `cylMoll` is `c`-periodic (`cylMollSmoothPeriodic`), so the sup over `z` reduces to centres with
  `|z.1| ≤ c`.
* The integrand is supported in `closedBall z ρ.rOut` and bounded by `sup|ρ.normed|`
  (`integral_sub_left_eq_self`, `norm_integral_le_of_norm_le`).
* On a closed ball `B` of fixed radius, with centre in the strip `|z.1| ≤ c`, a fixed number of
  cells covers `B` (`closedBall_subset_fixed`), so `∫_B |D|^r` is bounded uniformly; Hölder on the
  finite-measure ball (`eLpNorm_le_eLpNorm_mul_rpow_measure_univ`) bounds `∫_B |D|` uniformly.
Helpers `shiftCell`, `lintegral_shiftCell`, `lintegral_biUnion_le` are from `CylLocInt/Cover.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open CylLocIntCover UnforcedLeray.Cyl

/-- Fixed-radius covering: if `|z₀.1| + |R| + c < N c`, the ball lies in the `2N+1` shifted cells. -/
theorem closedBall_subset_fixed {c : ℝ} (hc : 0 < c) (z0 : ℝ × ℝ) (R : ℝ) (N : ℕ)
    (hN : |z0.1| + |R| + c < (N : ℝ) * c) :
    Metric.closedBall z0 R ⊆ ⋃ m ∈ Finset.Icc (-(N : ℤ)) N, shiftCell c m := by
  have hNc : |z0.1| + |R| + c < (N : ℝ) * c := hN
  intro w hw
  have hd : dist w z0 ≤ R := hw
  have hd1 : dist w.1 z0.1 ≤ R := le_trans (le_max_left _ _) (by rw [← Prod.dist_eq]; exact hd)
  rw [Real.dist_eq] at hd1
  have hb := abs_le.mp (le_trans hd1 (le_abs_self R))
  have hwA1 : w.1 ≤ |z0.1| + |R| := by
    linarith [le_abs_self z0.1, le_abs_self R, abs_nonneg z0.1, hb.2]
  have hwA2 : -(|z0.1| + |R|) ≤ w.1 := by
    linarith [neg_abs_le z0.1, neg_abs_le R, abs_nonneg z0.1, hb.1]
  set k : ℤ := ⌊(w.1 + c / 2) / c⌋ with hk
  have hk1' : (k : ℝ) * c ≤ w.1 + c / 2 := (le_div_iff₀ hc).1 (Int.floor_le _)
  have hk2' : w.1 + c / 2 < ((k : ℝ) + 1) * c := (div_lt_iff₀ hc).1 (Int.lt_floor_add_one _)
  have hmem : w ∈ shiftCell c (-k) := by
    rw [mem_shiftCell_iff]
    push_cast
    constructor <;> nlinarith
  refine Set.mem_iUnion₂.2 ⟨-k, ?_, hmem⟩
  rw [Finset.mem_Icc]
  constructor
  · by_contra hcon
    push Not at hcon
    have hk3 : (N : ℝ) + 1 ≤ (k : ℝ) := by
      have h4 : (k : ℤ) ≥ (N : ℤ) + 1 := by omega
      exact_mod_cast h4
    nlinarith
  · by_contra hcon
    push Not at hcon
    have hk3 : (k : ℝ) + 1 ≤ -(N : ℝ) := by
      have h4 : (k : ℤ) + 1 ≤ -(N : ℤ) := by omega
      exact_mod_cast h4
    nlinarith

theorem lintegral_closedBall_fixed {c : ℝ} (hc : 0 < c) {g : ℝ × ℝ → ℝ≥0∞}
    (hper : IsPeriodic c g) (z0 : ℝ × ℝ) (R : ℝ) (N : ℕ)
    (hN : |z0.1| + |R| + c < (N : ℝ) * c) :
    ∫⁻ w in Metric.closedBall z0 R, g w ≤ ((2 * N + 1 : ℕ) : ℝ≥0∞) * ∫⁻ w in cell c, g w := by
  have hcard : (Finset.Icc (-(N : ℤ)) N).card = 2 * N + 1 := by
    rw [Int.card_Icc]; omega
  calc ∫⁻ w in Metric.closedBall z0 R, g w
      ≤ ∫⁻ w in ⋃ m ∈ Finset.Icc (-(N : ℤ)) N, shiftCell c m, g w :=
        lintegral_mono_set (closedBall_subset_fixed hc z0 R N hN)
    _ ≤ ∑ m ∈ Finset.Icc (-(N : ℤ)) N, ∫⁻ w in shiftCell c m, g w := lintegral_biUnion_le _ _ _
    _ = ∑ m ∈ Finset.Icc (-(N : ℤ)) N, ∫⁻ w in cell c, g w :=
        Finset.sum_congr rfl fun m _ => lintegral_shiftCell hc hper m
    _ = ((2 * N + 1 : ℕ) : ℝ≥0∞) * ∫⁻ w in cell c, g w := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]

theorem cylMollBounded : CylMollBounded := by
  intro c r hc hr D hD ρ
  have hr1 : (1 : ℝ) ≤ r := hr.le
  have hr0 : 0 < r := by linarith
  have hper : IsPeriodic c D := hD.1
  have hcell : MemLp D (ENNReal.ofReal r) (cellμ c) := memLp_cell_of_avg hc hD.2
  have hAE : AEStronglyMeasurable D (volume : Measure (ℝ × ℝ)) :=
    aestronglyMeasurable_of_cell hc hper hcell.aestronglyMeasurable
  have hperM : IsPeriodic c (cylMoll ρ D) := (cylMollSmoothPeriodic c r hc hr D hD ρ).1
  have hcont : Continuous (ρ.normed volume) := ρ.continuous_normed
  have hsupp : HasCompactSupport (ρ.normed volume) := ρ.hasCompactSupport_normed
  obtain ⟨M1, hM1⟩ := hcont.bounded_above_of_compact_support hsupp
  have hM1nn : 0 ≤ M1 := le_trans (norm_nonneg _) (hM1 0)
  have hgper : IsPeriodic c (fun w => ‖D w‖ₑ ^ r) := fun z => by
    show ‖D (z.1 + c, z.2)‖ₑ ^ r = ‖D z‖ₑ ^ r
    rw [hper z]
  have hIr : ∫⁻ w in cell c, ‖D w‖ₑ ^ r < ⊤ := by
    have h1 := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (μ := cellμ c)
      (ENNReal.ofReal_pos.2 hr0).ne' ENNReal.ofReal_ne_top hcell.eLpNorm_lt_top
    rwa [ENNReal.toReal_ofReal hr0.le] at h1
  obtain ⟨N, hN⟩ := exists_nat_gt ((2 * c + |ρ.rOut|) / c)
  have hN' : 2 * c + |ρ.rOut| < (N : ℝ) * c := (div_lt_iff₀ hc).1 hN
  -- the uniform bound on the ball integrals of `|D|`, for centres in the strip `|z.1| ≤ c`
  have hV : volume (Metric.closedBall (0 : ℝ × ℝ) ρ.rOut) < ⊤ :=
    (isCompact_closedBall (0 : ℝ × ℝ) ρ.rOut).measure_lt_top
  obtain ⟨Kc, hKc⟩ : ∃ K : ℝ≥0∞, K = (((2 * N + 1 : ℕ) : ℝ≥0∞) * ∫⁻ w in cell c, ‖D w‖ₑ ^ r) ^ (1 / r)
      * (volume (Metric.closedBall (0 : ℝ × ℝ) ρ.rOut)) ^ (1 / (1 : ℝ) - 1 / r) := ⟨_, rfl⟩
  have hexp : (0 : ℝ) ≤ 1 / (1 : ℝ) - 1 / r := by
    rw [div_one, sub_nonneg, div_le_one hr0]; exact hr1
  have hKcfin : Kc < ⊤ := by
    rw [hKc]
    refine ENNReal.mul_lt_top ?_ ?_
    · exact ENNReal.rpow_lt_top_of_nonneg (by positivity)
        (ENNReal.mul_lt_top (ENNReal.natCast_ne_top _).lt_top hIr).ne
    · exact ENNReal.rpow_lt_top_of_nonneg hexp hV.ne
  have hball : ∀ z0 : ℝ × ℝ, |z0.1| ≤ c →
      ∫⁻ w in Metric.closedBall z0 ρ.rOut, ‖D w‖ₑ ≤ Kc := by
    intro z0 hz0
    have h1 : ∫⁻ w in Metric.closedBall z0 ρ.rOut, ‖D w‖ₑ ^ r ≤
        ((2 * N + 1 : ℕ) : ℝ≥0∞) * ∫⁻ w in cell c, ‖D w‖ₑ ^ r :=
      lintegral_closedBall_fixed hc hgper z0 ρ.rOut N (by
        have : |z0.1| + |ρ.rOut| + c ≤ 2 * c + |ρ.rOut| := by linarith
        linarith)
    have hLp : eLpNorm D (ENNReal.ofReal r)
        (volume.restrict (Metric.closedBall z0 ρ.rOut)) ≤
        (((2 * N + 1 : ℕ) : ℝ≥0∞) * ∫⁻ w in cell c, ‖D w‖ₑ ^ r) ^ (1 / r) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hr0).ne'
        ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hr0.le]
      exact ENNReal.rpow_le_rpow h1 (by positivity)
    have hpq : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := ENNReal.one_le_ofReal.2 hr1
    have hH := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq (hAE.restrict
      (s := Metric.closedBall z0 ρ.rOut))
    rw [eLpNorm_one_eq_lintegral_enorm, Measure.restrict_apply_univ,
      Measure.addHaar_closedBall_center (volume : Measure (ℝ × ℝ)) z0 ρ.rOut,
      ENNReal.toReal_one, ENNReal.toReal_ofReal hr0.le] at hH
    rw [hKc]
    exact le_trans hH (mul_le_mul_of_nonneg_right hLp zero_le)
  -- pointwise bound by the ball integral of `|D|`
  have hpt : ∀ z : ℝ × ℝ, ‖cylMoll ρ D z‖ ≤
      M1 * ∫ w in Metric.closedBall z ρ.rOut, ‖D w‖ := by
    intro z
    have hIntOn : IntegrableOn D (Metric.closedBall z ρ.rOut) volume :=
      integrableOn_closedBall_of_cell hc hr1 hper hcell z ρ.rOut
    have e : cylMoll ρ D z = ∫ t, ρ.normed volume (z - t) • D t := by
      unfold cylMoll
      have h := integral_sub_left_eq_self (fun y => ρ.normed volume y • D (z - y)) volume z
      simp only [sub_sub_cancel] at h
      exact h.symm
    rw [e]
    calc ‖∫ t, ρ.normed volume (z - t) • D t‖
        ≤ ∫ t, M1 * (Metric.closedBall z ρ.rOut).indicator (fun w => ‖D w‖) t := by
          apply norm_integral_le_of_norm_le
          · exact ((integrable_indicator_iff measurableSet_closedBall).2 hIntOn.norm).const_mul M1
          · refine Eventually.of_forall fun t => ?_
            by_cases ht : t ∈ Metric.closedBall z ρ.rOut
            · rw [indicator_of_mem ht, norm_smul]
              exact mul_le_mul_of_nonneg_right (hM1 _) (norm_nonneg _)
            · rw [indicator_of_notMem ht]
              have h0 : ρ.normed volume (z - t) = 0 := by
                by_contra hne
                have hmem : z - t ∈ Function.support (ρ.normed volume) := hne
                rw [ContDiffBump.support_normed_eq, Metric.mem_ball, dist_zero_right] at hmem
                apply ht
                rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
                exact hmem.le
              rw [h0, zero_smul, norm_zero, mul_zero]
      _ = M1 * ∫ t in Metric.closedBall z ρ.rOut, ‖D t‖ := by
          rw [integral_const_mul, integral_indicator measurableSet_closedBall]
  -- bound for centres in the strip
  have hfin : ∀ z : ℝ × ℝ, |z.1| ≤ c → ‖cylMoll ρ D z‖ ≤ M1 * Kc.toReal := by
    intro z hz
    have hint : ∫ t in Metric.closedBall z ρ.rOut, ‖D t‖ ≤ Kc.toReal := by
      rw [integral_norm_eq_lintegral_enorm (hAE.restrict (s := Metric.closedBall z ρ.rOut))]
      exact ENNReal.toReal_mono hKcfin.ne (hball z hz)
    exact (hpt z).trans (mul_le_mul_of_nonneg_left hint hM1nn)
  refine ⟨M1 * Kc.toReal, fun z i => ?_⟩
  obtain ⟨m, hm1, hm2⟩ := exists_shift_mem hc z.1
  have hzeq : cylMoll ρ D (z.1 + (m : ℝ) * c, z.2) = cylMoll ρ D z := hperM.add_int_mul m z
  have hz' : |(z.1 + (m : ℝ) * c, z.2).1| ≤ c := by
    show |z.1 + (m : ℝ) * c| ≤ c
    rw [abs_le]
    constructor <;> linarith
  calc ‖cylMoll ρ D z i‖ ≤ ‖cylMoll ρ D z‖ := PiLp.norm_apply_le _ _
    _ = ‖cylMoll ρ D (z.1 + (m : ℝ) * c, z.2)‖ := by rw [hzeq]
    _ ≤ M1 * Kc.toReal := hfin _ hz'

end UnforcedLeray.Short.IIb
