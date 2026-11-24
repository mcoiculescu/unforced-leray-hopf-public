import UnforcedLeray.Short.PartIIb.Sub.T12_6_2

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- The period strip of index `k`: `q ∈ [k c, k c + c)`, all `η`. -/
def ptbStrip (c : ℝ) (k : ℤ) : Set (ℝ × ℝ) :=
  Ico ((k : ℝ) * c) ((k : ℝ) * c + c) ×ˢ (univ : Set ℝ)

lemma ptbStrip_cover {c : ℝ} (hc : 0 < c) (R : ℝ) (m : ℕ) (hm : |R| / c ≤ m)
    (z : ℝ × ℝ) (hz : z.1 ∈ Icc (-R) R) :
    ∃ j : Fin (2 * m + 2), z ∈ ptbStrip c (((j : ℕ) : ℤ) - (m : ℤ) - 1) := by
  have hup : z.1 / c ≤ m :=
    le_trans (div_le_div_of_nonneg_right (by linarith [hz.2, le_abs_self R]) hc.le) hm
  have hdown : -(m : ℝ) ≤ z.1 / c := by
    have h1 : -|R| ≤ z.1 := by linarith [hz.1, le_abs_self R]
    have h2 : -(|R| / c) ≤ z.1 / c := by
      rw [← neg_div]; exact div_le_div_of_nonneg_right h1 hc.le
    linarith
  set k : ℤ := ⌊z.1 / c⌋ with hk
  have hk1 : (k : ℝ) ≤ z.1 / c := Int.floor_le _
  have hk2 : z.1 / c < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have hkm : k ≤ (m : ℤ) := by
    have : (k : ℝ) ≤ m := le_trans hk1 hup
    exact_mod_cast this
  have hkm' : -(m : ℤ) - 1 ≤ k := by
    have h1 : -(m : ℝ) - 1 < (k : ℝ) := by linarith
    have h' : -(m : ℤ) - 1 < k := by exact_mod_cast h1
    omega
  have hj0 : (0 : ℤ) ≤ k + m + 1 := by omega
  have hjv : (((k + m + 1).toNat : ℕ) : ℤ) = k + m + 1 := Int.toNat_of_nonneg hj0
  have hjlt : (k + m + 1).toNat < 2 * m + 2 := by omega
  refine ⟨⟨(k + m + 1).toNat, hjlt⟩, ?_⟩
  have hidx : (((k + m + 1).toNat : ℕ) : ℤ) - (m : ℤ) - 1 = k := by omega
  show z ∈ ptbStrip c ((((k + m + 1).toNat : ℕ) : ℤ) - (m : ℤ) - 1)
  rw [hidx]
  have e : z.1 / c * c = z.1 := div_mul_cancel₀ z.1 hc.ne'
  refine ⟨⟨?_, ?_⟩, mem_univ _⟩
  · have := mul_le_mul_of_nonneg_right hk1 hc.le
    linarith
  · have := mul_lt_mul_of_pos_right hk2 hc
    have h3 : ((k : ℝ) + 1) * c = (k : ℝ) * c + c := by ring
    linarith

theorem periodicBoxBound : UnforcedLeray.Short.IIb.PeriodicBoxBound := by
  unfold UnforcedLeray.Short.IIb.PeriodicBoxBound
  intro r c R hr hc
  have hr0 : 0 < r := by linarith
  have hr1 : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal hr0.le
  have h1r : (0 : ℝ) ≤ 1 / r := (div_pos one_pos hr0).le
  have h1r' : (0 : ℝ) ≤ 1 - 1 / r := by
    have : 1 / r ≤ 1 := by rw [div_le_one hr0]; linarith
    linarith
  set m : ℕ := ⌈|R| / c⌉₊ with hm_def
  have hm : |R| / c ≤ m := Nat.le_ceil _
  set N : ℕ := 2 * m + 2 with hN
  have hVfin : volume (Icc (-R) R ×ˢ Icc (-R) R) < ⊤ :=
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  refine ⟨(volume (Icc (-R) R ×ˢ Icc (-R) R) ^ (1 - 1 / r) * (N : ℝ≥0∞) ^ (1 / r) *
    (ENNReal.ofReal c) ^ (1 / r)).toReal, fun f hf hper => ?_⟩
  have hKfin : (volume (Icc (-R) R ×ˢ Icc (-R) R) ^ (1 - 1 / r) * (N : ℝ≥0∞) ^ (1 / r) *
      (ENNReal.ofReal c) ^ (1 / r)) ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg h1r' hVfin.ne)
        (ENNReal.rpow_ne_top_of_nonneg h1r (ENNReal.natCast_ne_top _)))
      (ENNReal.rpow_ne_top_of_nonneg h1r ENNReal.ofReal_ne_top)
  rw [ENNReal.ofReal_toReal hKfin]
  have hfB : AEStronglyMeasurable f (volume.restrict (Icc (-R) R ×ˢ Icc (-R) R)) := hf.restrict
  have hGper : Cyl.IsPeriodic c (fun z => ‖f z‖ₑ ^ r) := fun z => by simp only [hper z]
  -- Step 1: the box integral of `‖f‖^r` is at most `N` cells.
  have hI : ∫⁻ z in Icc (-R) R ×ˢ Icc (-R) R, ‖f z‖ₑ ^ r
      ≤ (N : ℝ≥0∞) * ∫⁻ z in Cyl.cell c, ‖f z‖ₑ ^ r := by
    have hsub : Icc (-R) R ×ˢ Icc (-R) R ⊆
        ⋃ j : Fin N, ptbStrip c (((j : ℕ) : ℤ) - (m : ℤ) - 1) := by
      intro z hz
      obtain ⟨j, hj⟩ := ptbStrip_cover hc R m hm z hz.1
      exact mem_iUnion.2 ⟨j, hj⟩
    calc ∫⁻ z in Icc (-R) R ×ˢ Icc (-R) R, ‖f z‖ₑ ^ r
        ≤ ∫⁻ z in ⋃ j : Fin N, ptbStrip c (((j : ℕ) : ℤ) - (m : ℤ) - 1), ‖f z‖ₑ ^ r :=
          lintegral_mono_set hsub
      _ ≤ ∑' j : Fin N, ∫⁻ z in ptbStrip c (((j : ℕ) : ℤ) - (m : ℤ) - 1), ‖f z‖ₑ ^ r :=
          lintegral_iUnion_le _ _
      _ = ∑ j : Fin N, ∫⁻ z in Cyl.cell c, ‖f z‖ₑ ^ r := by
          rw [tsum_fintype]
          apply Finset.sum_congr rfl
          intro j _
          exact Cyl.lintegral_strip_eq_cell hc hGper _
      _ = (N : ℝ≥0∞) * ∫⁻ z in Cyl.cell c, ‖f z‖ₑ ^ r := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- Step 2: Hölder on the box.
  have hHol := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := volume.restrict (Icc (-R) R ×ˢ Icc (-R) R)) (p := 1) (q := ENNReal.ofReal r)
    (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)) hfB
  rw [eLpNorm_one_eq_lintegral_enorm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hr0).ne'
      ENNReal.ofReal_ne_top, hr1, Measure.restrict_apply_univ] at hHol
  simp only [ENNReal.toReal_one, div_one] at hHol
  -- Step 3: the averaged norm.
  have hE : eLpNorm f (ENNReal.ofReal r) (Cyl.avgμ c)
      = (ENNReal.ofReal c⁻¹ * ∫⁻ z in Cyl.cell c, ‖f z‖ₑ ^ r) ^ (1 / r) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hr0).ne'
      ENNReal.ofReal_ne_top, hr1]
    unfold Cyl.avgμ Cyl.cellμ
    rw [lintegral_smul_measure, smul_eq_mul]
  -- Step 4: algebra.
  have hcc : ENNReal.ofReal c * ENNReal.ofReal c⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one]
  have hI' : (∫⁻ z in Cyl.cell c, ‖f z‖ₑ ^ r) ^ (1 / r)
      = (ENNReal.ofReal c) ^ (1 / r) * (ENNReal.ofReal c⁻¹ * ∫⁻ z in Cyl.cell c, ‖f z‖ₑ ^ r) ^ (1 / r) := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ h1r, ← mul_assoc, hcc, one_mul]
  rw [hE]
  calc ∫⁻ z in Icc (-R) R ×ˢ Icc (-R) R, ‖f z‖ₑ
      ≤ (∫⁻ z in Icc (-R) R ×ˢ Icc (-R) R, ‖f z‖ₑ ^ r) ^ (1 / r) *
          volume (Icc (-R) R ×ˢ Icc (-R) R) ^ (1 - 1 / r) := hHol
    _ ≤ ((N : ℝ≥0∞) * ∫⁻ z in Cyl.cell c, ‖f z‖ₑ ^ r) ^ (1 / r) *
          volume (Icc (-R) R ×ˢ Icc (-R) R) ^ (1 - 1 / r) :=
          mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow hI h1r) (by positivity)
    _ = (volume (Icc (-R) R ×ˢ Icc (-R) R) ^ (1 - 1 / r) * (N : ℝ≥0∞) ^ (1 / r) *
          (ENNReal.ofReal c) ^ (1 / r)) *
          (ENNReal.ofReal c⁻¹ * ∫⁻ z in Cyl.cell c, ‖f z‖ₑ ^ r) ^ (1 / r) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ h1r, hI']
          ring

end UnforcedLeray.Short.IIb
