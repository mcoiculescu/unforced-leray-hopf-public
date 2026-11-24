import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_7_3_1

/-!
# Part II-b, leaf `DeqhsPeriodicBox` (SP 1923-1927): finite box integrals of periodic `L^r(cell)` functions

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
Route. For `r > 1`, `x ≤ 1 + x^r` in `ℝ≥0∞`, so `∫_box h ≤ vol(box) + ∫_box h^r`. The box is covered by
finitely many period strips `[-c/2 + nc, -c/2 + nc + c) × ℝ` (`|n| ≤ N`), and each strip has the same
`h^r`-integral as the cell (`Cyl.lintegral_strip_eq_cell`, periodicity of `h^r`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- `x ≤ 1 + x^r` in `ℝ≥0∞` for `r > 1`. -/
theorem le_one_add_rpow_box {r : ℝ} (hr : 1 < r) (x : ℝ≥0∞) : x ≤ 1 + x ^ r := by
  by_cases hx : x ≤ 1
  · exact hx.trans le_self_add
  · push_neg at hx
    have h1 : x ^ (1 : ℝ) ≤ x ^ r := ENNReal.rpow_le_rpow_of_exponent_le hx.le hr.le
    rw [ENNReal.rpow_one] at h1
    exact h1.trans le_add_self

/-- **Leaf `PartII-b:T12/7/3/1/4`** (SP 1923-1927): a measurable, everywhere `c`-periodic function in
`L^r(cell)`, `r > 1`, has finite lintegral over every box. -/
theorem deqhsPeriodicBox : UnforcedLeray.Short.IIb.DeqhsPeriodicBox := by
  intro c r hc hr h hmeas hper hfin R
  have hr0 : 0 < r := by linarith
  have hHm : Measurable (fun z => h z ^ r) := hmeas.pow_const r
  have hHper : UnforcedLeray.Cyl.IsPeriodic c (fun z => h z ^ r) := fun z => by
    simp only [hper z]
  -- (1) the cell integral of `h^r` is finite
  have hCell : ∫⁻ z in UnforcedLeray.Cyl.cell c, h z ^ r < ⊤ := by
    have h1 := hfin
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (ENNReal.ofReal_pos.2 hr0).ne'
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hr0.le] at h1
    unfold UnforcedLeray.Cyl.cellμ at h1
    simpa only [enorm_eq_self] using h1
  -- (2) every period strip has the same `h^r` integral as the cell
  have hStrip : ∀ n : ℤ, ∫⁻ z in Ico (-c / 2 + (n : ℝ) * c) (-c / 2 + (n : ℝ) * c + c) ×ˢ
      (univ : Set ℝ), h z ^ r < ⊤ := fun n => by
    rw [UnforcedLeray.Cyl.lintegral_strip_eq_cell hc hHper (-c / 2 + (n : ℝ) * c)]
    exact hCell
  -- (3) cover of the box by finitely many strips
  obtain ⟨N, hN⟩ := exists_nat_gt (|R| / c + 1)
  have hNc : |R| + c < (N : ℝ) * c := by
    have h1 : |R| / c * c = |R| := div_mul_cancel₀ _ hc.ne'
    have h2 := mul_lt_mul_of_pos_right hN hc
    rw [add_mul, one_mul, h1] at h2
    linarith
  let T : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let S : ℤ → Set (ℝ × ℝ) := fun n => Ico (-c / 2 + (n : ℝ) * c) (-c / 2 + (n : ℝ) * c + c) ×ˢ
    (univ : Set ℝ)
  have hSm : ∀ n : ℤ, MeasurableSet (S n) := fun n =>
    (measurableSet_Ico).prod MeasurableSet.univ
  have hcover : ∀ z ∈ Icc (-R) R ×ˢ Icc (-R) R, ∃ n ∈ T, z ∈ S n := by
    intro z hz
    have hz1 : z.1 ∈ Icc (-R) R := (mem_prod.1 hz).1
    rw [mem_Icc] at hz1
    obtain ⟨hz1a, hz1b⟩ := hz1
    have hf1 : ((⌊(z.1 + c / 2) / c⌋ : ℤ) : ℝ) ≤ (z.1 + c / 2) / c := Int.floor_le _
    have hf2 : (z.1 + c / 2) / c < ((⌊(z.1 + c / 2) / c⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    set n : ℤ := ⌊(z.1 + c / 2) / c⌋ with hn
    have hf1' : (n : ℝ) * c ≤ z.1 + c / 2 := (le_div_iff₀ hc).1 hf1
    have hf2' : z.1 + c / 2 < ((n : ℝ) + 1) * c := (div_lt_iff₀ hc).1 hf2
    have hsplit : ((n : ℝ) + 1) * c = (n : ℝ) * c + c := by ring
    have hup : (n : ℝ) * c < (N : ℝ) * c := by
      linarith [le_abs_self R, hf1', hNc, hc]
    have hup' : (n : ℝ) < N := lt_of_mul_lt_mul_right hup hc.le
    have hup2 : n ≤ (N : ℤ) := by exact_mod_cast hup'.le
    have hlo : -(N : ℤ) ≤ n := by
      by_contra hcon
      push_neg at hcon
      have h3 : ((n : ℝ) + 1) ≤ -(N : ℝ) := by
        have h4 : n + 1 ≤ -(N : ℤ) := by omega
        exact_mod_cast h4
      have h4 : ((n : ℝ) + 1) * c ≤ -((N : ℝ) * c) := by nlinarith [h3, hc]
      linarith [le_abs_self R, neg_abs_le R, hz1a, hf2', hNc, hc, h4]
    refine ⟨n, Finset.mem_Icc.2 ⟨hlo, hup2⟩, ?_⟩
    refine mem_prod.2 ⟨⟨?_, ?_⟩, mem_univ _⟩
    · linarith [hf1']
    · linarith [hf2', hsplit]
  -- (4) the box integral of `h^r` is bounded by the sum of strip integrals
  have hBm : MeasurableSet (Icc (-R) R ×ˢ Icc (-R) R) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hbox_r : ∫⁻ z in Icc (-R) R ×ˢ Icc (-R) R, h z ^ r < ⊤ := by
    have hsum_fin : ∑ n ∈ T, ∫⁻ z in S n, h z ^ r < ⊤ :=
      ENNReal.sum_lt_top.2 fun n _ => hStrip n
    have hle : ∫⁻ z in Icc (-R) R ×ˢ Icc (-R) R, h z ^ r ≤ ∑ n ∈ T, ∫⁻ z in S n, h z ^ r := by
      calc ∫⁻ z in Icc (-R) R ×ˢ Icc (-R) R, h z ^ r
          = ∫⁻ z, (Icc (-R) R ×ˢ Icc (-R) R).indicator (fun z => h z ^ r) z :=
            (lintegral_indicator hBm _).symm
        _ ≤ ∫⁻ z, ∑ n ∈ T, (S n).indicator (fun z => h z ^ r) z := by
            refine lintegral_mono fun z => ?_
            by_cases hz : z ∈ Icc (-R) R ×ˢ Icc (-R) R
            · obtain ⟨n, hnT, hzS⟩ := hcover z hz
              rw [indicator_of_mem hz]
              calc h z ^ r = (S n).indicator (fun z => h z ^ r) z :=
                    (indicator_of_mem hzS (fun z => h z ^ r)).symm
                _ ≤ ∑ m ∈ T, (S m).indicator (fun z => h z ^ r) z :=
                    Finset.single_le_sum (f := fun m => (S m).indicator (fun z => h z ^ r) z)
                      (fun m _ => zero_le) hnT
            · rw [indicator_of_notMem hz]
              exact zero_le
        _ = ∑ n ∈ T, ∫⁻ z, (S n).indicator (fun z => h z ^ r) z :=
            lintegral_finset_sum T (fun n _ => hHm.indicator (hSm n))
        _ = ∑ n ∈ T, ∫⁻ z in S n, h z ^ r :=
            Finset.sum_congr rfl fun n _ => lintegral_indicator (hSm n) _
    exact lt_of_le_of_lt hle hsum_fin
  -- (5) `h ≤ 1 + h^r` on the box
  have hvol : volume (Icc (-R) R ×ˢ Icc (-R) R) < ⊤ :=
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  have hle2 : ∫⁻ z in Icc (-R) R ×ˢ Icc (-R) R, h z ≤
      ∫⁻ z in Icc (-R) R ×ˢ Icc (-R) R, (1 + h z ^ r) :=
    lintegral_mono fun z => le_one_add_rpow_box hr (h z)
  have hadd : ∫⁻ z in Icc (-R) R ×ˢ Icc (-R) R, (1 + h z ^ r) =
      (volume (Icc (-R) R ×ˢ Icc (-R) R)) + ∫⁻ z in Icc (-R) R ×ˢ Icc (-R) R, h z ^ r := by
    rw [lintegral_add_left measurable_const]
    simp
  exact lt_of_le_of_lt hle2 (by rw [hadd]; exact ENNReal.add_lt_top.2 ⟨hvol, hbox_r⟩)

end UnforcedLeray.Short.IIb
