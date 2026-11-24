import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PositiveKernel

/-!
# Minkowski's integral inequality in `L²` (source 4002)

Proves `phaseMinkowski_holds : PhaseMinkowski` (defined in `Sub/PositiveKernel.lean`).

Route: for a finite measure, truncate `ψ = ∫_S F(l,·) dl` at level `n`, so that the truncated
`L²` norm is finite; duality (Tonelli plus Hölder in `a` for each `l`) gives `I ≤ √I · M`, hence
`√I ≤ M`; then monotone convergence in `n`. The general `SFinite` measure is reduced to finite
pieces `∑_{k<K} sfiniteSeq ν k`, again by monotone convergence.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- `⨆ n, min x n = x` in `[0, ∞]`. -/
private lemma pm_iSup_min (x : ℝ≥0∞) : (⨆ n : ℕ, min x (n : ℝ≥0∞)) = x := by
  by_cases hx : x = ⊤
  · rw [hx]
    simp only [min_eq_right le_top]
    exact ENNReal.iSup_natCast
  · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hx
    apply le_antisymm
    · exact iSup_le fun n => min_le_left _ _
    · exact le_iSup_of_le n (min_eq_left hn.le).ge

/-- Minkowski's inequality for a finite measure, with truncation. -/
private lemma pm_fin (α : Type) [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (F : ℝ → α → ℝ≥0∞) (hF : Measurable (Function.uncurry F)) (S : Set ℝ) (hS : MeasurableSet S) :
    (∫⁻ a, (∫⁻ l : ℝ in S, F l a) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) ≤
      ∫⁻ l : ℝ in S, (∫⁻ a, F l a ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
  set ψ : α → ℝ≥0∞ := fun a => ∫⁻ l : ℝ in S, F l a with hψdef
  have hψm : Measurable ψ := (hF.comp measurable_swap).lintegral_prod_right'
  have hFl : ∀ l : ℝ, Measurable (fun a => F l a) := fun l =>
    hF.comp (measurable_const.prodMk measurable_id)
  set M : ℝ≥0∞ := ∫⁻ l : ℝ in S, (∫⁻ a, F l a ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) with hM
  have hkey : ∀ n : ℕ, (∫⁻ a, (min (ψ a) (n : ℝ≥0∞)) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) ≤ M := by
    intro n
    set T : α → ℝ≥0∞ := fun a => min (ψ a) (n : ℝ≥0∞) with hT
    have hTm : Measurable T := hψm.min measurable_const
    have hTle : ∀ a, T a ≤ (n : ℝ≥0∞) := fun a => min_le_right _ _
    have hTtop : ∀ a, T a ≠ ⊤ := fun a =>
      ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (hTle a)
    have hTT : ∀ a, T a ^ (2 : ℝ) ≤ T a * ψ a := by
      intro a
      rw [ENNReal.rpow_two, pow_two]
      gcongr
      exact min_le_left _ _
    set I : ℝ≥0∞ := ∫⁻ a, T a ^ (2 : ℝ) ∂μ with hI
    have hIle : I ≤ (n : ℝ≥0∞) ^ (2 : ℝ) * μ Set.univ := by
      calc I ≤ ∫⁻ _a, (n : ℝ≥0∞) ^ (2 : ℝ) ∂μ :=
            lintegral_mono fun a => ENNReal.rpow_le_rpow (hTle a) (by norm_num)
        _ = (n : ℝ≥0∞) ^ (2 : ℝ) * μ Set.univ := lintegral_const _
    have hIfin : I ≠ ⊤ :=
      ne_top_of_le_ne_top
        (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
          (ENNReal.natCast_ne_top n)) (measure_ne_top μ _)) hIle
    have hA : I ≤ ∫⁻ a, T a * ψ a ∂μ := lintegral_mono hTT
    have hB : ∫⁻ a, T a * ψ a ∂μ = ∫⁻ l : ℝ in S, ∫⁻ a, T a * F l a ∂μ := by
      have h1 : ∀ a, T a * ψ a = ∫⁻ l : ℝ in S, T a * F l a := fun a =>
        (lintegral_const_mul' _ _ (hTtop a)).symm
      calc ∫⁻ a, T a * ψ a ∂μ = ∫⁻ a, (∫⁻ l : ℝ in S, T a * F l a) ∂μ :=
            lintegral_congr fun a => h1 a
        _ = ∫⁻ l : ℝ in S, ∫⁻ a, T a * F l a ∂μ := by
            apply lintegral_lintegral_swap
            exact ((hTm.comp measurable_fst).mul
              (hF.comp (measurable_snd.prodMk measurable_fst))).aemeasurable
    have hH : ∀ l : ℝ, ∫⁻ a, T a * F l a ∂μ ≤
        I ^ (1 / 2 : ℝ) * (∫⁻ a, F l a ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := fun l =>
      ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hTm.aemeasurable
        (hFl l).aemeasurable
    have hC : ∫⁻ l : ℝ in S, ∫⁻ a, T a * F l a ∂μ ≤ I ^ (1 / 2 : ℝ) * M := by
      calc ∫⁻ l : ℝ in S, ∫⁻ a, T a * F l a ∂μ
          ≤ ∫⁻ l : ℝ in S, I ^ (1 / 2 : ℝ) * (∫⁻ a, F l a ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) :=
            lintegral_mono fun l => hH l
        _ = I ^ (1 / 2 : ℝ) * M :=
            lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hIfin)
    have hsq : I ≤ I ^ (1 / 2 : ℝ) * M := hA.trans (hB.le.trans hC)
    have hr : I ^ (1 / 2 : ℝ) ≤ M := by
      have hr2 : (I ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = I := by
        rw [← ENNReal.rpow_mul]
        norm_num
      have hrfin : I ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hIfin
      rcases eq_or_ne (I ^ (1 / 2 : ℝ)) 0 with h0 | h0
      · rw [h0]
        exact zero_le
      · have hrr : I ^ (1 / 2 : ℝ) * I ^ (1 / 2 : ℝ) = I := by
          calc I ^ (1 / 2 : ℝ) * I ^ (1 / 2 : ℝ) = (I ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
                rw [ENNReal.rpow_two, pow_two]
            _ = I := hr2
        have hle : I ^ (1 / 2 : ℝ) * I ^ (1 / 2 : ℝ) ≤ M * I ^ (1 / 2 : ℝ) := by
          rw [hrr, mul_comm M]
          exact hsq
        exact (ENNReal.mul_le_mul_iff_left h0 hrfin).mp hle
    exact hr
  -- pointwise: the truncations increase to `ψ`
  have hpt : ∀ a, ψ a ^ (2 : ℝ) = ⨆ n : ℕ, (min (ψ a) (n : ℝ≥0∞)) ^ (2 : ℝ) := by
    intro a
    simp only [ENNReal.rpow_two]
    conv_lhs => rw [← pm_iSup_min (ψ a)]
    exact Monotone.map_iSup_of_continuousAt (f := fun x : ℝ≥0∞ => x ^ 2)
      (g := fun n : ℕ => min (ψ a) (n : ℝ≥0∞)) (ENNReal.continuous_pow 2).continuousAt
      (fun x y hxy => pow_le_pow_left₀ (by positivity) hxy 2) (by simp)
  have hsupI : ∫⁻ a, ψ a ^ (2 : ℝ) ∂μ = ⨆ n : ℕ, ∫⁻ a, (min (ψ a) (n : ℝ≥0∞)) ^ (2 : ℝ) ∂μ := by
    calc ∫⁻ a, ψ a ^ (2 : ℝ) ∂μ
        = ∫⁻ a, ⨆ n : ℕ, (min (ψ a) (n : ℝ≥0∞)) ^ (2 : ℝ) ∂μ := lintegral_congr fun a => hpt a
      _ = ⨆ n : ℕ, ∫⁻ a, (min (ψ a) (n : ℝ≥0∞)) ^ (2 : ℝ) ∂μ := by
          apply lintegral_iSup (f := fun n a => (min (ψ a) (n : ℝ≥0∞)) ^ (2 : ℝ))
          · intro n
            exact (hψm.min measurable_const).pow_const _
          · intro m n hmn a
            exact ENNReal.rpow_le_rpow (min_le_min_left _ (Nat.cast_le.mpr hmn)) (by norm_num)
  have hbd : ∀ n : ℕ, ∫⁻ a, (min (ψ a) (n : ℝ≥0∞)) ^ (2 : ℝ) ∂μ ≤ M ^ (2 : ℝ) := by
    intro n
    calc ∫⁻ a, (min (ψ a) (n : ℝ≥0∞)) ^ (2 : ℝ) ∂μ
        = ((∫⁻ a, (min (ψ a) (n : ℝ≥0∞)) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
          rw [← ENNReal.rpow_mul]
          norm_num
      _ ≤ M ^ (2 : ℝ) := ENNReal.rpow_le_rpow (hkey n) (by norm_num)
  calc (∫⁻ a, ψ a ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)
      = (⨆ n : ℕ, ∫⁻ a, (min (ψ a) (n : ℝ≥0∞)) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
        rw [hsupI]
    _ ≤ (M ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow (iSup_le hbd) (by norm_num)
    _ = M := by
        rw [← ENNReal.rpow_mul]
        norm_num

/-- Minkowski's inequality for a general `SFinite` measure, from the finite case. -/
private lemma pm_general (α : Type) [MeasurableSpace α] (ν : Measure α) [SFinite ν]
    (F : ℝ → α → ℝ≥0∞) (hF : Measurable (Function.uncurry F)) (S : Set ℝ) (hS : MeasurableSet S) :
    (∫⁻ a, (∫⁻ l : ℝ in S, F l a) ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) ≤
      ∫⁻ l : ℝ in S, (∫⁻ a, F l a ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) := by
  set μ : ℕ → Measure α := sfiniteSeq ν with hμ
  set νK : ℕ → Measure α := fun K => ∑ k ∈ Finset.range K, μ k with hνK
  have hfin : ∀ K, IsFiniteMeasure (νK K) := by
    intro K
    constructor
    simp only [hνK, Measure.coe_finsetSum, Finset.sum_apply]
    exact ENNReal.sum_lt_top.mpr fun k _ => measure_lt_top _ _
  have hle : ∀ K, νK K ≤ ν := by
    intro K
    calc νK K ≤ Measure.sum μ := by
          apply Measure.le_iff'.mpr
          intro s
          calc (νK K) s = ∑ k ∈ Finset.range K, μ k s := by
                simp only [hνK, Measure.coe_finsetSum, Finset.sum_apply]
            _ ≤ ∑' k, μ k s := ENNReal.sum_le_tsum _
            _ ≤ Measure.sum μ s := Measure.le_sum_apply μ s
      _ = ν := sum_sfiniteSeq ν
  set Mν : ℝ≥0∞ := ∫⁻ l : ℝ in S, (∫⁻ a, F l a ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) with hMν
  have hR : ∀ K, ∫⁻ l : ℝ in S, (∫⁻ a, F l a ^ (2 : ℝ) ∂(νK K)) ^ (1 / 2 : ℝ) ≤ Mν := by
    intro K
    apply lintegral_mono
    intro l
    exact ENNReal.rpow_le_rpow (lintegral_mono' (hle K) le_rfl) (by norm_num)
  have hbdK : ∀ K, ∫⁻ a, (∫⁻ l : ℝ in S, F l a) ^ (2 : ℝ) ∂(νK K) ≤ Mν ^ (2 : ℝ) := by
    intro K
    have := hfin K
    have h1 := pm_fin α (νK K) F hF S hS
    have h2 := h1.trans (hR K)
    calc ∫⁻ a, (∫⁻ l : ℝ in S, F l a) ^ (2 : ℝ) ∂(νK K)
        = ((∫⁻ a, (∫⁻ l : ℝ in S, F l a) ^ (2 : ℝ) ∂(νK K)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
          rw [← ENNReal.rpow_mul]
          norm_num
      _ ≤ Mν ^ (2 : ℝ) := ENNReal.rpow_le_rpow h2 (by norm_num)
  have hLim : ∫⁻ a, (∫⁻ l : ℝ in S, F l a) ^ (2 : ℝ) ∂ν =
      ⨆ K, ∫⁻ a, (∫⁻ l : ℝ in S, F l a) ^ (2 : ℝ) ∂(νK K) := by
    conv_lhs => rw [← sum_sfiniteSeq ν]
    rw [lintegral_sum_measure, ENNReal.tsum_eq_iSup_nat]
    refine iSup_congr fun K => ?_
    simp only [hνK]
    rw [lintegral_finsetSum_measure]
  calc (∫⁻ a, (∫⁻ l : ℝ in S, F l a) ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ)
      = (⨆ K, ∫⁻ a, (∫⁻ l : ℝ in S, F l a) ^ (2 : ℝ) ∂(νK K)) ^ (1 / 2 : ℝ) := by rw [hLim]
    _ ≤ (Mν ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow (iSup_le hbdK) (by norm_num)
    _ = Mν := by
        rw [← ENNReal.rpow_mul]
        norm_num

/-- **Minkowski's integral inequality in `L²`** (source 4002). -/
theorem phaseMinkowski_holds : PhaseMinkowski := by
  intro α _ ν _ F hF S hS
  exact pm_general α ν F hF S hS

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
