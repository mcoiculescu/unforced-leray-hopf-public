import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2

/-!
# Minkowski's integral inequality in `L²` (`PartIII-b:C/near/masked/14/2`, task `minkowskiL2`)

Proof of `MinkowskiL2` (general fact, no source-specific input). Mathlib has no Minkowski
integral inequality, so the proof is elementary:

* Finite measure `ρ`: with `φ = min F N`, `F x = ∫ g l x dν`, Tonelli and Hölder (exponents 2, 2)
  give `∫ φ² dρ ≤ (∫ φ² dρ)^{1/2} · R`, hence `(∫ φ² dρ)^{1/2} ≤ R`; letting `N → ∞`
  (monotone convergence) gives the claim for `ρ`.
* General `μ`: `μ` is the sum of the finite measures `sfiniteSeq μ i`; the partial sums
  `ρ_n` are finite, the integrals over `μ` are the suprema over `n` of the integrals over `ρ_n`,
  and `ρ_n`-integrals of nonnegative functions are bounded by the `μ`-integrals.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- Minkowski's inequality in `L²` for a finite measure `ρ`. -/
theorem minkowskiL2_finite (ρ : Measure Chart) [IsFiniteMeasure ρ] (ν : Measure ℝ) [SFinite ν]
    (g : ℝ → Chart → ℝ≥0∞) (hg : Measurable (Function.uncurry g)) :
    ∫⁻ x, (∫⁻ l, g l x ∂ν) ^ (2 : ℝ) ∂ρ ≤
      (∫⁻ l, (∫⁻ x, (g l x) ^ (2 : ℝ) ∂ρ) ^ ((1 : ℝ) / 2) ∂ν) ^ (2 : ℝ) := by
  have hg' : Measurable (fun p : Chart × ℝ => g p.2 p.1) := hg.comp measurable_swap
  have hF : Measurable (fun x : Chart => ∫⁻ l, g l x ∂ν) :=
    Measurable.lintegral_prod_right' (f := fun p : Chart × ℝ => g p.2 p.1) hg'
  have hG2 : Measurable (fun l : ℝ => ∫⁻ x, (g l x) ^ (2 : ℝ) ∂ρ) :=
    Measurable.lintegral_prod_right' (f := fun p : ℝ × Chart => (g p.1 p.2) ^ (2 : ℝ))
      (hg.pow_const _)
  have hG : Measurable (fun l : ℝ => (∫⁻ x, (g l x) ^ (2 : ℝ) ∂ρ) ^ ((1 : ℝ) / 2)) :=
    hG2.pow_const _
  -- truncated bound
  have key : ∀ N : ℕ, ∫⁻ x, (min (∫⁻ l, g l x ∂ν) (N : ℝ≥0∞)) ^ (2 : ℝ) ∂ρ ≤
      ((∫⁻ l, (∫⁻ x, (g l x) ^ (2 : ℝ) ∂ρ) ^ ((1 : ℝ) / 2) ∂ν) ^ (2 : ℝ)) := by
    intro N
    have hφ : Measurable (fun x : Chart => min (∫⁻ l, g l x ∂ν) (N : ℝ≥0∞)) :=
      hF.min measurable_const
    have hφle : ∀ x : Chart, min (∫⁻ l, g l x ∂ν) (N : ℝ≥0∞) ≤ (N : ℝ≥0∞) :=
      fun x => min_le_right _ _
    have hφfin : ∀ x : Chart, min (∫⁻ l, g l x ∂ν) (N : ℝ≥0∞) ≠ ⊤ :=
      fun x => ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (hφle x)
    set A : ℝ≥0∞ := ∫⁻ x, (min (∫⁻ l, g l x ∂ν) (N : ℝ≥0∞)) ^ (2 : ℝ) ∂ρ with hAdef
    set R : ℝ≥0∞ := ∫⁻ l, (∫⁻ x, (g l x) ^ (2 : ℝ) ∂ρ) ^ ((1 : ℝ) / 2) ∂ν with hRdef
    have hAfin : A ≠ ⊤ := by
      have hle : A ≤ ∫⁻ _x, (N : ℝ≥0∞) ^ (2 : ℝ) ∂ρ :=
        lintegral_mono fun x => ENNReal.rpow_le_rpow (hφle x) (by norm_num)
      rw [lintegral_const] at hle
      exact ne_top_of_le_ne_top
        (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.natCast_ne_top N))
          (measure_ne_top ρ Set.univ)) hle
    have h1 : A ≤ ∫⁻ x, min (∫⁻ l, g l x ∂ν) (N : ℝ≥0∞) * (∫⁻ l, g l x ∂ν) ∂ρ := by
      refine lintegral_mono fun x => ?_
      rw [ENNReal.rpow_two, pow_two]
      exact mul_le_mul_of_nonneg_left (min_le_left _ _) zero_le
    have h2 : ∫⁻ x, min (∫⁻ l, g l x ∂ν) (N : ℝ≥0∞) * (∫⁻ l, g l x ∂ν) ∂ρ =
        ∫⁻ x, ∫⁻ l, min (∫⁻ l', g l' x ∂ν) (N : ℝ≥0∞) * g l x ∂ν ∂ρ := by
      refine lintegral_congr fun x => ?_
      rw [lintegral_const_mul' _ _ (hφfin x)]
    have h3 : ∫⁻ x, ∫⁻ l, min (∫⁻ l', g l' x ∂ν) (N : ℝ≥0∞) * g l x ∂ν ∂ρ =
        ∫⁻ l, ∫⁻ x, min (∫⁻ l', g l' x ∂ν) (N : ℝ≥0∞) * g l x ∂ρ ∂ν := by
      refine lintegral_lintegral_swap ?_
      exact ((hφ.comp measurable_fst).mul hg').aemeasurable
    have h4 : ∀ l : ℝ, ∫⁻ x, min (∫⁻ l', g l' x ∂ν) (N : ℝ≥0∞) * g l x ∂ρ ≤
        A ^ ((1 : ℝ) / 2) * (∫⁻ x, (g l x) ^ (2 : ℝ) ∂ρ) ^ ((1 : ℝ) / 2) := by
      intro l
      have hgl : AEMeasurable (fun x : Chart => g l x) ρ :=
        (hg.comp (measurable_prodMk_left (x := l))).aemeasurable
      have := ENNReal.lintegral_mul_le_Lp_mul_Lq ρ (p := 2) (q := 2)
        Real.HolderConjugate.two_two hφ.aemeasurable hgl
      exact this
    have h5 : ∫⁻ l, ∫⁻ x, min (∫⁻ l', g l' x ∂ν) (N : ℝ≥0∞) * g l x ∂ρ ∂ν ≤
        A ^ ((1 : ℝ) / 2) * R := by
      calc ∫⁻ l, ∫⁻ x, min (∫⁻ l', g l' x ∂ν) (N : ℝ≥0∞) * g l x ∂ρ ∂ν
          ≤ ∫⁻ l, A ^ ((1 : ℝ) / 2) * (∫⁻ x, (g l x) ^ (2 : ℝ) ∂ρ) ^ ((1 : ℝ) / 2) ∂ν :=
            lintegral_mono h4
        _ = A ^ ((1 : ℝ) / 2) * R := lintegral_const_mul _ hG
    have h6 : A ≤ A ^ ((1 : ℝ) / 2) * R :=
      calc A ≤ _ := h1
        _ = _ := h2
        _ = _ := h3
        _ ≤ _ := h5
    have hA2 : A ^ ((1 : ℝ) / 2) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hAfin
    have hsq : A ^ ((1 : ℝ) / 2) * A ^ ((1 : ℝ) / 2) = A := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num
    have h7 : A ^ ((1 : ℝ) / 2) ≤ R := by
      by_cases h0 : A ^ ((1 : ℝ) / 2) = 0
      · rw [h0]; exact zero_le
      · have h8 : A ^ ((1 : ℝ) / 2) * A ^ ((1 : ℝ) / 2) ≤ A ^ ((1 : ℝ) / 2) * R := by
          rw [hsq]; exact h6
        exact (ENNReal.mul_le_mul_iff_right h0 hA2).1 h8
    calc A = (A ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) := by
          rw [← ENNReal.rpow_mul]; norm_num
      _ ≤ R ^ (2 : ℝ) := ENNReal.rpow_le_rpow h7 (by norm_num)
  -- monotone convergence in the truncation
  have hsup : ∀ v : ℝ≥0∞, ⨆ N : ℕ, (min v (N : ℝ≥0∞)) ^ (2 : ℝ) = v ^ (2 : ℝ) := by
    intro v
    have hv : ⨆ N : ℕ, min v (N : ℝ≥0∞) = v := by
      by_cases hvt : v = ⊤
      · subst hvt
        simp [ENNReal.iSup_natCast]
      · refine le_antisymm (iSup_le fun N => min_le_left _ _) ?_
        obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hvt
        exact le_iSup_of_le N (by rw [min_eq_left hN.le])
    have hcont : ContinuousAt (fun y : ℝ≥0∞ => y ^ (2 : ℝ)) (⨆ N : ℕ, min v (N : ℝ≥0∞)) := by
      rw [hv]
      have : (fun y : ℝ≥0∞ => y ^ (2 : ℝ)) = fun y : ℝ≥0∞ => y ^ (2 : ℕ) := by
        funext y; rw [ENNReal.rpow_two]
      rw [this]
      exact (ENNReal.continuous_pow 2).continuousAt
    have hmono : Monotone (fun y : ℝ≥0∞ => y ^ (2 : ℝ)) :=
      fun a b hab => ENNReal.rpow_le_rpow hab (by norm_num)
    have hbot : (fun y : ℝ≥0∞ => y ^ (2 : ℝ)) ⊥ = ⊥ := by
      show (⊥ : ℝ≥0∞) ^ (2 : ℝ) = ⊥
      rw [ENNReal.bot_eq_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
    have := Monotone.map_iSup_of_continuousAt (f := fun y : ℝ≥0∞ => y ^ (2 : ℝ))
      (g := fun N : ℕ => min v (N : ℝ≥0∞)) hcont hmono hbot
    simp only [hv] at this
    exact this.symm
  have hmain : ∫⁻ x, (∫⁻ l, g l x ∂ν) ^ (2 : ℝ) ∂ρ ≤
      ((∫⁻ l, (∫⁻ x, (g l x) ^ (2 : ℝ) ∂ρ) ^ ((1 : ℝ) / 2) ∂ν) ^ (2 : ℝ)) := by
    calc ∫⁻ x, (∫⁻ l, g l x ∂ν) ^ (2 : ℝ) ∂ρ
        = ∫⁻ x, ⨆ N : ℕ, (min (∫⁻ l, g l x ∂ν) (N : ℝ≥0∞)) ^ (2 : ℝ) ∂ρ :=
          lintegral_congr fun x => (hsup _).symm
      _ = ⨆ N : ℕ, ∫⁻ x, (min (∫⁻ l, g l x ∂ν) (N : ℝ≥0∞)) ^ (2 : ℝ) ∂ρ := by
          refine lintegral_iSup (fun N => ?_) (fun M N hMN x => ?_)
          · exact (hF.min measurable_const).pow_const _
          · exact ENNReal.rpow_le_rpow (min_le_min_left _ (Nat.cast_le.2 hMN)) (by norm_num)
      _ ≤ _ := iSup_le key
  exact hmain

/-- **Minkowski's integral inequality in `L²`** (proved). -/
theorem minkowskiL2 : UnforcedLeray.Short.PartIIIb.NearInst.Masked.MinkowskiL2 := by
  unfold MinkowskiL2
  intro μ ν _ _ g hg
  have hfin : ∀ n : ℕ, IsFiniteMeasure (∑ i ∈ Finset.range n, sfiniteSeq μ i) := by
    intro n
    induction n with
    | zero => rw [Finset.range_zero, Finset.sum_empty]; infer_instance
    | succ k ih =>
        rw [Finset.sum_range_succ]
        have := ih
        infer_instance
  -- integrals over `μ` are suprema over the finite partial sums
  have hsup : ∀ h : Chart → ℝ≥0∞, ∫⁻ x, h x ∂μ =
      ⨆ n : ℕ, ∫⁻ x, h x ∂(∑ i ∈ Finset.range n, sfiniteSeq μ i) := by
    intro h
    calc ∫⁻ x, h x ∂μ = ∫⁻ x, h x ∂(Measure.sum (sfiniteSeq μ)) := by
          rw [sum_sfiniteSeq]
      _ = ∑' i, ∫⁻ x, h x ∂(sfiniteSeq μ i) := lintegral_sum_measure _ _
      _ = ⨆ n : ℕ, ∑ i ∈ Finset.range n, ∫⁻ x, h x ∂(sfiniteSeq μ i) :=
          ENNReal.tsum_eq_iSup_nat
      _ = ⨆ n : ℕ, ∫⁻ x, h x ∂(∑ i ∈ Finset.range n, sfiniteSeq μ i) :=
          iSup_congr fun n => (lintegral_finsetSum_measure _ _ _).symm
  -- partial sums are dominated by `μ`
  have hle : ∀ (h : Chart → ℝ≥0∞) (n : ℕ),
      ∫⁻ x, h x ∂(∑ i ∈ Finset.range n, sfiniteSeq μ i) ≤ ∫⁻ x, h x ∂μ := by
    intro h n
    rw [hsup h]
    exact le_iSup (fun n : ℕ => ∫⁻ x, h x ∂(∑ i ∈ Finset.range n, sfiniteSeq μ i)) n
  have hR : ∀ n : ℕ, ∫⁻ l, (∫⁻ x, (g l x) ^ (2 : ℝ) ∂(∑ i ∈ Finset.range n, sfiniteSeq μ i)) ^
      ((1 : ℝ) / 2) ∂ν ≤ ∫⁻ l, (∫⁻ x, (g l x) ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) ∂ν :=
    fun n => lintegral_mono fun l => ENNReal.rpow_le_rpow (hle (fun x => g l x ^ (2 : ℝ)) n)
      (by norm_num)
  have hmain : ∫⁻ x, (∫⁻ l, g l x ∂ν) ^ (2 : ℝ) ∂μ ≤
      ((∫⁻ l, (∫⁻ x, (g l x) ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) ∂ν) ^ (2 : ℝ)) := by
    refine (hsup (fun x => (∫⁻ l, g l x ∂ν) ^ (2 : ℝ))).le.trans ?_
    refine iSup_le fun n => ?_
    have := hfin n
    exact (minkowskiL2_finite _ ν g hg).trans
      (ENNReal.rpow_le_rpow (hR n) (by norm_num))
  calc (∫⁻ x, (∫⁻ l, g l x ∂ν) ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2)
      ≤ ((∫⁻ l, (∫⁻ x, (g l x) ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) ∂ν) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) :=
        ENNReal.rpow_le_rpow hmain (by norm_num)
    _ = ∫⁻ l, (∫⁻ x, (g l x) ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) ∂ν := by
        rw [← ENNReal.rpow_mul]; norm_num

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
