import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.CausalLimitAE.SliceClauses.Pairing

/-!
# Part III-a, task `PartIII-a:T18/2/1`: good ages and the slice clauses at one age

Helpers for `UnforcedLeray.Short.IIIa.CausalSliceClauses` (`Sub/T18_2_1.lean`), source of record
`the November 2 reference manuscript`, lines 3427-3440.

* `sc_good_ages`: for almost every `s > 0` every energy slice `∫_cell φₙ(s, ·)` is finite (Tonelli
  on `Icc a b × cell`, countable intersection over `n` and the intervals `Icc (1/(k+1)) (k+2)`).
* `sc_at_age`: at such an age, with `L²(cell)` slices converging, `divFree` and `weakGrad` pass to
  the limit (`sc_tendsto_integral_mul`, `Pairing.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- For almost every `s > 0`, every energy slice on the cell is finite (Tonelli). -/
theorem sc_good_ages (c : ℝ) {φ : ℕ → ℝ × (ℝ × ℝ) → ℝ≥0∞} (hφm : ∀ n, Measurable (φ n))
    (hφ : ∀ n, ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, φ n p < ⊤) :
    ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ n, ∫⁻ x in B0579.cell c, φ n (s, x) < ⊤ := by
  have step1 : ∀ n (a b : ℝ), 0 < a → a < b →
      ∀ᵐ s ∂(volume.restrict (Icc a b)), ∫⁻ x in B0579.cell c, φ n (s, x) < ⊤ := by
    intro n a b ha hab
    have hvol : (volume : Measure (ℝ × (ℝ × ℝ))) =
        (volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)) :=
      Measure.volume_eq_prod _ _
    have hprod : ∫⁻ p in Icc a b ×ˢ B0579.cell c, φ n p =
        ∫⁻ s in Icc a b, ∫⁻ x in B0579.cell c, φ n (s, x) := by
      rw [hvol, ← Measure.prod_restrict]
      exact lintegral_prod _ (hφm n).aemeasurable
    have hm : Measurable fun s : ℝ => ∫⁻ x in B0579.cell c, φ n (s, x) :=
      (hφm n).lintegral_prod_right'
    have hfin : ∫⁻ s in Icc a b, ∫⁻ x in B0579.cell c, φ n (s, x) ≠ ⊤ := by
      rw [← hprod]
      exact (hφ n a b ha hab).ne
    exact ae_lt_top hm hfin
  have step2 : ∀ᵐ s ∂(volume : Measure ℝ), ∀ n (k : ℕ),
      s ∈ Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 2) → ∫⁻ x in B0579.cell c, φ n (s, x) < ⊤ := by
    refine ae_all_iff.2 fun n => ae_all_iff.2 fun k => ?_
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hlt : 1 / ((k : ℝ) + 1) < (k : ℝ) + 2 := by
      have h1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      linarith
    exact (ae_restrict_iff' measurableSet_Icc).1 (step1 n _ _ hpos hlt)
  filter_upwards [ae_restrict_of_ae (s := Ioi (0 : ℝ)) step2,
    ae_restrict_mem measurableSet_Ioi] with s hs hsI
  have hs0 : 0 < s := hsI
  intro n
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / s + s)
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hinv : 0 ≤ 1 / s := by positivity
  have hdsN : 1 / s ≤ (N : ℝ) := by linarith
  have hsN : s ≤ (N : ℝ) + 2 := by linarith
  have hlow : 1 / ((N : ℝ) + 1) ≤ s := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 1 / s * s = 1 := one_div_mul_cancel hs0.ne'
    nlinarith [mul_le_mul_of_nonneg_right hdsN hs0.le]
  exact hs n N ⟨hlow, hsN⟩

/-- The weak-derivative identity, unpacked from `HasWeakCellDerivC`. -/
theorem sc_weak_id {c : ℝ} {j : Fin 2} {φ g : ℝ × ℝ → ℂ} (h : HasWeakCellDerivC c j φ g) :
    ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, φ x * (B0579.pd j ψ x : ℂ) = -∫ x in B0579.cell c, g x * (ψ x : ℂ) := by
  unfold HasWeakCellDerivC at h
  exact h.2

/-- The two clauses of `CausalSliceClauses` at one age `s`, from `L²(cell)` slices. -/
theorem sc_at_age {c : ℝ} {A : ℕ → (ℝ × ℝ) → Fin 2 → ℂ} {B : (ℝ × ℝ) → Fin 2 → ℂ}
    {GA : ℕ → (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {GB : (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hAm : ∀ n i, Measurable fun x => A n x i) (hBm : ∀ i, Measurable fun x => B x i)
    (hGAm : ∀ n i j, Measurable fun x => GA n x i j) (hGBm : ∀ i j, Measurable fun x => GB x i j)
    (hAL2 : ∀ n, ∫⁻ x in B0579.cell c,
      ENNReal.ofReal (vnorm2 (A n x) ^ 2 + tnorm2 (GA n x) ^ 2) < ⊤)
    (hdiv : ∀ n, ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, (A n x 0 * (B0579.pd 0 ψ x : ℂ) + A n x 1 * (B0579.pd 1 ψ x : ℂ)) = 0)
    (hweak : ∀ n i j, HasWeakCellDerivC c j (fun x => A n x i) (fun x => GA n x i j))
    (hconvB : Tendsto (fun n => ∫⁻ x in B0579.cell c,
      ENNReal.ofReal (vnorm2 (fun i => A n x i - B x i) ^ 2)) atTop (𝓝 0))
    (hconvG : Tendsto (fun n => ∫⁻ x in B0579.cell c,
      ENNReal.ofReal (tnorm2 (fun i j => GA n x i j - GB x i j) ^ 2)) atTop (𝓝 0)) :
    (∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, (B x 0 * (B0579.pd 0 ψ x : ℂ) + B x 1 * (B0579.pd 1 ψ x : ℂ)) = 0) ∧
    ∀ i j, HasWeakCellDerivC c j (fun x => B x i) (fun x => GB x i j) := by
  have hA2 : ∀ n i, ∫⁻ x in B0579.cell c, ENNReal.ofReal (‖A n x i‖ ^ 2) < ⊤ := by
    intro n i
    refine lt_of_le_of_lt (lintegral_mono (fun x => ?_)) (hAL2 n)
    exact ENNReal.ofReal_le_ofReal (le_trans (sc_norm_comp_sq_le (A n x) i)
      (le_add_of_nonneg_right (sq_nonneg _)))
  have hGA2 : ∀ n i j, ∫⁻ x in B0579.cell c, ENNReal.ofReal (‖GA n x i j‖ ^ 2) < ⊤ := by
    intro n i j
    refine lt_of_le_of_lt (lintegral_mono (fun x => ?_)) (hAL2 n)
    exact ENNReal.ofReal_le_ofReal (le_trans (sc_tensor_comp_sq_le (GA n x) i j)
      (le_add_of_nonneg_left (sq_nonneg _)))
  have hconvB' : ∀ i, Tendsto
      (fun n => ∫⁻ x in B0579.cell c, ENNReal.ofReal (‖A n x i - B x i‖ ^ 2)) atTop (𝓝 0) :=
    fun i => sc_vnorm_comp_tendsto (volume.restrict (B0579.cell c))
      (F := fun n x k => A n x k - B x k) hconvB i
  have hconvG' : ∀ i j, Tendsto
      (fun n => ∫⁻ x in B0579.cell c, ENNReal.ofReal (‖GA n x i j - GB x i j‖ ^ 2))
      atTop (𝓝 0) :=
    fun i j => sc_tnorm_comp_tendsto (volume.restrict (B0579.cell c))
      (G := fun n x i j => GA n x i j - GB x i j) hconvG i j
  have hBL2 : ∀ i, ∫⁻ x in B0579.cell c, ENNReal.ofReal (‖B x i‖ ^ 2) < ⊤ := fun i =>
    sc_limit_L2 (A := fun n x => A n x i) (B := fun x => B x i) (fun n => hAm n i)
      (fun n => hA2 n i) (hconvB' i)
  have hGBL2 : ∀ i j, ∫⁻ x in B0579.cell c, ENNReal.ofReal (‖GB x i j‖ ^ 2) < ⊤ := fun i j =>
    sc_limit_L2 (A := fun n x => GA n x i j) (B := fun x => GB x i j) (fun n => hGAm n i j)
      (fun n => hGA2 n i j) (hconvG' i j)
  refine ⟨fun ψ hψ => ?_, fun i j => ?_⟩
  · have hψ0 : B0579.IsCylTest c (B0579.pd 0 ψ) := hψ.pd 0
    have hψ1 : B0579.IsCylTest c (B0579.pd 1 ψ) := hψ.pd 1
    have T0 := sc_tendsto_integral_mul (μ := volume.restrict (B0579.cell c))
      (fn := fun n x => A n x 0) (f0 := fun x => B x 0)
      (w := fun x => (B0579.pd 0 ψ x : ℂ))
      (fun n => hAm n 0) (hBm 0) (sc_cyl_meas hψ0) (fun n => hA2 n 0) (hBL2 0)
      (sc_test_L2 hψ0) (hconvB' 0)
    have T1 := sc_tendsto_integral_mul (μ := volume.restrict (B0579.cell c))
      (fn := fun n x => A n x 1) (f0 := fun x => B x 1)
      (w := fun x => (B0579.pd 1 ψ x : ℂ))
      (fun n => hAm n 1) (hBm 1) (sc_cyl_meas hψ1) (fun n => hA2 n 1) (hBL2 1)
      (sc_test_L2 hψ1) (hconvB' 1)
    have hI : ∀ n, (∫ x in B0579.cell c, A n x 0 * (B0579.pd 0 ψ x : ℂ)) +
        ∫ x in B0579.cell c, A n x 1 * (B0579.pd 1 ψ x : ℂ) = 0 := by
      intro n
      rw [← integral_add (sc_integrable (hAm n 0) (sc_cyl_meas hψ0) (hA2 n 0) (sc_test_L2 hψ0))
        (sc_integrable (hAm n 1) (sc_cyl_meas hψ1) (hA2 n 1) (sc_test_L2 hψ1))]
      exact hdiv n ψ hψ
    have hzero : Tendsto (fun n => (∫ x in B0579.cell c, A n x 0 * (B0579.pd 0 ψ x : ℂ)) +
        ∫ x in B0579.cell c, A n x 1 * (B0579.pd 1 ψ x : ℂ)) atTop (𝓝 0) := by
      simp only [hI]
      exact tendsto_const_nhds
    have hlim := tendsto_nhds_unique (T0.add T1) hzero
    rw [integral_add (sc_integrable (hBm 0) (sc_cyl_meas hψ0) (hBL2 0) (sc_test_L2 hψ0))
      (sc_integrable (hBm 1) (sc_cyl_meas hψ1) (hBL2 1) (sc_test_L2 hψ1))]
    exact hlim
  · unfold HasWeakCellDerivC
    refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
    · exact sc_integrable (hBm i) (sc_cyl_meas (hψ.pd j)) (hBL2 i) (sc_test_L2 (hψ.pd j))
    · exact sc_integrable (hGBm i j) (sc_cyl_meas hψ) (hGBL2 i j) (sc_test_L2 hψ)
    · have T1 := sc_tendsto_integral_mul (μ := volume.restrict (B0579.cell c))
        (fn := fun n x => A n x i) (f0 := fun x => B x i)
        (w := fun x => (B0579.pd j ψ x : ℂ))
        (fun n => hAm n i) (hBm i) (sc_cyl_meas (hψ.pd j)) (fun n => hA2 n i) (hBL2 i)
        (sc_test_L2 (hψ.pd j)) (hconvB' i)
      have T2 := sc_tendsto_integral_mul (μ := volume.restrict (B0579.cell c))
        (fn := fun n x => GA n x i j) (f0 := fun x => GB x i j)
        (w := fun x => (ψ x : ℂ))
        (fun n => hGAm n i j) (hGBm i j) (sc_cyl_meas hψ) (fun n => hGA2 n i j) (hGBL2 i j)
        (sc_test_L2 hψ) (hconvG' i j)
      have hI : ∀ n, (∫ x in B0579.cell c, A n x i * (B0579.pd j ψ x : ℂ)) =
          -∫ x in B0579.cell c, GA n x i j * (ψ x : ℂ) :=
        fun n => sc_weak_id (hweak n i j) ψ hψ
      have hT2 := T2.neg
      have hT1 : Tendsto (fun n => ∫ x in B0579.cell c, A n x i * (B0579.pd j ψ x : ℂ))
          atTop (𝓝 (-∫ x in B0579.cell c, GB x i j * (ψ x : ℂ))) := by
        simp only [hI]
        exact hT2
      exact tendsto_nhds_unique T1 hT1

end UnforcedLeray.Short.IIIa
