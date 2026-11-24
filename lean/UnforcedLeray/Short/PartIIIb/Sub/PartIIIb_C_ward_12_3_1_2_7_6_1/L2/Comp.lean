import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_6_1.L2.Jets

/-!
# Composite jets `b ∘ chart` of order `1, 2` with the `ϱ⁻¹` scaling

Source `the November 2 reference manuscript`
lines 2360-2366, 2385-2387 (Faà di Bruno, `norm_iteratedFDerivWithin_comp_le` on `axisᶜ`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray

theorem comp_jet {R : ℝ} (hR : 0 < R) : ∃ a : ℝ, 1 ≤ a ∧ ∀ (τ : ℝ) (b : ℝ × (ℝ × ℝ) → Axi.Merid),
    ContDiff ℝ ∞ b → ∀ (y : Space), y ∉ Axi.axis → ∀ Cm : ℝ,
    (∀ i ≤ 2, ‖iteratedFDeriv ℝ i b (Axi.chart R τ y)‖ ≤ Cm) → ∀ n : ℕ, 1 ≤ n → n ≤ 2 →
      ‖iteratedFDeriv ℝ n (fun z => b (Axi.chart R τ z)) y‖ ≤
        (n.factorial : ℝ) * Cm * (a * (Axi.ϱ y)⁻¹ * (1 + Axi.age R y + |Axi.trans R y|)) ^ n := by
  obtain ⟨a1, ha1, h1⟩ := chart_jet hR 1 le_rfl
  obtain ⟨a2, ha2, h2⟩ := chart_jet hR 2 (by norm_num)
  refine ⟨1 + a1 + a2, by linarith, ?_⟩
  intro τ b hb y hy Cm hCm n hn1 hn2
  have hopen : IsOpen (Axi.axisᶜ : Set Space) := Axi.isOpen_compl_axis
  have hx : y ∈ (Axi.axisᶜ : Set Space) := hy
  have hchart : ContDiffOn ℝ ∞ (Axi.chart R τ) Axi.axisᶜ :=
    IIb.ChartJetsAux.contDiffOn_chart hR.ne' τ
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (Axi.ϱ y)⁻¹ := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; exact inv_nonneg.2 (Axi.ϱ_nonneg y)
  have hs : Axi.age R y = R ^ 2 * t ^ 2 := by rw [age_eq_sq, ht]
  have hs0 : 0 ≤ Axi.age R y := by rw [hs]; positivity
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = 1 + Axi.age R y + |Axi.trans R y| := ⟨_, rfl⟩
  have hW1 : 1 ≤ W := by rw [hW]; linarith [abs_nonneg (Axi.trans R y)]
  set a : ℝ := 1 + a1 + a2 with ha
  have ha1' : 1 ≤ a := by rw [ha]; linarith
  rw [← ht, ← hW]
  have hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDerivWithin ℝ i (Axi.chart R τ) Axi.axisᶜ y‖
      ≤ (a * t * W) ^ i := by
    intro i hi1 hin
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) i hopen hx]
    have hi2 : i ≤ 2 := hin.trans hn2
    have hb1 : ‖iteratedFDeriv ℝ i (Axi.chart R τ) y‖ ≤ a * t ^ i * W := by
      have hle : ∀ ai : ℝ, ai ≤ a → ‖iteratedFDeriv ℝ i (Axi.chart R τ) y‖ ≤ ai * t ^ i * W →
          ‖iteratedFDeriv ℝ i (Axi.chart R τ) y‖ ≤ a * t ^ i * W := by
        intro ai hai h
        refine h.trans ?_
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hai (pow_nonneg ht0 i))
          (by linarith)
      interval_cases i
      · refine hle a1 (by rw [ha]; linarith) ?_
        have := h1 τ y hy
        rw [← ht, ← hW] at this
        simpa using this
      · refine hle a2 (by rw [ha]; linarith) ?_
        have := h2 τ y hy
        rw [← ht, ← hW] at this
        simpa using this
    refine hb1.trans ?_
    calc a * t ^ i * W ≤ a ^ i * t ^ i * W ^ i := by
          refine mul_le_mul (mul_le_mul (le_self_pow₀ ha1' (by omega)) le_rfl (pow_nonneg ht0 i)
            (by positivity)) (le_self_pow₀ hW1 (by omega)) (by linarith) (by positivity)
      _ = (a * t * W) ^ i := by ring
  have hbound0 : ∀ i, i ≤ n → ‖iteratedFDerivWithin ℝ i b univ (Axi.chart R τ y)‖ ≤ Cm := by
    intro i hi
    rw [iteratedFDerivWithin_univ]
    exact hCm i (hi.trans hn2)
  have key := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (g := b) (f := Axi.chart R τ)
    (n := n) (s := Axi.axisᶜ) (t := univ) (x := y) (N := ∞)
    hb.contDiffOn hchart (by exact_mod_cast le_top) uniqueDiffOn_univ hopen.uniqueDiffOn
    (mapsTo_univ _ _) hx hbound0 hD
  have e : iteratedFDeriv ℝ n (fun z => b (Axi.chart R τ z)) y =
      iteratedFDerivWithin ℝ n (b ∘ Axi.chart R τ) Axi.axisᶜ y :=
    (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) n hopen hx).symm
  rw [e]
  exact key

end UnforcedLeray.Short.PartIIIb.Concrete
