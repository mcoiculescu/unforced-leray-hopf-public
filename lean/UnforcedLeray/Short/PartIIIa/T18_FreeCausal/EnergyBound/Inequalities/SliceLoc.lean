import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_3_2

/-!
# Part III-a, task `PartIII-a:T18/3/2/3` (sliceLoc): Tonelli slices on a cell

Source: `the November 2 reference manuscript` lines 3541-3552.
For `c > 0` and a measurable `g ≥ 0` with finite `∫⁻` over every `[s₁,s₂] × cell c` (`0 < s₁`):
the slice integral `s ↦ ∫_cell g(s,·)` is measurable, integrable on every `[s₁,s₂]`, and a.e. `s > 0`
the slice `g(s,·)` is integrable on the cell.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Product set integral as an iterated integral (`Measure.prod_restrict`, `lintegral_prod`). -/
theorem lintegral_restrict_prod_eq (I : Set ℝ) (T : Set (ℝ × ℝ)) (f : ℝ × (ℝ × ℝ) → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ p in I ×ˢ T, f p = ∫⁻ s in I, ∫⁻ x in T, f (s, x) := by
  rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), ← Measure.prod_restrict,
    lintegral_prod f hf.aemeasurable]

theorem sliceLoc : UnforcedLeray.Short.IIIa.SliceLoc := by
  intro c g hc hg hg0 hfin
  set L : ℝ → ℝ≥0∞ := fun s => ∫⁻ x in B0579.cell c, ENNReal.ofReal (g (s, x)) with hL
  have hf : Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (g p) := hg.ennreal_ofReal
  have hLm : Measurable L :=
    Measurable.lintegral_prod_right' (f := fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (g p)) hf
  -- the real slice integral equals the `toReal` of the lintegral slice
  have hsl : ∀ s, sliceSq c g s = (L s).toReal := by
    intro s
    unfold sliceSq
    rw [hL]
    exact integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => hg0 (s, x))
      (hg.comp measurable_prodMk_left).aestronglyMeasurable
  have hmeas : Measurable (sliceSq c g) := by
    have h := (StronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (B0579.cell c)) hg.stronglyMeasurable).measurable
    exact h
  -- finiteness of the lintegral slice on each compact age interval
  have hLfin : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → ∫⁻ s in Icc s₁ s₂, L s < ⊤ := by
    intro s₁ s₂ h1 h2
    exact (lintegral_restrict_prod_eq (Icc s₁ s₂) (B0579.cell c) _ hf).symm.trans_lt
      (hfin s₁ s₂ h1 h2)
  have hLae : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → ∀ᵐ s ∂(volume.restrict (Icc s₁ s₂)), L s < ⊤ :=
    fun s₁ s₂ h1 h2 => ae_lt_top hLm (hLfin s₁ s₂ h1 h2).ne
  refine ⟨hmeas, ?_, ?_⟩
  · -- integrability of the slice integral on compact age intervals
    intro s₁ s₂ h1 h2
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt (lintegral_mono fun s => ?_) (hLfin s₁ s₂ h1 h2)
    rw [Real.enorm_eq_ofReal (sliceSq_nonneg hg0 s), hsl s]
    exact ENNReal.ofReal_toReal_le
  · -- a.e. slice integrability on the cell, via a countable cover of `Ioi 0`
    let S : ℕ → Set ℝ := fun n => Icc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2)
    have hcover : Ioi (0 : ℝ) ⊆ ⋃ n : ℕ, S n := by
      intro s hs
      have hs' : 0 < s := hs
      refine mem_iUnion.2 ⟨⌈s⌉₊ + ⌈1 / s⌉₊, ?_, ?_⟩
      · have hN : ((⌈s⌉₊ + ⌈1 / s⌉₊ : ℕ) : ℝ) = (⌈s⌉₊ : ℝ) + (⌈1 / s⌉₊ : ℝ) := by push_cast; ring
        have h1 : s ≤ (⌈s⌉₊ : ℝ) := Nat.le_ceil s
        have h2 : 1 / s ≤ (⌈1 / s⌉₊ : ℝ) := Nat.le_ceil _
        have h3 : (0 : ℝ) ≤ (⌈1 / s⌉₊ : ℝ) := Nat.cast_nonneg _
        have h4 : 1 / s ≤ ((⌈s⌉₊ + ⌈1 / s⌉₊ : ℕ) : ℝ) + 2 := by rw [hN]; linarith
        have h5 : 1 ≤ (((⌈s⌉₊ + ⌈1 / s⌉₊ : ℕ) : ℝ) + 2) * s := (div_le_iff₀ hs').1 h4
        show 1 / (((⌈s⌉₊ + ⌈1 / s⌉₊ : ℕ) : ℝ) + 2) ≤ s
        rw [div_le_iff₀ (by positivity)]
        linarith [mul_comm s (((⌈s⌉₊ + ⌈1 / s⌉₊ : ℕ) : ℝ) + 2)]
      · have hN : ((⌈s⌉₊ + ⌈1 / s⌉₊ : ℕ) : ℝ) = (⌈s⌉₊ : ℝ) + (⌈1 / s⌉₊ : ℝ) := by push_cast; ring
        have h1 : s ≤ (⌈s⌉₊ : ℝ) := Nat.le_ceil s
        have h3 : (0 : ℝ) ≤ (⌈1 / s⌉₊ : ℝ) := Nat.cast_nonneg _
        show s ≤ ((⌈s⌉₊ + ⌈1 / s⌉₊ : ℕ) : ℝ) + 2
        rw [hN]; linarith
    have hae : ∀ n : ℕ, ∀ᵐ s ∂(volume.restrict (S n)), L s < ⊤ := by
      intro n
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hlt : 1 / ((n : ℝ) + 2) < (n : ℝ) + 2 := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
      exact hLae _ _ (by positivity) hlt
    have hall : ∀ᵐ s ∂(volume.restrict (⋃ n : ℕ, S n)), L s < ⊤ :=
      (ae_restrict_iUnion_iff _ _).2 hae
    have hpos : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), L s < ⊤ :=
      ae_restrict_of_ae_restrict_of_subset hcover hall
    filter_upwards [hpos] with s hs
    refine ⟨(hg.comp measurable_prodMk_left).aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt (le_of_eq ?_) hs
    exact lintegral_congr fun x => Real.enorm_eq_ofReal (hg0 (s, x))

end UnforcedLeray.Short.IIIa
