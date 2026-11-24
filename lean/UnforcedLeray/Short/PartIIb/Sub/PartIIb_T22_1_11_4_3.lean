import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_1_11_4

/-!


Source: `the November 2 reference manuscript`, lines 2074-2093, 2103-2105.
Write `a = max s (τ-η)` and `b(t) = max a (τ - 2|t-τ|/ν)`.  The tail `∫_a^τ` of the quotient splits at
`b(t)`: the window `[b, τ]` (length `O(|t-τ|)`) contributes `O(√|t-τ|)`, the outside `[a, b]` is
dominated by an integrable majorant of small mass; the limit tail is small by
`C B (1 + (ν(τ-r))^(-1/2))`-integrability.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.CylPDE

/-- Limit tail, source 2074-2093: `|ν ∑_i ∫_{max s (τ-η)}^τ ∂_iK_{ν(τ-r)} * ∂_iF(r)(x) dr| ≤ ε` for
all small `η` (integrand `≤ C B (1 + (ν(τ-r))^(-1/2))`, integrable). -/
def ConvTD_Tail_Lim : Prop := ∀ (ν s T : ℝ), 0 < ν → s ≤ T → ∀ (B : ℝ) (F : ℝ → Pl → ℝ),
  FReg s T F → (∀ r ∈ Icc s T, WB B (F r) ∧ ∀ j : Fin 2, WB B (B0579.pd j (F r))) →
    ∀ τ ∈ Icc s T, ∀ x : Pl, ∀ ε : ℝ, 0 < ε → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      |ν * ∑ i : Fin 2, ∫ r in max s (τ - η)..τ,
          heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x| ≤ ε

/-- Window estimate, source 2103-2105: for `r` within `2|t-τ|/ν` of `τ`,
`|H_{a+h'}F-H_aF| ≤ C B (|h'|+2√|h'|)`, so the window contributes `≤ C √|t-τ|` (for `t < τ`,
`heatSG` at nonpositive age is the identity; continuity at age `0` by `HeatCont`). -/
def ConvTD_Tail_Window : Prop := ∀ (ν s T : ℝ), 0 < ν → s ≤ T → ∀ (B : ℝ) (F : ℝ → Pl → ℝ),
  FReg s T F → (∀ r ∈ Icc s T, WB B (F r) ∧ ∀ j : Fin 2, WB B (B0579.pd j (F r))) →
    ∀ τ ∈ Icc s T, ∀ x : Pl, ∃ C δ : ℝ, 0 < δ ∧ ∀ η : ℝ, 0 < η → ∀ t ∈ Icc s T, t ≠ τ →
      |t - τ| < δ →
      |(t - τ)⁻¹ * ∫ r in max (max s (τ - η)) (τ - 2 * |t - τ| / ν)..τ,
          (heatSG (ν * (t - r)) (F r) x - heatSG (ν * (τ - r)) (F r) x)| ≤ C * Real.sqrt |t - τ|

/-- Outside estimate, source 2074-2093: on `r ≤ τ - 2|t-τ|/ν` both ages `ν(t-r), ν(τ-r)` are
`≥ ν(τ-r)/2`, the mean value theorem with `ConvTD_A` gives
`|difference|/|h| ≤ ν C B (1 + (ν(τ-r)/2)^(-1/2))`, integrable of small mass on `(τ-η, τ)`,
uniformly in `t`. -/
def ConvTD_Tail_Outside : Prop := ∀ (ν s T : ℝ), 0 < ν → s ≤ T → ∀ (B : ℝ) (F : ℝ → Pl → ℝ),
  FReg s T F → (∀ r ∈ Icc s T, WB B (F r) ∧ ∀ j : Fin 2, WB B (B0579.pd j (F r))) →
    ∀ τ ∈ Icc s T, ∀ x : Pl, ∀ ε : ℝ, 0 < ε → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ t ∈ Icc s T, t ≠ τ →
      |(t - τ)⁻¹ * ∫ r in max s (τ - η)..max (max s (τ - η)) (τ - 2 * |t - τ| / ν),
          (heatSG (ν * (t - r)) (F r) x - heatSG (ν * (τ - r)) (F r) x)| ≤ ε

theorem convTD_Quot_tail_of (hI : ConvTD_Int) (hL : ConvTD_Tail_Lim) (hW : ConvTD_Tail_Window)
    (hO : ConvTD_Tail_Outside) : ConvTD_Quot_Tail := by
  intro ν s T hν hsT B F hF hb τ hτ x ε hε
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨η₁, hη₁, hL1⟩ := hL ν s T hν hsT B F hF hb τ hτ x ε hε
  obtain ⟨η₂, hη₂, hO2⟩ := hO ν s T hν hsT B F hF hb τ hτ x (ε / 2) hε2
  obtain ⟨C, δ, hδ, hW1⟩ := hW ν s T hν hsT B F hF hb τ hτ x
  set η := min η₁ η₂ with hηdef
  have hη : 0 < η := lt_min hη₁ hη₂
  refine ⟨η, hη, hL1 η hη (min_le_left _ _), ?_⟩
  -- choose δ' so that C * sqrt δ' ≤ ε/2
  set δ' := min δ (((ε / 2) / (|C| + 1)) ^ 2) with hδ'
  have hpos : 0 < ((ε / 2) / (|C| + 1)) ^ 2 := by positivity
  refine ⟨δ', lt_min hδ hpos, ?_⟩
  intro t ht htne htd
  have hb0 : ∀ r ∈ Icc s T, WB B (F r) := fun r hr => (hb r hr).1
  set a := max s (τ - η) with ha
  set b := max a (τ - 2 * |t - τ| / ν) with hbdef
  have hsa : s ≤ a := le_max_left _ _
  have hab : a ≤ b := le_max_left _ _
  have haτ : a ≤ τ := max_le hτ.1 (by linarith)
  have hbτ : b ≤ τ := by
    refine max_le haτ ?_
    have : 0 ≤ 2 * |t - τ| / ν := by positivity
    linarith
  have hsub : ∀ {p q : ℝ}, p ∈ Icc s T → q ∈ Icc s T → Set.uIcc p q ⊆ Set.uIcc s T := by
    intro p q hp hq; rw [Set.uIcc_of_le hsT]; exact Set.uIcc_subset_Icc hp hq
  have hsI : s ∈ Icc s T := ⟨le_refl _, hsT⟩
  have hint : IntervalIntegrable
      (fun r : ℝ => heatSG (ν * (t - r)) (F r) x - heatSG (ν * (τ - r)) (F r) x) volume s τ :=
    ((hI ν s T hν hsT B F hF hb0 t ht x).sub (hI ν s T hν hsT B F hF hb0 τ hτ x)).mono_set
      (hsub hsI hτ)
  have hsτ : s ≤ τ := hτ.1
  have h1 : IntervalIntegrable
      (fun r : ℝ => heatSG (ν * (t - r)) (F r) x - heatSG (ν * (τ - r)) (F r) x) volume a b :=
    hint.mono_set (by
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le hsτ]; exact Set.Icc_subset_Icc hsa hbτ)
  have h2 : IntervalIntegrable
      (fun r : ℝ => heatSG (ν * (t - r)) (F r) x - heatSG (ν * (τ - r)) (F r) x) volume b τ :=
    hint.mono_set (by
      rw [Set.uIcc_of_le hbτ, Set.uIcc_of_le hsτ]
      exact Set.Icc_subset_Icc (hsa.trans hab) le_rfl)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h1 h2
  have hηle : η ≤ η₂ := min_le_right _ _
  have hA := hO2 η hη hηle t ht htne
  have hBw := hW1 η hη t ht htne (lt_of_lt_of_le htd (min_le_left _ _))
  have hsq : Real.sqrt |t - τ| ≤ (ε / 2) / (|C| + 1) := by
    rw [Real.sqrt_le_left (by positivity)]
    exact (htd.le).trans (min_le_right _ _)
  have hC : C * Real.sqrt |t - τ| ≤ ε / 2 := by
    have h0 : 0 ≤ Real.sqrt |t - τ| := Real.sqrt_nonneg _
    calc C * Real.sqrt |t - τ| ≤ |C| * ((ε / 2) / (|C| + 1)) :=
          mul_le_mul (le_abs_self C) hsq h0 (abs_nonneg C)
      _ ≤ ε / 2 := by
          rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
          nlinarith [abs_nonneg C]
  rw [← hsplit, mul_add]
  calc _ ≤ |(t - τ)⁻¹ * ∫ r in a..b, (heatSG (ν * (t - r)) (F r) x - heatSG (ν * (τ - r)) (F r) x)|
        + |(t - τ)⁻¹ * ∫ r in b..τ, (heatSG (ν * (t - r)) (F r) x - heatSG (ν * (τ - r)) (F r) x)| :=
        abs_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hA (hBw.trans hC)
    _ = ε := by ring

end UnforcedLeray.Short.IIb.CylPDE
