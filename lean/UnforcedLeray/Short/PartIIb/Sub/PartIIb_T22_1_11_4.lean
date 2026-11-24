import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_1_11

/-!


Source: `the November 2 reference manuscript`, lines 2074-2093, 2103-2105.
With `f_t(r) = H_{ν(t-r)}F(r)(x)` and `G_i(r) = ∂_iK_{ν(τ-r)} * ∂_iF(r)(x)` the quotient splits at the
cutoff `c = max s (τ-η)` into an inner part (`∫_s^c`, fixed cutoff, dominated convergence with the
dominator `C B (1 + (a(r)/2)^(-1/2))`, integrable against `(τ-r)^(-1/2)`) and a tail part
(`∫_c^τ`, uniformly small in `t`: the window `|r-τ| ≤ 2|t-τ|/ν` contributes `O(√|t-τ|)`, the rest is
dominated by an integrable majorant of small mass).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.CylPDE

/-- Integrability on `[s, τ]` of the limit integrands `r ↦ ∂_iK_{ν(τ-r)} * ∂_iF(r)(x)`
(bounded by `C B (1 + (ν(τ-r))^(-1/2))`, measurable by `HeatCont`; `Beta.lean`). -/
def ConvTD_Quot_GInt : Prop := ∀ (ν s T : ℝ), 0 < ν → s ≤ T → ∀ (B : ℝ) (F : ℝ → Pl → ℝ),
  FReg s T F → (∀ r ∈ Icc s T, WB B (F r) ∧ ∀ j : Fin 2, WB B (B0579.pd j (F r))) →
    ∀ τ ∈ Icc s T, ∀ x : Pl, ∀ i : Fin 2,
      IntervalIntegrable (fun r : ℝ => heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x) volume s τ

/-- Inner part: for a fixed cutoff `η > 0` the quotient over `[s, max s (τ-η)]` converges
(dominated convergence away from `r = τ`, pointwise limit from `ConvTD_A`). -/
def ConvTD_Quot_Inner : Prop := ∀ (ν s T : ℝ), 0 < ν → s ≤ T → ∀ (B : ℝ) (F : ℝ → Pl → ℝ),
  FReg s T F → (∀ r ∈ Icc s T, WB B (F r) ∧ ∀ j : Fin 2, WB B (B0579.pd j (F r))) →
    ∀ τ ∈ Icc s T, ∀ x : Pl, ∀ η : ℝ, 0 < η →
      Tendsto (fun t : ℝ => (t - τ)⁻¹ * ∫ r in s..max s (τ - η),
          (heatSG (ν * (t - r)) (F r) x - heatSG (ν * (τ - r)) (F r) x))
        (𝓝[Icc s T \ {τ}] τ)
        (𝓝 (ν * ∑ i : Fin 2, ∫ r in s..max s (τ - η),
          heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x))

/-- Tail part: for every `ε > 0` there is a cutoff `η > 0` such that the limit tail is `≤ ε` and the
quotient tail over `[max s (τ-η), τ]` is `≤ ε` for all `t ∈ [s, T]` close to `τ`, `t ≠ τ`
(mean value/`ConvTD_A` bound `C B (1 + b^(-1/2))` outside the window, window estimate
`C B (|h| + 2√|h|)` inside). -/
def ConvTD_Quot_Tail : Prop := ∀ (ν s T : ℝ), 0 < ν → s ≤ T → ∀ (B : ℝ) (F : ℝ → Pl → ℝ),
  FReg s T F → (∀ r ∈ Icc s T, WB B (F r) ∧ ∀ j : Fin 2, WB B (B0579.pd j (F r))) →
    ∀ τ ∈ Icc s T, ∀ x : Pl, ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      |ν * ∑ i : Fin 2, ∫ r in max s (τ - η)..τ,
          heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x| ≤ ε ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Icc s T, t ≠ τ → |t - τ| < δ →
        |(t - τ)⁻¹ * ∫ r in max s (τ - η)..τ,
          (heatSG (ν * (t - r)) (F r) x - heatSG (ν * (τ - r)) (F r) x)| ≤ ε

theorem convTD_Quot_of (hI : ConvTD_Int) (hG : ConvTD_Quot_GInt) (hIn : ConvTD_Quot_Inner)
    (hT : ConvTD_Quot_Tail) : ConvTD_Quot := by
  intro ν s T hν hsT B F hF hb τ hτ x
  have hb0 : ∀ r ∈ Icc s T, WB B (F r) := fun r hr => (hb r hr).1
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨η, hη, hLt, δ, hδ, hQt⟩ := hT ν s T hν hsT B F hF hb τ hτ x (ε / 3) hε3
  have hsc : s ≤ max s (τ - η) := le_max_left _ _
  have hcτ : max s (τ - η) ≤ τ := max_le hτ.1 (by linarith)
  have hin := Metric.tendsto_nhds.1 (hIn ν s T hν hsT B F hF hb τ hτ x η hη) (ε / 3) hε3
  have hsub : ∀ {a b : ℝ}, a ∈ Icc s T → b ∈ Icc s T →
      Set.uIcc a b ⊆ Set.uIcc s T := by
    intro a b ha hb' ; rw [Set.uIcc_of_le hsT]
    exact Set.uIcc_subset_Icc ha hb'
  filter_upwards [hin, self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds τ hδ)] with t hdist ht hball
  have htI : t ∈ Icc s T := ht.1
  have htne : t ≠ τ := ht.2
  have hball' : |t - τ| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using hball
  have hsI : s ∈ Icc s T := ⟨le_refl _, hsT⟩
  have hint : IntervalIntegrable
      (fun r : ℝ => heatSG (ν * (t - r)) (F r) x - heatSG (ν * (τ - r)) (F r) x) volume s τ :=
    ((hI ν s T hν hsT B F hF hb0 t htI x).sub (hI ν s T hν hsT B F hF hb0 τ hτ x)).mono_set
      (hsub hsI hτ)
  have hcI : max s (τ - η) ∈ Icc s T := ⟨hsc, hcτ.trans hτ.2⟩
  have h1 := hint.mono_set (Set.uIcc_subset_uIcc_left
    (Set.mem_uIcc_of_le hsc hcτ) : Set.uIcc s (max s (τ - η)) ⊆ Set.uIcc s τ)
  have h2 := hint.mono_set (Set.uIcc_subset_uIcc_right
    (Set.mem_uIcc_of_le hsc hcτ) : Set.uIcc (max s (τ - η)) τ ⊆ Set.uIcc s τ)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h1 h2
  have hGsplit : ∀ i : Fin 2,
      ∫ r in s..τ, heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x =
      (∫ r in s..max s (τ - η), heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x) +
      ∫ r in max s (τ - η)..τ, heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x := by
    intro i
    have hg := hG ν s T hν hsT B F hF hb τ hτ x i
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hg.mono_set (Set.uIcc_subset_uIcc_left (Set.mem_uIcc_of_le hsc hcτ)))
      (hg.mono_set (Set.uIcc_subset_uIcc_right (Set.mem_uIcc_of_le hsc hcτ)))).symm
  have hQ := hQt t htI htne hball'
  rw [Real.dist_eq] at hdist ⊢
  simp only [hGsplit, Finset.sum_add_distrib, mul_add] at hLt ⊢
  rw [← hsplit, mul_add]
  set Qi := (t - τ)⁻¹ * ∫ r in s..max s (τ - η),
    (heatSG (ν * (t - r)) (F r) x - heatSG (ν * (τ - r)) (F r) x)
  set Qt := (t - τ)⁻¹ * ∫ r in max s (τ - η)..τ,
    (heatSG (ν * (t - r)) (F r) x - heatSG (ν * (τ - r)) (F r) x)
  set Li := ν * ∑ i : Fin 2, ∫ r in s..max s (τ - η),
    heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x
  set Lt := ν * ∑ i : Fin 2, ∫ r in max s (τ - η)..τ,
    heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x
  have e : Qi + Qt - (Li + Lt) = (Qi - Li) + Qt - Lt := by ring
  rw [e]
  calc |(Qi - Li) + Qt - Lt| ≤ |Qi - Li| + |Qt| + |Lt| := by
        have := abs_add_three (Qi - Li) Qt (-Lt)
        simpa [sub_eq_add_neg, abs_neg] using this
    _ < ε := by linarith
