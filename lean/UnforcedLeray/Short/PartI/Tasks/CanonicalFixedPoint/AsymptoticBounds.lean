import UnforcedLeray.Short.PartI.Sub.PartI_C06

/-!
# Part I, task `PartI:C06/9`: the canonical asymptotic bounds

Source of record: `the November 2 reference manuscript`, eq.
`short-canonical-asymptotic` (lines 1082-1085) and the normalized solutions (lines 1119-1121).

Proof outline. Write `W θ = canonicalW lam κ V θ`. Given `‖W θ - q‖ ≤ C/θ` for `θ ≥ b₀`:
* boundedness: on `[b, max b b₀]` by compactness and continuity; beyond, `‖W‖ ≤ ‖q‖ + |C|/b₀`;
* `W - ℓ(W)q = (W - q) - ℓ(W - q)q` (as `ℓ q = 1`), so `‖W - ℓ(W)q‖ ≤ (1 + ‖ℓ‖‖q‖)‖W - q‖`;
* `|ℓ(W) - 1| = |ℓ(W - q)| ≤ ‖ℓ‖ |C|/θ`, which tends to zero.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

theorem canonicalAsymptoticBounds : CanonicalAsymptoticBounds := by
  unfold CanonicalAsymptoticBounds
  intro lam κ q l hl b V hb hV hAs
  obtain ⟨C, b0, hb0, hasy⟩ := hAs
  -- tail estimate: `‖W θ - q‖ ≤ |C|/θ` for `θ ≥ b₀`
  have hWq : ∀ θ : ℝ, b0 ≤ θ → ‖canonicalW lam κ V θ - q‖ ≤ |C| / θ := by
    intro θ hθb
    have hθ : 0 < θ := lt_of_lt_of_le hb0 hθb
    have h := hasy θ hθb
    have hC : C / θ ≤ |C| / θ := div_le_div_of_nonneg_right (le_abs_self C) hθ.le
    exact le_trans h hC
  -- compact part
  have hb1 : b ≤ max b b0 := le_max_left _ _
  have hcont : ContinuousOn (canonicalW lam κ V) (Icc b (max b b0)) :=
    (continuousOn_canonicalW hb lam κ hV).mono Icc_subset_Ici_self
  obtain ⟨M0, hM0⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hcont
  have hC0 : 0 ≤ |C| / b0 := div_nonneg (abs_nonneg C) hb0.le
  set M : ℝ := |M0| + ‖q‖ + |C| / b0 with hMdef
  have hM : 0 ≤ M := by
    have := abs_nonneg M0
    have := norm_nonneg q
    linarith
  -- uniform bound on `[b, ∞)`
  have hWbound : ∀ θ : ℝ, b ≤ θ → ‖canonicalW lam κ V θ‖ ≤ M := by
    intro θ hbθ
    by_cases hθ : θ ≤ max b b0
    · have h := hM0 θ ⟨hbθ, hθ⟩
      have := le_abs_self M0
      have := abs_nonneg M0
      have := norm_nonneg q
      have := hC0
      rw [hMdef]
      linarith
    · have hθb0 : b0 ≤ θ := by
        have : max b b0 < θ := lt_of_not_ge hθ
        exact le_trans (le_max_right _ _) this.le
      have hθpos : 0 < θ := lt_of_lt_of_le hb0 hθb0
      have hdiv : |C| / θ ≤ |C| / b0 :=
        div_le_div_of_nonneg_left (abs_nonneg C) hb0 hθb0
      have htri : ‖canonicalW lam κ V θ‖ ≤ ‖canonicalW lam κ V θ - q‖ + ‖q‖ := by
        calc ‖canonicalW lam κ V θ‖
            = ‖(canonicalW lam κ V θ - q) + q‖ := by rw [sub_add_cancel]
          _ ≤ ‖canonicalW lam κ V θ - q‖ + ‖q‖ := norm_add_le _ _
      have h1 := hWq θ hθb0
      have h2 : |M0| ≥ 0 := abs_nonneg M0
      rw [hMdef]
      linarith
  -- the normalized remainder: identity plus estimate, valid for all θ
  have hkey : ∀ θ : ℝ,
      ‖canonicalW lam κ V θ - l (canonicalW lam κ V θ) • q‖
        ≤ (1 + ‖l‖ * ‖q‖) * ‖canonicalW lam κ V θ - q‖ := by
    intro θ
    have e : canonicalW lam κ V θ - l (canonicalW lam κ V θ) • q
        = (canonicalW lam κ V θ - q) - l (canonicalW lam κ V θ - q) • q := by
      rw [map_sub, hl, sub_smul, one_smul]
      abel
    rw [e]
    have h1 : ‖l (canonicalW lam κ V θ - q)‖ ≤ ‖l‖ * ‖canonicalW lam κ V θ - q‖ :=
      l.le_opNorm _
    calc ‖(canonicalW lam κ V θ - q) - l (canonicalW lam κ V θ - q) • q‖
        ≤ ‖canonicalW lam κ V θ - q‖ + ‖l (canonicalW lam κ V θ - q) • q‖ := norm_sub_le _ _
      _ = ‖canonicalW lam κ V θ - q‖ + ‖l (canonicalW lam κ V θ - q)‖ * ‖q‖ := by
          rw [norm_smul]
      _ ≤ ‖canonicalW lam κ V θ - q‖ + (‖l‖ * ‖canonicalW lam κ V θ - q‖) * ‖q‖ := by
          gcongr
      _ = (1 + ‖l‖ * ‖q‖) * ‖canonicalW lam κ V θ - q‖ := by ring
  -- constants for the second bound
  have hL : 0 ≤ 1 + ‖l‖ * ‖q‖ := by
    have := norm_nonneg l
    have := norm_nonneg q
    positivity
  set N0 : ℝ := (1 + ‖l‖ * ‖q‖) * (M + ‖q‖) with hN0def
  have hN0 : 0 ≤ N0 := by
    have := norm_nonneg q
    rw [hN0def]
    exact mul_nonneg hL (by linarith)
  set b1 : ℝ := max b b0 with hb1def
  have hb1pos : 0 < b1 := lt_of_lt_of_le hb0 (le_max_right _ _)
  set K : ℝ := N0 * b1 + (1 + ‖l‖ * ‖q‖) * |C| with hKdef
  have hK0 : 0 ≤ (1 + ‖l‖ * ‖q‖) * |C| := mul_nonneg hL (abs_nonneg C)
  have hN0b1 : 0 ≤ N0 * b1 := mul_nonneg hN0 hb1pos.le
  have hboundK : ∀ θ : ℝ, b ≤ θ →
      ‖canonicalW lam κ V θ - l (canonicalW lam κ V θ) • q‖ ≤ K / θ := by
    intro θ hbθ
    by_cases hθ : θ ≤ b1
    · have hθpos : 0 < θ := lt_of_lt_of_le hb (le_trans hbθ le_rfl)
      have hnorm : ‖canonicalW lam κ V θ - q‖ ≤ M + ‖q‖ := by
        have htri : ‖canonicalW lam κ V θ - q‖ ≤ ‖canonicalW lam κ V θ‖ + ‖q‖ :=
          norm_sub_le _ _
        linarith [hWbound θ hbθ]
      have hN : ‖canonicalW lam κ V θ - l (canonicalW lam κ V θ) • q‖ ≤ N0 := by
        calc ‖canonicalW lam κ V θ - l (canonicalW lam κ V θ) • q‖
            ≤ (1 + ‖l‖ * ‖q‖) * ‖canonicalW lam κ V θ - q‖ := hkey θ
          _ ≤ (1 + ‖l‖ * ‖q‖) * (M + ‖q‖) :=
              mul_le_mul_of_nonneg_left hnorm hL
      rw [le_div_iff₀ hθpos]
      have e1 : ‖canonicalW lam κ V θ - l (canonicalW lam κ V θ) • q‖ * θ ≤ N0 * θ :=
        mul_le_mul_of_nonneg_right hN hθpos.le
      have e2 : N0 * θ ≤ N0 * b1 := mul_le_mul_of_nonneg_left hθ hN0
      linarith
    · have hθb0 : b0 ≤ θ := by
        have : b1 < θ := lt_of_not_ge hθ
        exact le_trans (le_max_right _ _) this.le
      have hθpos : 0 < θ := lt_of_lt_of_le hb0 hθb0
      have hθ' : ‖canonicalW lam κ V θ - q‖ * θ ≤ |C| :=
        (le_div_iff₀ hθpos).mp (hWq θ hθb0)
      rw [le_div_iff₀ hθpos]
      have e1 : ‖canonicalW lam κ V θ - l (canonicalW lam κ V θ) • q‖ * θ
          ≤ (1 + ‖l‖ * ‖q‖) * ‖canonicalW lam κ V θ - q‖ * θ :=
        mul_le_mul_of_nonneg_right (hkey θ) hθpos.le
      have e2 : (1 + ‖l‖ * ‖q‖) * ‖canonicalW lam κ V θ - q‖ * θ
          ≤ (1 + ‖l‖ * ‖q‖) * |C| := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hθ' hL
      linarith
  -- limit of `ℓ(W)`
  have hlim : Tendsto (fun θ : ℝ => ‖l (canonicalW lam κ V θ) - 1‖) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun θ : ℝ => ‖l‖ * |C| * θ⁻¹)
    · exact Eventually.of_forall (fun θ => norm_nonneg _)
    · filter_upwards [eventually_ge_atTop (max b b0)] with θ hθ
      have hθb0 : b0 ≤ θ := le_trans (le_max_right _ _) hθ
      have hθpos : 0 < θ := lt_of_lt_of_le hb0 hθb0
      have e : l (canonicalW lam κ V θ) - 1 = l (canonicalW lam κ V θ - q) := by
        rw [map_sub, hl]
      rw [e]
      calc ‖l (canonicalW lam κ V θ - q)‖
          ≤ ‖l‖ * ‖canonicalW lam κ V θ - q‖ := l.le_opNorm _
        _ ≤ ‖l‖ * (|C| / θ) := mul_le_mul_of_nonneg_left (hWq θ hθb0) (norm_nonneg _)
        _ = ‖l‖ * |C| * θ⁻¹ := by ring
    · simpa using (tendsto_inv_atTop_zero.const_mul (‖l‖ * |C|))
  refine ⟨⟨M, hWbound⟩, ⟨K, hboundK⟩, ?_⟩
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hlim

end UnforcedLeray.Short.PartI
