import UnforcedLeray.Infra.CompactDuhamel.Strip

/-!
# Compact Duhamel perturbation for all elapsed times

`paper/main.tex`, lines 338-340: "`E(t,s) - S_0(t-s)` is compact", for every `t ≥ s`.

On the strip `s ≤ τ ≤ s + 1` this is `isCompactOperator_stripEvolution_sub`. Beyond the strip
the free evolution must be a semigroup on `[0, ∞)`: the `VolterraData` only bounds `S₀` on
`[0, 1]`, and `D.Compatible` only states the semigroup law for elapsed times in `[0, 1]`. With
`S₀ a S₀ b = S₀ (a + b)` for `a, b ≥ 0`, the evolution law `E(τ,s) = E(τ,s+1) E(s+1,s)` gives

`E(τ,s) - S₀(τ-s) = (E(τ,s+1) - S₀(τ-s-1)) E(s+1,s) + S₀(τ-s-1) (E(s+1,s) - S₀(1))`,

and induction on the number of strips proves `isCompactOperator_evolution_sub`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Real

namespace UnforcedLeray.Infra.CompactDuhamel

open UnforcedLeray.Infra.VolterraEvolution UnforcedLeray.Infra.VolterraEvolution.VolterraData

variable {𝕜 : Type*} [RCLike 𝕜] {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [NormedSpace ℝ X]
  [SMulCommClass ℝ 𝕜 X]

/-- **Compact Duhamel perturbation, global form** (`paper/main.tex`, lines 332-340). Let `X` be a
Hilbert space, `D : VolterraData 𝕜 X Y` compatible (`D.Compatible`), with `S₀` a semigroup on
`[0, ∞)` and `S t ∘ B r : X → X` compact for every `0 < t ≤ 1` and every `r`. Then
`E(τ,s) - S₀(τ - s)` is compact for every `s ≤ τ`. -/
theorem isCompactOperator_evolution_sub (D : VolterraData 𝕜 X Y) (hD : D.Compatible)
    (hS₀ : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (D.S₀ a).comp (D.S₀ b) = D.S₀ (a + b))
    (hK : ∀ t r : ℝ, 0 < t → t ≤ 1 → IsCompactOperator ((D.S t).comp (D.B r)))
    {s τ : ℝ} (hsτ : s ≤ τ) :
    IsCompactOperator (D.evolution τ s - D.S₀ (τ - s)) := by
  have hstrip : ∀ s τ : ℝ, τ ∈ Icc s (s + 1) →
      IsCompactOperator (D.evolution τ s - D.S₀ (τ - s)) := fun s τ hτ => by
    rw [evolution_eq_stripEvolution hD hτ]
    exact isCompactOperator_stripEvolution_sub D hK hτ
  suffices H : ∀ n : ℕ, ∀ s τ : ℝ, s ≤ τ → τ ≤ s + n + 1 →
      IsCompactOperator (D.evolution τ s - D.S₀ (τ - s)) by
    exact H ⌊τ - s⌋₊ s τ hsτ (by have := Nat.lt_floor_add_one (τ - s); linarith)
  intro n
  induction n with
  | zero =>
    intro s τ h1 h2
    exact hstrip s τ ⟨h1, by simpa using h2⟩
  | succ n ih =>
    intro s τ h1 h2
    by_cases h : τ ≤ s + 1
    · exact hstrip s τ ⟨h1, h⟩
    · rw [not_le] at h
      have hK1 := ih (s + 1) τ h.le (by push_cast at h2; linarith)
      have hK2 := hstrip s (s + 1) ⟨by linarith, le_rfl⟩
      have heq : D.evolution τ s - D.S₀ (τ - s) =
          (D.evolution τ (s + 1) - D.S₀ (τ - (s + 1))).comp (D.evolution (s + 1) s) +
            (D.S₀ (τ - (s + 1))).comp (D.evolution (s + 1) s - D.S₀ (s + 1 - s)) := by
        rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
          evolution_comp hD (by linarith) h.le, hS₀ _ _ (by linarith) (by linarith)]
        have : τ - (s + 1) + (s + 1 - s) = τ - s := by ring
        rw [this]
        abel
      rw [heq]
      exact (hK1.comp_clm _).add (hK2.clm_comp _)

end UnforcedLeray.Infra.CompactDuhamel
