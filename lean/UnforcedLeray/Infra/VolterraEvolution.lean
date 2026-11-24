import UnforcedLeray.Infra.VolterraEvolution.StripLaw
import UnforcedLeray.Infra.VolterraEvolution.ShortTime
import UnforcedLeray.Infra.VolterraEvolution.GammaBound

/-!
# Volterra construction of an evolution family with square-root smoothing

Abstract form of the evolution step of `paper/main.tex`, Section `sec:st18-265`
(lines 292-306): "Volterra iteration … constructs a jointly strongly continuous evolution
`E(τ,s)`, periodic in both time arguments. On each strip of bounded elapsed time it is
uniformly bounded … iteration of the strip gives exponential boundedness."

Setting (`VolterraData 𝕜 X Y`, `𝕜 = ℝ` or `ℂ`): Banach spaces `X`, `Y`; a free evolution
`S₀ : ℝ → (X →L X)` bounded and strongly continuous on `[0,1]`; a smoothing family
`S : ℝ → (Y →L X)` with `‖S t‖ ≤ C₀ t^{-1/2}` and strongly continuous on `(0,1]`; a uniformly
bounded, strongly continuous coefficient family `B : ℝ → (X →L Y)`.

Results (with `E = D.evolution`):

* strip (`Strip.lean`): for `s ≤ τ ≤ s + 1`,
  `E(τ,s) x = S₀(τ - s) x + ∫ r in s..τ, S (τ - r) (B r (E(r,s) x))`, `‖E(τ,s)‖ ≤ 2 M₀ e^λ`,
  strong continuity in `τ`, and uniqueness among strongly continuous solutions;
* evolution law `E(τ,r) E(r,s) = E(τ,s)` for all `s ≤ r ≤ τ` (under `D.Compatible`);
* strong continuity of `τ ↦ E(τ,s) x` on `[s, ∞)`;
* exponential bound `‖E(τ,s)‖ ≤ M e^{ω(τ - s)}`;
* periodicity `E(τ + P, s + P) = E(τ,s)` for `P`-periodic `B`;
* uniqueness of the global family (`eq_evolution_of_volterra`);
* short-time comparison `‖E(τ,s) - S₀(τ-s)‖ ≤ C (τ-s)^{1/2}` (`ShortTime.lean`) and the
  iterated Gamma bound for the Picard terms (`GammaBound.lean`).

File layout: `Kernel` (scalar kernel integrals), `Beta` (Beta integral), `Operator`
(`VolterraData`, the Volterra integral), `Strip` (Picard construction, uniqueness),
`StripLaw` (evolution law, periodicity), `Cocycle` (iteration of strips, abstract),
`ShortTime`, `GammaBound`, and this file (the global family).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral Real

namespace UnforcedLeray.Infra.VolterraEvolution

namespace VolterraData

variable {𝕜 : Type*} [RCLike 𝕜] {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [NormedSpace ℝ X] [SMulCommClass ℝ 𝕜 X]
  [CompleteSpace X] (D : VolterraData 𝕜 X Y)

/-- The evolution family `E(τ,s)` for all elapsed times, obtained by iterating unit strips:
`E(τ,s) = E_strip(τ, s+n) E_strip(s+n, s+n-1) ⋯ E_strip(s+1, s)`, `n = ⌊τ - s⌋₊`. -/
def evolution (τ s : ℝ) : X →L[𝕜] X := Cocycle.extend D.stripEvolution τ s

/-- The constant `M = max (2 M₀ e^λ) 1` of the exponential bound. -/
def evolutionBound : ℝ := max D.stripBound 1

/-- On the strip `s ≤ τ ≤ s + 1` the global family is the strip evolution. -/
theorem evolution_eq_stripEvolution {D : VolterraData 𝕜 X Y} (hD : D.Compatible) {s τ : ℝ}
    (hτ : τ ∈ Icc s (s + 1)) : D.evolution τ s = D.stripEvolution τ s :=
  Cocycle.extend_eq_self (localLaw_stripEvolution hD) hτ.1 hτ.2

/-- **Volterra equation** for the global family on every strip `s ≤ τ ≤ s + 1`. -/
theorem evolution_volterra {D : VolterraData 𝕜 X Y} (hD : D.Compatible) {s τ : ℝ}
    (hτ : τ ∈ Icc s (s + 1)) (x : X) :
    D.evolution τ s x =
      D.S₀ (τ - s) x + ∫ r in s..τ, D.S (τ - r) (D.B r (D.evolution r s x)) := by
  rw [evolution_eq_stripEvolution hD hτ, D.stripEvolution_eq hτ x]
  congr 1
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le hτ.1] at hr
  simp only [evolution_eq_stripEvolution hD (⟨hr.1, hr.2.trans hτ.2⟩ : r ∈ Icc s (s + 1))]

/-- **Evolution law.** `E(τ,r) E(r,s) = E(τ,s)` for all `s ≤ r ≤ τ`. -/
theorem evolution_comp {D : VolterraData 𝕜 X Y} (hD : D.Compatible) {s r τ : ℝ}
    (hsr : s ≤ r) (hrτ : r ≤ τ) : (D.evolution τ r).comp (D.evolution r s) = D.evolution τ s := by
  rw [← ContinuousLinearMap.mul_def]
  exact Cocycle.extend_mul (localLaw_stripEvolution hD) hsr hrτ

theorem evolution_apply_comp {D : VolterraData 𝕜 X Y} (hD : D.Compatible) {s r τ : ℝ}
    (hsr : s ≤ r) (hrτ : r ≤ τ) (x : X) :
    D.evolution τ r (D.evolution r s x) = D.evolution τ s x := by
  rw [← ContinuousLinearMap.comp_apply, evolution_comp hD hsr hrτ]

omit [NormedSpace ℝ X] [SMulCommClass ℝ 𝕜 X] [CompleteSpace X] in
theorem one_le_evolutionBound : 1 ≤ D.evolutionBound := le_max_right _ _

/-- **Exponential bound.** `‖E(τ,s)‖ ≤ M e^{(log M)(τ - s)}` for `s ≤ τ`,
with `M = max (2 M₀ e^λ) 1`. -/
theorem norm_evolution_le {s τ : ℝ} (hsτ : s ≤ τ) :
    ‖D.evolution τ s‖ ≤
      D.evolutionBound * exp (Real.log D.evolutionBound * (τ - s)) := by
  refine Cocycle.norm_extend_le_exp D.one_le_evolutionBound (fun s τ _ _ => ?_) ?_ hsτ
  · exact (D.norm_stripEvolution_le τ s).trans (le_max_left _ _)
  · rw [ContinuousLinearMap.one_def]
    exact ContinuousLinearMap.norm_id_le

/-- **Exponential boundedness**, existential form: there are `M ≥ 1` and `ω ≥ 0` with
`‖E(τ,s)‖ ≤ M e^{ω(τ - s)}` for all `s ≤ τ`. -/
theorem exists_norm_evolution_le :
    ∃ M ω : ℝ, 1 ≤ M ∧ 0 ≤ ω ∧
      ∀ s τ : ℝ, s ≤ τ → ‖D.evolution τ s‖ ≤ M * exp (ω * (τ - s)) :=
  ⟨D.evolutionBound, Real.log D.evolutionBound, D.one_le_evolutionBound,
    Real.log_nonneg D.one_le_evolutionBound, fun _ _ h => D.norm_evolution_le h⟩

/-- **Strong continuity** of `τ ↦ E(τ,s) x` on `[s, ∞)`. -/
theorem continuousOn_evolution {D : VolterraData 𝕜 X Y} (hD : D.Compatible) (s : ℝ) (x : X) :
    ContinuousOn (fun τ => D.evolution τ s x) (Ici s) := by
  intro τ₀ hτ₀
  have hτ₀' : s ≤ τ₀ := hτ₀
  set r := max s (τ₀ - 1 / 2) with hr
  have hsr : s ≤ r := le_max_left _ _
  have hr2 : τ₀ - 1 / 2 ≤ r := le_max_right _ _
  have hrτ₀ : r ≤ τ₀ := max_le hτ₀' (by linarith)
  have heq : EqOn (fun τ => D.evolution τ s x)
      (fun τ => D.stripEvolution τ r (D.evolution r s x)) (Icc r (r + 1)) := by
    intro τ hτ
    simp only
    rw [← evolution_eq_stripEvolution hD hτ, evolution_apply_comp hD hsr hτ.1]
  have hc : ContinuousOn (fun τ => D.stripEvolution τ r (D.evolution r s x)) (Icc r (r + 1)) :=
    D.continuousOn_stripEvolution r _
  have hcw : ContinuousWithinAt (fun τ => D.evolution τ s x) (Icc r (r + 1)) τ₀ :=
    (hc.congr heq) τ₀ ⟨hrτ₀, by linarith⟩
  refine hcw.mono_of_mem_nhdsWithin ?_
  have hsub : Ici s ∩ Ioo (τ₀ - 1 / 2) (τ₀ + 1 / 2) ⊆ Icc r (r + 1) := by
    intro t ht
    exact ⟨max_le ht.1 ht.2.1.le, by linarith [ht.2.2]⟩
  exact mem_of_superset (inter_mem_nhdsWithin (Ici s) (Ioo_mem_nhds (by linarith) (by linarith)))
    hsub

/-- **Periodicity.** If the coefficients are `P`-periodic, `E(τ + P, s + P) = E(τ,s)`. -/
theorem evolution_periodic {P : ℝ} (hB : ∀ r, D.B (r + P) = D.B r) (τ s : ℝ) :
    D.evolution (τ + P) (s + P) = D.evolution τ s :=
  Cocycle.extend_periodic (D.stripEvolution_periodic hB) τ s

/-- **Uniqueness of the global family.** A family that is strongly continuous on every strip,
satisfies the Volterra equation on every strip and the evolution law, coincides with
`evolution` for all `s ≤ τ`. -/
theorem eq_evolution_of_volterra {D : VolterraData 𝕜 X Y} (hD : D.Compatible)
    (E' : ℝ → ℝ → X →L[𝕜] X)
    (hcont : ∀ s x, ContinuousOn (fun τ => E' τ s x) (Icc s (s + 1)))
    (heq : ∀ s τ, τ ∈ Icc s (s + 1) → ∀ x,
      E' τ s x = D.S₀ (τ - s) x + ∫ r in s..τ, D.S (τ - r) (D.B r (E' r s x)))
    (hlaw : ∀ s r τ, s ≤ r → r ≤ τ → (E' τ r).comp (E' r s) = E' τ s) :
    ∀ s τ, s ≤ τ → E' τ s = D.evolution τ s := by
  have hstrip : ∀ s τ, τ ∈ Icc s (s + 1) → E' τ s = D.evolution τ s := fun s τ hτ => by
    rw [evolution_eq_stripEvolution hD hτ]
    exact D.eq_stripEvolution_of_volterra s (E' · s) (hcont s) (heq s) τ hτ
  suffices H : ∀ n : ℕ, ∀ s τ : ℝ, s ≤ τ → τ ≤ s + n + 1 → E' τ s = D.evolution τ s by
    intro s τ hsτ
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
      rw [← hlaw s (s + 1) τ (by linarith) h.le, ← evolution_comp hD (by linarith) h.le,
        ih (s + 1) τ h.le (by push_cast at h2; linarith),
        hstrip s (s + 1) ⟨by linarith, le_rfl⟩]

end VolterraData

end UnforcedLeray.Infra.VolterraEvolution
