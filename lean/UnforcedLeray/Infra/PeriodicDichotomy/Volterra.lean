import UnforcedLeray.Infra.PeriodicDichotomy.Rates
import UnforcedLeray.Infra.VolterraEvolution

/-!
# Periodic dichotomy, IV: the Volterra evolution as a periodic splitting

The global Volterra evolution of `UnforcedLeray.Infra.VolterraEvolution` (complex scalars,
compatible data, `S₀ 0 = 1`, `P`-periodic coefficients) is an evolution family in the sense of
`PeriodicSplitting`, with the strip bound required by `exists_dichotomy_rates`. This connects
`paper/main.tex`, lines 292-306 (construction of `E(τ,s)`) with lines 359-404 (the dichotomy).
-/

set_option autoImplicit false

noncomputable section

open Metric Complex Set
open UnforcedLeray.Infra.VolterraEvolution

namespace UnforcedLeray.Infra.PeriodicDichotomy

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

namespace VolterraSplitting

/-- `E(s, s) = S₀(0)` for the global Volterra evolution. -/
theorem evolution_self {V : VolterraData ℂ X Y} (hV : V.Compatible) (s : ℝ) :
    V.evolution s s = V.S₀ 0 := by
  rw [VolterraData.evolution_eq_stripEvolution hV ⟨le_rfl, by linarith⟩,
    V.stripEvolution_self]

end VolterraSplitting

/-- The periodic splitting attached to the Volterra evolution of compatible data with
`S₀ 0 = 1` and `P`-periodic coefficients, and a circle `|z| = r` in the resolvent set of the
monodromy `E(P, 0)`. -/
def PeriodicSplitting.ofVolterra (V : VolterraData ℂ X Y) (hV : V.Compatible)
    (hS₀ : V.S₀ 0 = 1) {P : ℝ} (hP : 0 < P) (hB : ∀ t, V.B (t + P) = V.B t) {r : ℝ}
    (hr : 0 < r) (hsph : sphere (0 : ℂ) r ⊆ resolventSet ℂ (V.evolution P 0)) :
    PeriodicSplitting X where
  E := V.evolution
  P := P
  P_pos := hP
  E_self s := by rw [VolterraSplitting.evolution_self hV, hS₀]
  E_comp s r τ hsr hrτ := by
    rw [ContinuousLinearMap.mul_def]
    exact VolterraData.evolution_comp hV hsr hrτ
  E_periodic τ s := V.evolution_periodic hB τ s
  r := r
  r_pos := hr
  sphere_subset := hsph

/-- The Volterra evolution satisfies the strip bound `‖E(τ, s)‖ ≤ C` for `0 ≤ τ - s ≤ P`. -/
theorem PeriodicSplitting.ofVolterra_strip (V : VolterraData ℂ X Y) (hV : V.Compatible)
    (hS₀ : V.S₀ 0 = 1) {P : ℝ} (hP : 0 < P) (hB : ∀ t, V.B (t + P) = V.B t) {r : ℝ}
    (hr : 0 < r) (hsph : sphere (0 : ℂ) r ⊆ resolventSet ℂ (V.evolution P 0)) :
    ∃ C : ℝ, ∀ s τ, s ≤ τ → τ ≤ s + P →
      ‖(PeriodicSplitting.ofVolterra V hV hS₀ hP hB hr hsph).E τ s‖ ≤ C := by
  obtain ⟨M, ω, -, hω, hE⟩ := V.exists_norm_evolution_le
  refine ⟨M * Real.exp (ω * P), fun s τ hsτ hτ => ?_⟩
  refine (hE s τ hsτ).trans ?_
  have hM : 0 ≤ M := (norm_nonneg _).trans (hE 0 0 le_rfl |>.trans (by simp))
  gcongr
  linarith

end UnforcedLeray.Infra.PeriodicDichotomy
