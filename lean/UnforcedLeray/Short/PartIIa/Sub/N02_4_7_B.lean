import UnforcedLeray.Short.PartIIa.Sub.N02_4_7

/-!
# Part II-a, task `PartII-a:N02/4/7` (`nzModeBounds`): second-level decomposition

Source: `the November 2 reference manuscript`, lines 1722-1727.  The `j = 0` and `j = 1`
moment bounds of `NzModeBounds` are stated separately (`NzmbJ0`, `NzmbJ1`); `nzModeBounds_of` assembles
`NzModeBounds` from them (elementary bookkeeping: `(1+|k|⁻¹) ≤ (1+|k|⁻¹)²`, nonnegativity).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- **`j = 0` moment bound.** Energy identity (`NzmbWeightedEnergy`) for `(S^α φ, S^α ψ)` with data
`(S^α a, S^α b)` (`nzmb_modeEq_iter`, `nzmb_iter_fderiv`): each of `k²‖S^αφ‖², ‖∂_η S^αφ‖², k²‖S^αψ‖²,
‖∂_η S^αψ‖²` integrates (against `s^{-3/2}`) to at most `∫(‖S^αa‖²+‖S^αb‖²)`; so the moments of
`kφ, ∂_ηφ, kψ, ∂_ηψ` are `≤ m(a)+m(b)` and those of `φ, ψ` are `≤ |k|⁻¹(m(a)+m(b))`. -/
def NzmbJ0 : Prop :=
  ∀ (k : ℝ), k ≠ 0 → ∀ (a b φ ψ : ℝ × ℝ → ℂ),
    ContDiff ℝ ∞ a → ContDiff ℝ ∞ b → NzBand2 a → NzBand2 b → NzDecay2 φ → NzDecay2 ψ →
    NzModeEq k a b φ ψ →
    ∀ α ∈ Finset.range 2,
      ∀ g ∈ ({φ, fun x => fderiv ℝ φ x (0, 1), fun x => (k : ℂ) * φ x,
          ψ, fun x => fderiv ℝ ψ x (0, 1), fun x => (k : ℂ) * ψ x} : Set (ℝ × ℝ → ℂ)),
        nzMom2 0 α g ≤ (1 + |k|⁻¹) * (nzMom2 0 α a + nzMom2 0 α b)

/-- **`j = 1` moment bound.** Energy identity for `(η S^α φ, η S^α ψ)` with data
`(η S^α a - S^α ψ, η S^α b + S^α φ)` (`NzmbEtaModeEq`, `NzmbEtaMul`, `NzmbSliceEtaDecay`), `η∂_ηφ =
∂_η(ηφ) - φ`, lower-order terms by `NzmbJ0`. -/
def NzmbJ1 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℝ), k ≠ 0 → ∀ (a b φ ψ : ℝ × ℝ → ℂ),
    ContDiff ℝ ∞ a → ContDiff ℝ ∞ b → NzBand2 a → NzBand2 b → NzDecay2 φ → NzDecay2 ψ →
    NzModeEq k a b φ ψ →
    ∀ α ∈ Finset.range 2,
      ∀ g ∈ ({φ, fun x => fderiv ℝ φ x (0, 1), fun x => (k : ℂ) * φ x,
          ψ, fun x => fderiv ℝ ψ x (0, 1), fun x => (k : ℂ) * ψ x} : Set (ℝ × ℝ → ℂ)),
        nzMom2 1 α g ≤
          C * (1 + |k|⁻¹) ^ 2 * ∑ i ∈ Finset.range 2, (nzMom2 i α a + nzMom2 i α b)

theorem nzMom2_nonneg (j α : ℕ) (g : ℝ × ℝ → ℂ) : 0 ≤ nzMom2 j α g := by
  unfold nzMom2
  apply Real.rpow_nonneg
  apply setIntegral_nonneg (measurableSet_Ioi.prod MeasurableSet.univ)
  intro x hx
  have h1 : 0 < x.1 := hx.1
  have := Real.rpow_nonneg h1.le (-(3 / 2 : ℝ))
  positivity

/-- Assembly of `NzModeBounds` from the `j = 0` and `j = 1` bounds. -/
theorem nzModeBounds_of (h0 : NzmbJ0) (h1 : NzmbJ1) : NzModeBounds := by
  obtain ⟨C1, hC1, hC⟩ := h1
  refine ⟨C1 + 1, by linarith, ?_⟩
  intro k hk a b φ ψ ha hb hBa hBb hφ hψ hE α hα j hj g hg
  have hsum : 0 ≤ ∑ i ∈ Finset.range 2, (nzMom2 i α a + nzMom2 i α b) :=
    Finset.sum_nonneg (fun i _ => add_nonneg (nzMom2_nonneg _ _ _) (nzMom2_nonneg _ _ _))
  have hk' : 0 ≤ |k|⁻¹ := by positivity
  have hp : 0 ≤ (1 + |k|⁻¹) := by linarith
  have hge : 1 + |k|⁻¹ ≤ (1 + |k|⁻¹) ^ 2 := by nlinarith
  have hsq : 0 ≤ (1 + |k|⁻¹) ^ 2 := by positivity
  rw [Finset.mem_range] at hj
  interval_cases j
  · have := h0 k hk a b φ ψ ha hb hBa hBb hφ hψ hE α hα g hg
    have hle : nzMom2 0 α a + nzMom2 0 α b ≤ ∑ i ∈ Finset.range 2, (nzMom2 i α a + nzMom2 i α b) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      have := add_nonneg (nzMom2_nonneg 1 α a) (nzMom2_nonneg 1 α b)
      linarith
    have hm := add_nonneg (nzMom2_nonneg 0 α a) (nzMom2_nonneg 0 α b)
    calc nzMom2 0 α g ≤ (1 + |k|⁻¹) * (nzMom2 0 α a + nzMom2 0 α b) := this
      _ ≤ (1 + |k|⁻¹) ^ 2 * ∑ i ∈ Finset.range 2, (nzMom2 i α a + nzMom2 i α b) := by
          apply mul_le_mul hge hle hm hsq
      _ ≤ (C1 + 1) * (1 + |k|⁻¹) ^ 2 * ∑ i ∈ Finset.range 2, (nzMom2 i α a + nzMom2 i α b) := by
          have : 0 ≤ (1 + |k|⁻¹) ^ 2 * ∑ i ∈ Finset.range 2, (nzMom2 i α a + nzMom2 i α b) :=
            mul_nonneg hsq hsum
          nlinarith
  · have := hC k hk a b φ ψ ha hb hBa hBb hφ hψ hE α hα g hg
    have : 0 ≤ (1 + |k|⁻¹) ^ 2 * ∑ i ∈ Finset.range 2, (nzMom2 i α a + nzMom2 i α b) :=
      mul_nonneg hsq hsum
    nlinarith

end UnforcedLeray.Short.PartIIa
