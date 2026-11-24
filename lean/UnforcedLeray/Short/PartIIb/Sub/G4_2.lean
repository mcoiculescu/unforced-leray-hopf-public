import UnforcedLeray.Short.PartIIb.Sub.G4

/-!
# Part II-b, task `PartII-b:G4/2` (`FrozenStreamBounds`): decomposition

Source of record: `the November 2 reference manuscript`, lines 2347-2358: the
Gaussian angular-two eigenstream is a harmonic quadrupole plus a Gaussian remainder outside a fixed
core; periodizing the harmonic part uses `sumInvSqShift` and gives `(π/c)² csc²(π(q+iη)/c)`; the
apparent poles are replaced by the smooth core, giving exponential transverse decay at scale `c`
with polynomial `c` costs.

Three true source facts, stated as `Prop`s, and the conditional theorem `frozenStreamBounds_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

/-- Leaf (a), smoothness of the planar eigenstream including the origin (SP 2347-2352). The regular
index-2 root at `r = 0` gives `q(r) = r² p(r²)` with `p` smooth, so `planarStream q =
(x₁+ix₂)² H(|x|²)` with `H` smooth; this uses the eigen equation `q = 2ik/(λ+2iΩ) · greenInverse q`
(`Re λ > 0`), not only `ContDiffOn q (Ioi 0)`. -/
def PlanarStreamSmooth : Prop :=
  ∀ (lam : ℂ) (q : Planar.Profile), Planar.IsGrowingEigenpair lam q →
    ContDiff ℝ ∞ (planarStream q)

/-- Leaf (b), quadrupole plus Gaussian remainder outside a core (SP 2349-2352): with
`M = -¼ · ∫₀^∞ s³ q` the planar stream minus the harmonic part `M (x₁ - i x₂)^{-2}` has all
derivatives bounded by a Gaussian outside a ball of radius `ρ`. -/
def PlanarStreamQuadSplit : Prop :=
  ∀ (lam : ℂ) (q : Planar.Profile), Planar.IsGrowingEigenpair lam q →
    ∃ (ρ : ℝ) (M : ℂ), 0 < ρ ∧ ∀ j : ℕ, ∃ (C κ : ℝ), 0 < κ ∧ ∀ x : ℝ × ℝ,
      ρ ^ 2 < x.1 ^ 2 + x.2 ^ 2 →
        ‖iteratedFDeriv ℝ j (fun y : ℝ × ℝ => planarStream q y -
            M * (((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) ^ (-2 : ℤ))) x‖ ≤
          C * Real.exp (-(κ * (x.1 ^ 2 + x.2 ^ 2)))

/-- Leaf (c), periodization with the core cut (SP 2349-2358, using `SumInvSqShift`): a smooth
`F : ℝ² → ℂ` equal to `M (x₁ - i x₂)^{-2}` plus a Gaussian-bounded remainder outside a ball
has a `c`-periodization `Σ_k F(x₁ + kc, x₂)` that is `C^∞`, with all derivatives bounded by
`C c^N e^{-κ|x₂|/c}` for `c ≥ 1`. -/
def PeriodizeCoreCut : Prop :=
  ∀ (F : ℝ × ℝ → ℂ) (ρ : ℝ) (M : ℂ), ContDiff ℝ ∞ F → 0 < ρ →
    (∀ j : ℕ, ∃ (C κ : ℝ), 0 < κ ∧ ∀ x : ℝ × ℝ, ρ ^ 2 < x.1 ^ 2 + x.2 ^ 2 →
        ‖iteratedFDeriv ℝ j (fun y : ℝ × ℝ => F y -
            M * (((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) ^ (-2 : ℤ))) x‖ ≤
          C * Real.exp (-(κ * (x.1 ^ 2 + x.2 ^ 2)))) →
    ∀ j : ℕ, ∃ (C κ : ℝ) (N : ℕ), 0 < C ∧ 0 < κ ∧ ∀ c : ℝ, 1 ≤ c →
      ContDiff ℝ ∞ (fun x : ℝ × ℝ => ∑' k : ℤ, F (x.1 + k * c, x.2)) ∧
      ∀ x : ℝ × ℝ, ‖iteratedFDeriv ℝ j (fun y : ℝ × ℝ => ∑' k : ℤ, F (y.1 + k * c, y.2)) x‖ ≤
        C * c ^ N * Real.exp (-(κ * |x.2| / c))

/-- **Conditional assembly**: `FrozenStreamBounds` from the three leaves. -/
theorem frozenStreamBounds_of (hA : PlanarStreamSmooth) (hB : PlanarStreamQuadSplit)
    (hC : PeriodizeCoreCut) : FrozenStreamBounds := by
  intro lam q h j
  obtain ⟨ρ, M, hρ, hsplit⟩ := hB lam q h
  exact hC (planarStream q) ρ M (hA lam q h) hρ hsplit j

end UnforcedLeray.Short.IIb
