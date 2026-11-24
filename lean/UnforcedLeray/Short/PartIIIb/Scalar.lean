import UnforcedLeray.Short.PartIIIb.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Real.Sign
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Phase selection and the scalar crossing (lines 5922-5985) and the unit coefficient (4697-4730)

Concrete objects of the source, on their whole carriers:

* `Nnu lam κ ν = e^{λ/ν} ν^{-κ}` (lines 4565, 5925), `lam κ : ℂ`, `ν > 0`;
* `LCoeff lam ell μ = ℓ₊(H₀) Γ(μ+5/2) / λ^{μ+5/2}` (line 4703) and
  `mellinC lam ell J μ = (63πi/128) L(μ) J(μ)` (lines 4703, 5924), where `ell = ℓ₊(H₀)` and
  `J` is the canonical Mellin function (Corollary `cor:short-mellin`, Part I);
* `epsCube` is `ε_n³ = e^{-γ/ν} ν^{Re κ - 5 - 2σ₀} / (2|𝒞(σ₀)|)` (lines 5936-5940);
* `muWin σ₀ ν z = σ₀ + z/(2|log ν|)` (line 5946).

The ν-dependence is a sequence `ν : ℕ → ℝ`, the phase-locked sequence of line 5929-5932.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set

namespace UnforcedLeray.Short.PartIIIb

/-- `N_ν = e^{λ/ν} ν^{-κ}` (lines 4565, 5925). -/
def Nnu (lam κ : ℂ) (ν : ℝ) : ℂ := Complex.exp (lam / (ν : ℂ)) * (ν : ℂ) ^ (-κ)

/-- `L(μ) = ℓ₊(H₀) Γ(μ+5/2) / λ^{μ+5/2}` (line 4703). -/
def LCoeff (lam ell : ℂ) (μ : ℂ) : ℂ :=
  ell * (Complex.Gamma (μ + 5 / 2) / lam ^ (μ + 5 / 2))

/-- `𝒞(μ) = (63πi/128) L(μ) J(μ)` (lines 4703, 5924-5926). -/
def mellinC (lam ell : ℂ) (J : ℂ → ℂ) (μ : ℂ) : ℂ :=
  ((63 * Real.pi / 128 : ℝ) : ℂ) * Complex.I * LCoeff lam ell μ * J μ

/-- The strip `0 < Re μ < 1/4` where `J` lives (Corollary `cor:short-mellin`). -/
def strip14 : Set ℂ := {μ : ℂ | 0 < μ.re ∧ μ.re < 1 / 4}

/-- `ε_n³` (lines 5936-5940), with `Cσ = 𝒞(σ₀)`, `γ = Re λ`. -/
def epsCube (γ : ℝ) (κ : ℂ) (σ₀ : ℝ) (Cσ : ℂ) (ν : ℝ) : ℝ :=
  Real.exp (-γ / ν) * ν ^ (κ.re - 5 - 2 * σ₀) / (2 * ‖Cσ‖)

/-- The window `μ_n(z) = σ₀ + z/(2|log ν_n|)` (line 5946). -/
def muWin (σ₀ ν z : ℝ) : ℝ := σ₀ + z / (2 * |Real.log ν|)

/-- The signed unit response `2 ε³ ν^{5+2μ} Re{𝒞(μ) N_ν}` (lines 5962-5964, 4719-4722). -/
def unitResp (lam κ : ℂ) (C : ℂ → ℂ) (ε3 ν μ : ℝ) : ℝ :=
  2 * ε3 * ν ^ (5 + 2 * μ) * (C (μ : ℂ) * Nnu lam κ ν).re

/-- Phase selection (lines 5924-5927): if `J` is holomorphic on the strip and not identically
zero there, `ℓ₊(H₀) ≠ 0` and `Re λ > 0`, there is `σ₀ ∈ (0,1/4)` with `𝒞(σ₀) ≠ 0`. -/
def PhaseSelection : Prop :=
  ∀ (lam ell : ℂ) (J : ℂ → ℂ), 0 < lam.re → ell ≠ 0 →
    AnalyticOnNhd ℂ J strip14 → (∃ μ ∈ strip14, J μ ≠ 0) →
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ σ₀ < 1 / 4 ∧ mellinC lam ell J (σ₀ : ℂ) ≠ 0

/-- The phase-locked sequence (lines 5928-5934): for `ω ≠ 0` and any `b c` there are `ν_n > 0`,
`ν_n → 0`, with `ω/ν_n - b log ν_n + c = 2π n sign ω` for all large `n`. -/
def PhaseLockedSequence : Prop :=
  ∀ (ω b c : ℝ), ω ≠ 0 → ∃ ν : ℕ → ℝ, (∀ n, 0 < ν n) ∧ Tendsto ν atTop (𝓝 0) ∧
    ∀ᶠ n : ℕ in atTop, ω / ν n - b * Real.log (ν n) + c = 2 * Real.pi * Real.sign ω * n

/-- The signed unit response tends to `e^{-z}` uniformly on `[-1,1]` (lines 5960-5972), on the
phase-locked sequence, for `𝒞 = mellinC lam ell J` with `J` continuous at `σ₀` and `𝒞(σ₀) ≠ 0`. -/
def ScalarGainLimit : Prop :=
  ∀ (lam κ ell : ℂ) (J : ℂ → ℂ) (σ₀ : ℝ), 0 < lam.re → lam.im ≠ 0 → ell ≠ 0 →
    ContinuousAt J (σ₀ : ℂ) → 0 < σ₀ →
    mellinC lam ell J (σ₀ : ℂ) ≠ 0 →
    ∀ ν : ℕ → ℝ, (∀ n, 0 < ν n) → Tendsto ν atTop (𝓝 0) →
      (∀ᶠ n : ℕ in atTop,
        lam.im / ν n - κ.im * Real.log (ν n) + Complex.arg (mellinC lam ell J (σ₀ : ℂ))
          = 2 * Real.pi * Real.sign lam.im * n) →
      TendstoUniformlyOn
        (fun n z => unitResp lam κ (mellinC lam ell J)
          (epsCube lam.re κ σ₀ (mellinC lam ell J (σ₀ : ℂ)) (ν n)) (ν n)
          (muWin σ₀ (ν n) z))
        (fun z => Real.exp (-z)) atTop (Icc (-1 : ℝ) 1)

/-- The loop gain `ε³ |N_ν| ν^{5+2μ_n(z)}` stays between two fixed positive constants
(lines 5955-5957): between `e^{-1}/(2|𝒞(σ₀)|)` and `e/(2|𝒞(σ₀)|)`. -/
def LoopGainBand : Prop :=
  ∀ (lam κ ell : ℂ) (J : ℂ → ℂ) (σ₀ : ℝ), 0 < lam.re → ell ≠ 0 →
    mellinC lam ell J (σ₀ : ℂ) ≠ 0 →
    ∀ ν : ℕ → ℝ, (∀ n, 0 < ν n) → Tendsto ν atTop (𝓝 0) →
      ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
        Real.exp (-1) / (2 * ‖mellinC lam ell J (σ₀ : ℂ)‖) ≤
            epsCube lam.re κ σ₀ (mellinC lam ell J (σ₀ : ℂ)) (ν n) * ‖Nnu lam κ (ν n)‖ *
              (ν n) ^ (5 + 2 * muWin σ₀ (ν n) z) ∧
        epsCube lam.re κ σ₀ (mellinC lam ell J (σ₀ : ℂ)) (ν n) * ‖Nnu lam κ (ν n)‖ *
              (ν n) ^ (5 + 2 * muWin σ₀ (ν n) z) ≤
            Real.exp 1 / (2 * ‖mellinC lam ell J (σ₀ : ℂ)‖)

end UnforcedLeray.Short.PartIIIb
