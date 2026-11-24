import UnforcedLeray.Short.PartIIIa.StressSpaces

/-!
# Part III-a: analytic inputs of `stress-short:coefficients` / `:transverse` (SP 2703-2745)

Each input is a `Prop` over the concrete level `p : Cons.C03.Concrete.Params`, its raw lift
`p.raw`, inlet columns `p.inlet i` and actual train `p.train` (no free predicates).  The
coefficient `v = s^{-1/2}V` is `chartCoeff p.R ·`; the regime is `IIb.BgRegime p d dm dp`
(`ε = e^{-d/ν}`, `c = ν^{-2}`).  Constants are `C ν^{-k}` (the polynomial `P_ν`).

* `RawCoeffLate` (SP 2703-2723, "the train heat expansion ... mean stream and its fixed weighted
  derivatives have size `(1+s)^{-1/2}` on transverse scale `√(1+s)` ... stream completion
  `ε(1-η∂_η-2s∂_s)ψ` has size `P_ν ε (1+s)^{-1/2}` ... fluctuations have exponential decay after
  overlap"): age `s ≥ 1`.
* `RawCoeffEarly` (SP 2724-2727, "before overlap the Gaussian comparison gives the same polynomial
  bounds ... early smoothness gives the third bound"): age `s ≤ 1`.
* `InletCoeffBounds` (SP 2726, "the finite inlet is absorbed by `P_ν`"): inlet columns.
* `RawTransverseTail`, `InletTransverseTail` (SP 2731-2745): transverse localisation; the raw tail
  uses the Gaussian vorticity tail, the horizontal stream kernels (`StreamKernelBound`) and the
  decaying zero-mode primitives.

## The slow data of the inlet (`ORG:stmt/PartIII-a/ParamsWideQuantifiers`)

`p.mode` (the eigenprofile `q`) and `p.ageCut` (`Σ`, the cutoff age `H = Σ/ν`) are fields of
`Params` that `IIb.BgRegime` does not constrain, and the inlet `p.inlet i` is linear in `p.mode`.
In the source the inlet is the fixed Gaussian angular-two eigenstream of the frozen growing pair
(SP 2048-2049, 2347-2358, 2385-2387), and its bounds have constants depending on it. So the two
inlet statements fix a slow age `Σ > 0` and a growing eigenpair `IsGrowingEigenpair λ q` before
the constants and restrict to levels with `p.ageCut = Σ`, `p.mode = q` (the pattern of
`Short/PartII-b/Sub/G4.lean` and `IIb.ExactSplitExport`). The raw statements involve only the raw
lift and the train and stay uniform.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.IIb

/-- **Train heat expansion at late age** (SP 2703-2723): for `s ≥ 1`,
`√s W|v_raw| ≤ P_ν(s^{-1/2}+ε)` and the `L²_ηL^∞_q` bound at age `s`. -/
def RawCoeffLate : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∀ mZ : ℝ, 3 / 2 < mZ → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
      (∀ pt : ℝ × (ℝ × ℝ), 1 ≤ pt.1 →
        Real.sqrt pt.1 * transWeight mZ pt * ‖chartCoeff p.R p.raw pt‖ ≤
          C * (p.ν⁻¹) ^ k * (pt.1 ^ (-1 / 2 : ℝ) + p.ε)) ∧
      (∀ s : ℝ, 1 ≤ s → etaL2QSup p.c mZ (chartCoeff p.R p.raw) s ≤
        ENNReal.ofReal (C * (p.ν⁻¹) ^ k *
          ((1 + s) ^ (-3 / 4 : ℝ) + p.ε * (1 + s) ^ (-1 / 4 : ℝ))))

/-- **Gaussian comparison before overlap and early smoothness** (SP 2724-2727): for `0 < s ≤ 1`,
`√s W|v_raw| ≤ P_ν √s` and the `L²_ηL^∞_q` norm of `W v_raw(s)` is `≤ P_ν`. -/
def RawCoeffEarly : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∀ mZ : ℝ, 3 / 2 < mZ → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
      (∀ pt : ℝ × (ℝ × ℝ), 0 < pt.1 → pt.1 ≤ 1 →
        Real.sqrt pt.1 * transWeight mZ pt * ‖chartCoeff p.R p.raw pt‖ ≤
          C * (p.ν⁻¹) ^ k * Real.sqrt pt.1) ∧
      (∀ s : ℝ, 0 < s → s ≤ 1 → etaL2QSup p.c mZ (chartCoeff p.R p.raw) s ≤
        ENNReal.ofReal (C * (p.ν⁻¹) ^ k))

/-- **The finite inlet is absorbed by `P_ν`** (SP 2726; the inlet construction 2347-2362, the
frozen growing pair 2048-2049): at a fixed slow age `Σ > 0` and a fixed growing eigenpair
`(λ, q)`, at the levels with `p.ageCut = Σ`, `p.mode = q`, each inlet column `E_i` has chart
coefficient with `√s W|v_i| ≤ P_ν`, `√s W|v_i| ≤ P_ν√s` for `s ≤ 1`, and
`‖W v_i(s)‖_{L²_ηL^∞_q} ≤ P_ν(1+s)^{-3/4}` for every `s > 0` (the inlet is supported at ages
`≤ H/2 = Σ/(2ν)`, polynomial in `ν⁻¹`, so the decay is absorbed). The constants depend on
`(Σ, q)`. -/
def InletCoeffBounds : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∀ mZ : ℝ, 3 / 2 < mZ →
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ i : Fin 2,
      (∀ pt : ℝ × (ℝ × ℝ), 0 < pt.1 →
        Real.sqrt pt.1 * transWeight mZ pt * ‖chartCoeff p.R (p.inlet i) pt‖ ≤
          C * (p.ν⁻¹) ^ k) ∧
      (∀ pt : ℝ × (ℝ × ℝ), 0 < pt.1 → pt.1 ≤ 1 →
        Real.sqrt pt.1 * transWeight mZ pt * ‖chartCoeff p.R (p.inlet i) pt‖ ≤
          C * (p.ν⁻¹) ^ k * Real.sqrt pt.1) ∧
      (∀ s : ℝ, 0 < s → etaL2QSup p.c mZ (chartCoeff p.R (p.inlet i)) s ≤
        ENNReal.ofReal (C * (p.ν⁻¹) ^ k * (1 + s) ^ (-3 / 4 : ℝ)))

/-- **Decay of the horizontal stream kernels** (SP 2740-2742): for `|k| ≥ 2π/c`,
`e^{-|k||η|}/(2|k|) ≤ (c/(4π)) e^{-2π|η|/c}`. -/
def StreamKernelBound : Prop :=
  ∀ c : ℝ, 0 < c → ∀ k η : ℝ, 2 * Real.pi / c ≤ |k| →
    Real.exp (-(|k| * |η|)) / (2 * |k|) ≤ c / (4 * Real.pi) * Real.exp (-(2 * Real.pi * |η| / c))

/-- **Transverse tail of the raw part and of the planar train** (SP 2731-2745): for every
`D > 0` there are `C_⊥, ν₀` with, on `0 < s < ε^{-b}`, `|η| > C_⊥(c/ν + √(ε^{-b}) + 1)`,
`√s W(|v_raw| + |v_flat|) ≤ e^{-D/ν}`. -/
def RawTransverseTail : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∀ mZ : ℝ, 3 / 2 < mZ → ∀ bexp D : ℝ, 0 < bexp → 0 < D →
    ∃ (Cperp ν₀ : ℝ), 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ pt : ℝ × (ℝ × ℝ), 0 < pt.1 → pt.1 < p.ε ^ (-bexp) →
        Cperp * (p.c / p.ν + Real.sqrt (p.ε ^ (-bexp)) + 1) < |pt.2.2| →
        Real.sqrt pt.1 * transWeight mZ pt *
          (‖chartCoeff p.R p.raw pt‖ + ‖p.train.v pt.1 pt.2‖) ≤ Real.exp (-D / p.ν)

/-- **Transverse tail of the inlet columns** (SP 2743-2745, "Increasing `C_⊥` absorbs ... the
finite inlet's stream tail"; the periodized eigenstream decays exponentially in `η`, SP
2347-2358): at a fixed slow age `Σ > 0` and a fixed growing eigenpair `(λ, q)`, at the levels with
`p.ageCut = Σ`, `p.mode = q`; `C_⊥, ν₀` depend on `(Σ, q)`. -/
def InletTransverseTail : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∀ mZ : ℝ, 3 / 2 < mZ → ∀ bexp D : ℝ, 0 < bexp → 0 < D →
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
    ∃ (Cperp ν₀ : ℝ), 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ i : Fin 2,
      ∀ pt : ℝ × (ℝ × ℝ), 0 < pt.1 → pt.1 < p.ε ^ (-bexp) →
        Cperp * (p.c / p.ν + Real.sqrt (p.ε ^ (-bexp)) + 1) < |pt.2.2| →
        Real.sqrt pt.1 * transWeight mZ pt * ‖chartCoeff p.R (p.inlet i) pt‖ ≤
          Real.exp (-D / p.ν)

end UnforcedLeray.Short.IIIa
