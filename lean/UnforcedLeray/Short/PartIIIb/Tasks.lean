import UnforcedLeray.Short.PartIIIb.Basic
import UnforcedLeray.Short.PartIIIb.MixedReturn
import UnforcedLeray.Short.PartIIIb.Scalar
import UnforcedLeray.Short.PartIIIb.Near
import UnforcedLeray.Short.PartIIIb.StatementsA
import UnforcedLeray.Short.PartIIIb.Assembly
import UnforcedLeray.Short.PartIIIb.StatementsB

/-!


Each `def T_… : Prop` is one proof obligation that follows from earlier Props of Part III-b by
estimates on exponents (no further theory).  They are the missing arrows of
`Assembly.spectral_assembly` (hypotheses `HSmall`, `GainConv`) and of the repair section
(`QSmall` from the error families and the pair norm, lines 5644-5686).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set

namespace UnforcedLeray.Short.PartIIIb

/-- Continuity in `z` of the frozen quantity `ℓ(z) w(z)` of `closure:mixed-return`
(line 5760: "the real function `d_n` is continuous"), where `w(z) = (I - R̃(z))⁻¹ a(z)`. -/
def T_schurContinuity : Prop :=
  ∀ {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (A : ℝ → X →L[ℝ] E) (B : ℝ → E →L[ℝ] X) (C : ℝ → X →L[ℝ] X) (R : ℝ → E →L[ℝ] E)
    (a : ℝ → E) (ℓ : ℝ → E →L[ℝ] ℝ) (c q : ℝ),
    ContinuousOn A (Icc (-1) 1) → ContinuousOn B (Icc (-1) 1) → ContinuousOn C (Icc (-1) 1) →
    ContinuousOn R (Icc (-1) 1) → ContinuousOn a (Icc (-1) 1) → ContinuousOn ℓ (Icc (-1) 1) →
    (∀ z ∈ Icc (-1 : ℝ) 1, ‖C z‖ ≤ c) → c < 1 →
    (∀ z ∈ Icc (-1 : ℝ) 1, ‖schurTilde (A z) (B z) (C z) (R z)‖ ≤ q) → q < 1 →
    ContinuousOn (fun z => ℓ z (schurSol (A z) (B z) (C z) (R z) (a z))) (Icc (-1) 1)

/-- `MixedReturnLemma` from its helpers (lines 5744-5774). -/
def T_mixedReturn : Prop := MR_Reduce → MR_Crossing → T_schurContinuity → MixedReturnLemma

/-- Exponent bookkeeping for `NearParameterChoice` (lines 4109-4124): for `p > 0`,
`(C_* ν^r e^{-d₀/ν})^p e^{x/ν} ≤ P_ν e^{-(p d₀ - x)/ν}` uniformly for `C_* ∈ [c₁,c₂]`,
`|r| ≤ r_max`. -/
def T_epsPow : Prop :=
  ∀ (c1 c2 rmax d0 p x : ℝ), 0 < c1 → c1 ≤ c2 → 0 ≤ rmax → 0 < d0 → 0 < p →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ Cs ∈ Icc c1 c2, ∀ r ∈ Icc (-rmax) rmax,
        (Cs * ν ^ r * Real.exp (-d0 / ν)) ^ p * Real.exp (x / ν) ≤
          C * ν⁻¹ ^ k * Real.exp (-(p * d0 - x) / ν)

/-- `NearParameterChoice` from `T_epsPow`. -/
def T_nearParam : Prop := T_epsPow → NearParameterChoice

/-- `A_* = ε³|N_ν|ν^{5+2μ_n(z)} = e^{-z}/(2|𝒞(σ₀)|)` exactly (lines 5955-5957), for `0<ν<1`. -/
def T_astarExact : Prop :=
  ∀ (lam κ Cσ : ℂ) (σ₀ ν z : ℝ), Cσ ≠ 0 → 0 < ν → ν < 1 →
    Astar lam κ Cσ σ₀ ν z = Real.exp (-z) / (2 * ‖Cσ‖)

/-- `LoopGainBand` from `T_astarExact` (lines 5955-5957). -/
def T_loopGain : Prop := T_astarExact → LoopGainBand

/-- Exact value of the signed unit response on the phase-locked sequence (lines 5962-5967):
`2ε³ν^{5+2μ} Re[𝒞(μ)N_ν] = e^{-z} Re[𝒞(μ)/𝒞(σ₀)]` when `𝒞(σ₀)N_ν > 0`. -/
def T_unitRespExact : Prop :=
  ∀ (lam κ ell : ℂ) (J : ℂ → ℂ) (σ₀ ν z : ℝ), 0 < ν → ν < 1 →
    mellinC lam ell J (σ₀ : ℂ) ≠ 0 →
    (∃ m : ℤ, lam.im / ν - κ.im * Real.log ν + Complex.arg (mellinC lam ell J (σ₀ : ℂ))
        = 2 * Real.pi * m) →
    unitResp lam κ (mellinC lam ell J)
        (epsCube lam.re κ σ₀ (mellinC lam ell J (σ₀ : ℂ)) ν) ν (muWin σ₀ ν z) =
      Real.exp (-z) * ((mellinC lam ell J ((muWin σ₀ ν z : ℝ) : ℂ) /
        mellinC lam ell J (σ₀ : ℂ)).re)

/-- Continuity of `𝒞` at a real point of the strip (lines 4703, 5924). -/
def T_mellinContinuousAt : Prop :=
  ∀ (lam ell : ℂ) (J : ℂ → ℂ) (σ₀ : ℝ), 0 < lam.re → 0 < σ₀ → ContinuousAt J (σ₀ : ℂ) →
    ContinuousAt (mellinC lam ell J) (σ₀ : ℂ)

/-- `ScalarGainLimit` from the exact identity and continuity (lines 5960-5972). -/
def T_scalarGain : Prop := T_unitRespExact → T_mellinContinuousAt → ScalarGainLimit

/-- Sequence form of `ν⁻ᵏ e^{-c/ν} → 0`, and with `√ν` (lines 4823-4830, 5900-5904). -/
def T_polyExp : Prop :=
  ∀ (k : ℕ) (c : ℝ) (ν : ℕ → ℝ), 0 < c → (∀ n, 0 < ν n) → Tendsto ν atTop (𝓝 0) →
    Tendsto (fun n => (ν n)⁻¹ ^ k * Real.exp (-c / ν n)) atTop (𝓝 0) ∧
    Tendsto (fun n => (ν n)⁻¹ ^ k * Real.exp (-c / Real.sqrt (ν n))) atTop (𝓝 0)

/-- Explicit Laplace integral of the unit coefficient (lines 4709-4715):
`a₀(B_μ) = -(21/4) L(μ) + O(P_ν e^{-b/ν})` for a cutoff `χ̂_f` with `χ̂_f = 1` on `[0,1]`,
`χ̂_f = 0` on `[1.1,∞)`. -/
def T_a0Unit : Prop :=
  ∀ (lam ell : ℂ) (chi dchi : ℝ → ℝ) (μ : ℝ), 0 < lam.re → 0 < μ →
    (∀ x, HasDerivAt chi (dchi x) x) → Continuous dchi → (∀ x, x ≤ 1 → chi x = 1) → (∀ x, 1.1 ≤ x → chi x = 0) →
    ∃ (C b ν₀ : ℝ) (k : ℕ), 0 < b ∧ 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ‖aZero lam ell (μ : ℂ) (Bmu chi dchi ν μ) + (21 / 4 : ℂ) * LCoeff lam ell (μ : ℂ)‖ ≤
        C * ν⁻¹ ^ k * Real.exp (-b / ν)

/-- Newton kernel derivative (lines 4863-4866): with `F = ∂₃₃N`, `N = 1/(4π|x|)`,
`D²F(r,0,0) = (4π r⁵)⁻¹ diag(-12, 3, 9)`. -/
def T_newtonD2 : Prop :=
  ∀ r : ℝ, 0 < r →
    let F : (Fin 3 → ℝ) → ℝ := fun x =>
      (3 * x 2 ^ 2 - (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2)) /
        (4 * Real.pi * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) ^ (5 / 2 : ℝ))
    ∀ i j : Fin 3,
      fderiv ℝ (fderiv ℝ F) ![r, 0, 0] (Pi.single i 1) (Pi.single j 1) =
        (if i = j then (![-12, 3, 9] : Fin 3 → ℝ) i else 0) / (4 * Real.pi * r ^ 5)

/-- `HSmall` (the hypothesis `r_n + h_n → 0` of `closure:mixed-return`) from the module results
(lines 5883-5909): `QSmall`, `PLBound`, `CurvedFlatComparison`, `FlatLimit`, with the budget
`1.1 a_s < min{c_N, γ/100}/4` (line 5877-5879) and `A_*` bounded on the window
(`LoopGainBand`). -/
def T_hsmall : Prop :=
  ∀ (S : ReturnSeq) (lam κ ell : ℂ) (J : ℂ → ℂ) (σ₀ a_s cN : ℝ),
    0 < lam.re → 0 < a_s → mellinC lam ell J (σ₀ : ℂ) ≠ 0 →
    (∀ n, 0 < S.ν n) → Tendsto S.ν atTop (𝓝 0) →
    1.1 * a_s < min cN (lam.re / 100) / 4 →
    QSmall S lam.re → PLBound S a_s → CurvedFlatComparison S a_s cN →
    FlatLimit S lam κ ell J σ₀ a_s → HSmall S

/-- `GainConv` (lines 5960-5972): `Λ(a_μ) = unitResp + O(A_* P e^{-b/ν})` (`FlatLimit`) and
`unitResp → e^{-z}` uniformly (`ScalarGainLimit`). -/
def T_gain : Prop :=
  ScalarGainLimit → ∀ (S : ReturnSeq) (lam κ ell : ℂ) (J : ℂ → ℂ) (σ₀ a_s : ℝ),
    0 < lam.re → lam.im ≠ 0 → ell ≠ 0 → ContinuousAt J (σ₀ : ℂ) → 0 < σ₀ →
    mellinC lam ell J (σ₀ : ℂ) ≠ 0 → (∀ n, 0 < S.ν n) → Tendsto S.ν atTop (𝓝 0) →
    (∀ᶠ n : ℕ in atTop,
        lam.im / S.ν n - κ.im * Real.log (S.ν n) + Complex.arg (mellinC lam ell J (σ₀ : ℂ))
          = 2 * Real.pi * Real.sign lam.im * n) →
    FlatLimit S lam κ ell J σ₀ a_s → GainConv S

/-- `QSmall` from the error-family bounds and the pair norm (lines 5644-5686): the four matrix
coefficients `Qδ_A, Qδ_G e^{a/ν}, e^{-a/ν}χ_A + e^{-a/ν}K_sQδ_A, χ_G + K_sQδ_G`, `a = γ/8`,
all `≤ P e^{-γ/(100ν)}` when `ω_b, m₀, η_δ < γ/1000`. -/
def T_qsmall : Prop :=
  ∀ (S : ReturnSeq) (γ ωb m0 ηδ : ℝ), 0 < γ → 0 ≤ ωb → 0 ≤ m0 → 0 ≤ ηδ →
    ωb < γ / 1000 → m0 < γ / 1000 → ηδ < γ / 1000 →
    (∀ n, 0 < S.ν n) → Tendsto S.ν atTop (𝓝 0) →
    (∀ n, ∀ z ∈ Icc (-1 : ℝ) 1, (S.ops n z).IsGraphLift) →
    ErrorFamilyBounds S γ ωb m0 → PairNormAndNearSolver S γ ηδ → QSmall S γ

end UnforcedLeray.Short.PartIIIb
