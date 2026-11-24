import UnforcedLeray.Short.PartIIa.Sub.N02

/-!
# Part II-a, task `PartII-a:N02/4` (`NearLerayNonzeroMode`): split into named lemmas

Target: `NearLerayNonzeroMode` (`Short/PartII-a/Sub/N02.lean`, zero `q`-mean tests, source lines
1730-1740 of `the November 2 reference manuscript`).

This file does not prove the target. It proves the assembly
`nearLerayNonzeroMode_of_split` (fully proved) from two named analytic `Prop`s:

* `NzFlatPotentials` (lemma (b)): the flat Hodge potentials of a zero-`q`-mean test, with moment
  bounds. Analytic core: `q`-Fourier expansion and Parseval, per-mode `η`-multiplier `P_0(k, ξ)`
  with `|∂_ξ^j P_0| ≤ C_j |k|^{-j}` (`Units/B0493.lean`), `S` commutes with the projections.
* `NzCutoffApprox` (lemma (d)): the cutoffs `χ(η/L) φ`, `χ(η/L) ψ` with `L = ε^{-1/2}`, which are
  band potentials (`IsCTest`), so `NearGradMember`/`NearStreamMember` place their exact
  counterparts in `(solenoidalHC ε c)ᗮ` and `solenoidalHC ε c`. Elementary estimates, no `c`.

The Hilbert-space identification of the two projections (lemma (c)) is proved here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-! ### Moment functionals on `measureH c` (the summands of `nearLerayRhs`) -/

/-- `∫ (|η|^j)² ‖S^a g‖²` on `measureH c`. -/
def nzSq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ) (a j : ℕ)
    (g : Profile → E) : ℝ :=
  ∫ p, (|p.2.2| ^ j) ^ 2 * ‖(opS^[a] g) p‖ ^ 2 ∂(measureH c)

/-- `Σ_{a, j ∈ {0,1}} ‖η^j S^a g‖_{L²(measureH c)}`: the moment sum of `nearLerayRhs`. -/
def nzMomSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ) (g : Profile → E) : ℝ :=
  ∑ a ∈ Finset.range 2, ∑ j ∈ Finset.range 2, (nzSq c a j g) ^ (1 / 2 : ℝ)

/-- The weighted moments `(|η|^j)² ‖S^a g‖²` for `a, j ∈ {0,1}` are integrable on `measureH c`. -/
def nzFin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ) (g : Profile → E) : Prop :=
  ∀ a ∈ Finset.range 2, ∀ j ∈ Finset.range 2,
    Integrable (fun p : Profile => (|p.2.2| ^ j) ^ 2 * ‖(opS^[a] g) p‖ ^ 2) (measureH c)

/-- Moment sum of a potential pair `(φ, ψ)` together with its first `q`- and `η`-derivatives. -/
def nzPot (c : ℝ) (φ ψ : Profile → ℂ) : ℝ :=
  nzMomSum c φ + nzMomSum c (pdQ φ) + nzMomSum c (pdEta φ) +
    nzMomSum c ψ + nzMomSum c (pdQ ψ) + nzMomSum c (pdEta ψ)

/-- The right-hand side of `NearLerayApproxOn` is `C (1 + c + c⁻¹)^d √ε` times `nzMomSum c f`. -/
theorem nearLerayRhs_eq_nzMomSum (C : ℝ) (d : ℕ) (c ε : ℝ) (f : Profile → MeridC) :
    nearLerayRhs C d c ε f = C * (1 + c + c⁻¹) ^ d * Real.sqrt ε * nzMomSum c f := rfl

/-! ### The two analytic lemma Props -/

/-- **Lemma (b): flat Hodge potentials of a zero-`q`-mean test (analytic core).** For a smooth test `f`
with zero `q`-mean and `c > 0`, `f` is pointwise the sum of the flat gradient `(φ_q, φ_η)` of a potential
`φ` and the flat stream field `(-ψ_η, ψ_q)` of a potential `ψ`. Both are smooth, `c`-periodic, supported
in the `s`-band of `f`; the gradient piece lies in `(solenoidalHC 0 c)ᗮ`, the stream piece in
`solenoidalHC 0 c`; the weighted moments are integrable, and `nzPot c φ ψ ≤ C (1 + c + c⁻¹)^d nzMomSum c f`
with `C`, `d` independent of `c` and `f`. Per `q`-mode `k = 2πn/c ≠ 0` the potentials are
`φ_k = (ik)^{-1} (I - P_0)_1 f_k`, with `|∂_ξ^j P_0(k,ξ)| ≤ C_j |k|^{-j}` (`Units/B0493`). -/
def NzFlatPotentials : Prop :=
  ∃ (d : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (c : ℝ), 0 < c → ∀ (f : Profile → MeridC),
    IsMeridTest c f → QMeanZero c f →
    ∃ (φ ψ : Profile → ℂ),
      ContDiff ℝ ∞ φ ∧ ContDiff ℝ ∞ ψ ∧ QPeriodic c φ ∧ QPeriodic c ψ ∧
      (∃ s0 s1 : ℝ, 0 < s0 ∧ ∀ p : Profile, (φ p ≠ 0 ∨ ψ p ≠ 0) → p.1 ∈ Icc s0 s1) ∧
      (∀ p : Profile, f p = cgradC 0 φ p + streamC 0 ψ p) ∧
      (∃ hG : MemLp (cgradC 0 φ) 2 (measureH c), hG.toLp _ ∈ (solenoidalHC 0 c)ᗮ) ∧
      (∃ hS : MemLp (streamC 0 ψ) 2 (measureH c), hS.toLp _ ∈ solenoidalHC 0 c) ∧
      nzFin c φ ∧ nzFin c ψ ∧ nzFin c (pdQ φ) ∧ nzFin c (pdEta φ) ∧
      nzFin c (pdQ ψ) ∧ nzFin c (pdEta ψ) ∧
      nzPot c φ ψ ≤ C * (1 + c + c⁻¹) ^ d * nzMomSum c f

/-- **Lemma (d): cutoff approximation (elementary).** Given the gradient and stream membership of
`NearGradMember` and `NearStreamMember`, the cutoffs `χ(η/L) φ`, `χ(η/L) ψ` with `L = ε^{-1/2}` give
`cgradC ε (χ_L φ) ∈ (solenoidalHC ε c)ᗮ` and `streamC ε (χ_L ψ) ∈ solenoidalHC ε c` within
`C √ε nzPot c φ ψ` of the flat pieces. Here `χ` is a fixed smooth cutoff with `χ = 1` on `[-1,1]`, support
in `[-2,2]`, `0 ≤ χ ≤ 1`. Estimates: `|1 - χ_L| ≤ |η|/L`, `|χ_L'| ≤ C/L`,
`ε K(χ_L φ) = ε(2 χ_L Sφ + χ_L η∂_η φ + (η/L) χ'(η/L) φ)` with `ε ≤ √ε`. No `c`-dependence. -/
def NzCutoffApprox : Prop :=
  NearGradMember → NearStreamMember →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c ε : ℝ), 0 < c → 0 < ε → ε ≤ 1 →
      ∀ (φ ψ : Profile → ℂ), ContDiff ℝ ∞ φ → ContDiff ℝ ∞ ψ → QPeriodic c φ → QPeriodic c ψ →
      (∃ s0 s1 : ℝ, 0 < s0 ∧ ∀ p : Profile, (φ p ≠ 0 ∨ ψ p ≠ 0) → p.1 ∈ Icc s0 s1) →
      nzFin c φ → nzFin c ψ → nzFin c (pdQ φ) → nzFin c (pdEta φ) →
      nzFin c (pdQ ψ) → nzFin c (pdEta ψ) →
      ∀ (hG : MemLp (cgradC 0 φ) 2 (measureH c)) (hS : MemLp (streamC 0 ψ) 2 (measureH c)),
        (∃ g ∈ (solenoidalHC ε c)ᗮ, ‖hG.toLp _ - g‖ ≤ C * Real.sqrt ε * nzPot c φ ψ) ∧
        (∃ s ∈ solenoidalHC ε c, ‖hS.toLp _ - s‖ ≤ C * Real.sqrt ε * nzPot c φ ψ)

/-! ### Lemma (c): identification of the two projections (proved) -/

/-- If `F = G + S` with `G ∈ Kᗮ` and `S ∈ K`, then `Kᗮ.starProjection F = G` and `K.starProjection F = S`. -/
theorem nzN02_starProjection_of_decomp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (K : Submodule ℂ E) [K.HasOrthogonalProjection] [Kᗮ.HasOrthogonalProjection]
    (F G S : E) (hG : G ∈ Kᗮ) (hS : S ∈ K) (h : F = G + S) :
    Kᗮ.starProjection F = G ∧ K.starProjection F = S := by
  have hK0 : K.starProjection G = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff (K := K)).2 hG
  have hK1 : K.starProjection S = S := (Submodule.starProjection_eq_self_iff (K := K)).2 hS
  have hO0 : Kᗮ.starProjection S = 0 := Submodule.starProjection_orthogonal_apply_eq_zero (K := K) hS
  have hO1 : Kᗮ.starProjection G = G := (Submodule.starProjection_eq_self_iff (K := Kᗮ)).2 hG
  subst h
  constructor
  · rw [map_add, hO0, hO1, add_zero]
  · rw [map_add, hK0, hK1, zero_add]

/-! ### Assembly: the target from (b), (c), (d) -/

/-- **Assembly (fully proved).** `NearLerayNonzeroMode` follows from the flat Hodge potentials (b) and
the cutoff approximation (d). -/
theorem nearLerayNonzeroMode_of_split (hB : NzFlatPotentials) (hD : NzCutoffApprox) :
    NearLerayNonzeroMode := by
  unfold NearLerayNonzeroMode
  intro hgrad hstream
  obtain ⟨d, C, hC, hpot⟩ := hB
  obtain ⟨Cd, hCd, hcut⟩ := hD hgrad hstream
  refine ⟨d, Cd * C, mul_nonneg hCd hC, fun c ε hc hε hε1 f F hf hT hF => ?_⟩
  obtain ⟨φ, ψ, hφs, hψs, hφp, hψp, hband, hdec, ⟨hG, hGm⟩, ⟨hS, hSm⟩,
    h1, h2, h3, h4, h5, h6, hbd⟩ := hpot c hc f hf hT
  have hsum : F = hG.toLp (cgradC 0 φ) + hS.toLp (streamC 0 ψ) := by
    apply Lp.ext
    filter_upwards [hF, Lp.coeFn_add (hG.toLp (cgradC 0 φ)) (hS.toLp (streamC 0 ψ)),
      hG.coeFn_toLp, hS.coeFn_toLp] with p hFp hadd hGp hSp
    rw [hFp, hadd, Pi.add_apply, hGp, hSp, hdec p]
  obtain ⟨hp1, hp2⟩ := nzN02_starProjection_of_decomp (solenoidalHC 0 c) F
    (hG.toLp (cgradC 0 φ)) (hS.toLp (streamC 0 ψ)) hGm hSm hsum
  obtain ⟨⟨g, hg, hgb⟩, ⟨s, hs, hsb⟩⟩ :=
    hcut c ε hc hε hε1 φ ψ hφs hψs hφp hψp hband h1 h2 h3 h4 h5 h6 hG hS
  have h0 : 0 ≤ Cd * Real.sqrt ε := mul_nonneg hCd (Real.sqrt_nonneg ε)
  have hle : Cd * Real.sqrt ε * nzPot c φ ψ ≤
      Cd * Real.sqrt ε * (C * (1 + c + c⁻¹) ^ d * nzMomSum c f) :=
    mul_le_mul_of_nonneg_left hbd h0
  refine ⟨⟨g, hg, ?_⟩, ⟨s, hs, ?_⟩⟩
  · rw [hp1, nearLerayRhs_eq_nzMomSum]
    refine le_trans hgb (le_trans hle (le_of_eq ?_))
    ring
  · rw [hp2, nearLerayRhs_eq_nzMomSum]
    refine le_trans hsb (le_trans hle (le_of_eq ?_))
    ring

end UnforcedLeray.Short.PartIIa
