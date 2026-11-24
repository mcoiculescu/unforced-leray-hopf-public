import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.Split

/-!
# Part II-a, task `PartII-a:N02/4` (`NearLerayNonzeroMode`): decomposition into four lemma Props

Target: `NearLerayNonzeroMode` (`Sub/N02.lean`), zero `q`-mean tests, source of record
`the November 2 reference manuscript`, lines 1713-1727 (nonzero `q`-frequencies:
flat Hodge pieces, exact counterparts, inverse `q`-derivative costs `c/(2π)`, multiplier bounds) and
lines 1744-1749 ("Initially use finite Fourier sums, compact log-age support and Schwartz transverse
profiles ... Fourier truncation are dense in the displayed norm").

The helpers `nzSq`, `nzMomSum`, `nzFin`, `nzPot`, the identification `nzN02_starProjection_of_decomp`
and the cutoff Prop `NzCutoffApprox` come from the (compiled) file
`Tasks/N02LerayComparison/NonzeroMode/Split.lean` of the first attempt. Its general Prop
`NzFlatPotentials` (infinite Fourier series) is superseded by the finite-mode route below and is
no longer used.

Route (as in the source): prove the estimate for tests with finitely many nonzero `q`-modes, then pass
to all zero-mean tests by Fourier truncation.

* `NzFinPotentials` (finite modes): flat Hodge potentials `φ, ψ` of a finite-mode zero-mean test with
  exponential decay in `η` and the moment bound `nzPot ≤ C (1 + c + c⁻¹)^d nzMomSum f`.
* `NzFlatMembership`: potentials with exponential decay in `η` have `cgradC 0 φ ∈ (solenoidalHC 0 c)ᗮ`
  and `streamC 0 φ ∈ solenoidalHC 0 c` (`η`-cutoff limit of `NearGradMember`, `NearStreamMember`).
* `NzCutoffApprox` (Split.lean): the `ε`-counterparts by the cutoff `χ(η/L)`, `L = ε^{-1/2}`.
* `NzTruncApprox`: Fourier truncations of a zero-mean test converge in `H` and do not increase
  `nzMomSum`.

Proved here: the finite-mode assembly `nearLerayFin_of`, the closure lemma `nzApprox_closure`,
the density step `nzDensity` and the conditional theorem `nearLerayNonzeroMode_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-! ### Finite-mode tests and exponentially decaying potentials -/

/-- **Finite `q`-mode profiles.** `f(s, q, η) = Σ_{n ∈ M} e^{2π i n q / c} a_n(s, η)` for a finite set `M`
of nonzero frequencies (`0 ∉ M`), with smooth coefficients `a_n : ℝ × ℝ → ℂ²` supported in a band
`s ∈ [s₀, s₁]`, `s₀ > 0`, `|η| ≤ L` (source lines 1744-1745: "finite Fourier sums, compact log-age
support"). -/
def NzFinModes (c : ℝ) (f : Profile → MeridC) : Prop :=
  ∃ (M : Finset ℤ) (a : ℤ → ℝ × ℝ → MeridC), (0 : ℤ) ∉ M ∧
    (∀ n ∈ M, ContDiff ℝ ∞ (a n)) ∧
    (∀ n ∈ M, ∃ s0 s1 L : ℝ, 0 < s0 ∧
      ∀ x : ℝ × ℝ, a n x ≠ 0 → x.1 ∈ Icc s0 s1 ∧ |x.2| ≤ L) ∧
    ∀ p : Profile, f p = ∑ n ∈ M,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) •
        a n (p.1, p.2.2)

/-- A potential decays exponentially in `η` together with its first `q`- and `η`-derivatives, uniformly
in `(s, q)` (the Schwartz transverse profiles of source line 1745). -/
def NzExpDecay (φ : Profile → ℂ) : Prop :=
  ∃ κ C : ℝ, 0 < κ ∧ ∀ p : Profile,
    ‖φ p‖ ≤ C * Real.exp (-κ * |p.2.2|) ∧ ‖pdQ φ p‖ ≤ C * Real.exp (-κ * |p.2.2|) ∧
      ‖pdEta φ p‖ ≤ C * Real.exp (-κ * |p.2.2|)

/-! ### The four lemma Props -/

/-- **Lemma NzFinPotentials: flat Hodge potentials of a finite-mode zero-mean test** (source lines
1713-1727). For `c > 0` and a smooth test `f` with zero `q`-mean and finitely many `q`-modes, `f` is
pointwise the sum of the flat gradient `(φ_q, φ_η)` and the flat stream field `(-ψ_η, ψ_q)` of smooth
`c`-periodic potentials supported in the `s`-band of `f`, decaying exponentially in `η`; the weighted
moments are integrable and `nzPot c φ ψ ≤ C (1 + c + c⁻¹)^d nzMomSum c f` with `C`, `d` independent of
`c` and `f`. Per mode `k = 2πn/c`, the potentials solve `i k φ - ψ_η = f_r`, `φ_η + i k ψ = f_z`
(an explicit Green-kernel solution, `e^{-|k||η|}/(2|k|)`), the energy identity
`k²‖φ‖² + ‖φ_η‖² + k²‖ψ‖² + ‖ψ_η‖² = ‖f‖²` gives the bounds, and `|k| ≥ 2π/c`. -/
def NzFinPotentials : Prop :=
  ∃ (d : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (c : ℝ), 0 < c → ∀ (f : Profile → MeridC),
    IsMeridTest c f → QMeanZero c f → NzFinModes c f →
    ∃ (φ ψ : Profile → ℂ),
      ContDiff ℝ ∞ φ ∧ ContDiff ℝ ∞ ψ ∧ QPeriodic c φ ∧ QPeriodic c ψ ∧
      (∃ s0 s1 : ℝ, 0 < s0 ∧ ∀ p : Profile, (φ p ≠ 0 ∨ ψ p ≠ 0) → p.1 ∈ Icc s0 s1) ∧
      (∀ p : Profile, f p = cgradC 0 φ p + streamC 0 ψ p) ∧
      NzExpDecay φ ∧ NzExpDecay ψ ∧
      nzFin c φ ∧ nzFin c ψ ∧ nzFin c (pdQ φ) ∧ nzFin c (pdEta φ) ∧
      nzFin c (pdQ ψ) ∧ nzFin c (pdEta ψ) ∧
      nzPot c φ ψ ≤ C * (1 + c + c⁻¹) ^ d * nzMomSum c f

/-- **Lemma NzFlatMembership: the flat pieces lie in the flat subspaces.** For a smooth `c`-periodic
potential `φ` supported in an `s`-band and decaying exponentially in `η`, the flat gradient
`cgradC 0 φ` lies in `(solenoidalHC 0 c)ᗮ` and the flat stream field `streamC 0 φ` lies in
`solenoidalHC 0 c` (both are in `L²(measureH c)`). Proof: the cutoffs `χ(η/L) φ` are `IsCTest`, so
`NearGradMember` and `NearStreamMember` (at `ε = 0`) put `cgradC 0 (χ_L φ)` and `streamC 0 (χ_L φ)` in the
two closed subspaces; they converge in `L²(measureH c)` to `cgradC 0 φ`, `streamC 0 φ` as `L → ∞`
(dominated convergence, exponential decay, band support, weight `s^{-3/2} ≤ s₀^{-3/2}`). -/
def NzFlatMembership : Prop :=
  NearGradMember → NearStreamMember → ∀ (c : ℝ), 0 < c → ∀ (φ : Profile → ℂ),
    ContDiff ℝ ∞ φ → QPeriodic c φ →
    (∃ s0 s1 : ℝ, 0 < s0 ∧ ∀ p : Profile, φ p ≠ 0 → p.1 ∈ Icc s0 s1) → NzExpDecay φ →
    (∃ hG : MemLp (cgradC 0 φ) 2 (measureH c), hG.toLp _ ∈ (solenoidalHC 0 c)ᗮ) ∧
    (∃ hS : MemLp (streamC 0 φ) 2 (measureH c), hS.toLp _ ∈ solenoidalHC 0 c)

/-- **Lemma NzTruncApprox: Fourier truncation** (source lines 1746-1747, "Fourier truncation ... dense in
the displayed norm"). For a smooth test `f` with zero `q`-mean and a class `F` of `f` in `H`, there are
finite-mode zero-mean smooth tests `f_N` (the partial sums `Σ_{0 < |n| ≤ N} e^{2π i n q / c} a_n(s, η)`
with `a_n = c⁻¹ ∫_0^c e^{-2π i n q / c} f dq`) with classes `F_N → F` in `H` and
`nzMomSum c f_N ≤ nzMomSum c f` (the truncation commutes with `S` and `η`, and is a fibrewise
contraction in `L²(dq)` by Bessel's inequality). -/
def NzTruncApprox : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (f : Profile → MeridC), IsMeridTest c f → QMeanZero c f →
    ∀ (F : HSpace c MeridC), (F : Profile → MeridC) =ᵐ[measureH c] f →
    ∃ (fN : ℕ → Profile → MeridC) (FN : ℕ → HSpace c MeridC),
      (∀ N, IsMeridTest c (fN N) ∧ QMeanZero c (fN N) ∧ NzFinModes c (fN N) ∧
        ((FN N : Profile → MeridC) =ᵐ[measureH c] fN N) ∧
        nzMomSum c (fN N) ≤ nzMomSum c f) ∧
      Tendsto FN atTop (𝓝 F)

/-! ### Finite-mode assembly -/

/-- **Finite-mode assembly (proved).** The approximation statement on zero-mean tests with finitely many
`q`-modes follows from the potentials, their membership and the cutoff approximation. -/
theorem nearLerayFin_of (hP : NzFinPotentials) (hM : NzFlatMembership) (hD : NzCutoffApprox) :
    NearGradMember → NearStreamMember →
      NearLerayApproxOn (fun c f => QMeanZero c f ∧ NzFinModes c f) := by
  intro hgrad hstream
  obtain ⟨d, C, hC, hpot⟩ := hP
  obtain ⟨Cd, hCd, hcut⟩ := hD hgrad hstream
  refine ⟨d, Cd * C, mul_nonneg hCd hC, fun c ε hc hε hε1 f F hf hT hF => ?_⟩
  obtain ⟨φ, ψ, hφs, hψs, hφp, hψp, hband, hdec, hφd, hψd, h1, h2, h3, h4, h5, h6, hbd⟩ :=
    hpot c hc f hf hT.1 hT.2
  have hbφ : ∃ s0 s1 : ℝ, 0 < s0 ∧ ∀ p : Profile, φ p ≠ 0 → p.1 ∈ Icc s0 s1 := by
    obtain ⟨s0, s1, h0, hb⟩ := hband
    exact ⟨s0, s1, h0, fun p hp => hb p (Or.inl hp)⟩
  have hbψ : ∃ s0 s1 : ℝ, 0 < s0 ∧ ∀ p : Profile, ψ p ≠ 0 → p.1 ∈ Icc s0 s1 := by
    obtain ⟨s0, s1, h0, hb⟩ := hband
    exact ⟨s0, s1, h0, fun p hp => hb p (Or.inr hp)⟩
  obtain ⟨⟨hG, hGm⟩, -⟩ := hM hgrad hstream c hc φ hφs hφp hbφ hφd
  obtain ⟨-, ⟨hS, hSm⟩⟩ := hM hgrad hstream c hc ψ hψs hψp hbψ hψd
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

/-! ### Density: from finite modes to all zero-mean tests -/

/-- **Closure of a distance bound (proved).** If `x_N → x` and each `x_N` is within `r` of a closed
subspace `V`, then so is `x`. -/
theorem nzApprox_closure {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (V : Submodule ℂ E) [V.HasOrthogonalProjection] {x : E} {xN : ℕ → E}
    {r : ℝ} (hx : Tendsto xN atTop (𝓝 x)) (h : ∀ N, ∃ g ∈ V, ‖xN N - g‖ ≤ r) :
    ∃ g ∈ V, ‖x - g‖ ≤ r := by
  refine ⟨V.starProjection x, Submodule.starProjection_apply_mem V x, ?_⟩
  have hmin : ∀ g ∈ V, ‖x - V.starProjection x‖ ≤ ‖x - g‖ := by
    intro g hg
    rw [Submodule.starProjection_minimal]
    exact ciInf_le (⟨0, by rintro _ ⟨y, rfl⟩; exact norm_nonneg _⟩ :
      BddBelow (Set.range fun y : V => ‖x - (y : E)‖)) (⟨g, hg⟩ : V)
  have hlim : Tendsto (fun N => ‖x - xN N‖ + r) atTop (𝓝 (0 + r)) := by
    have h0 : Tendsto (fun N => ‖xN N - x‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 hx
    have h1 : Tendsto (fun N => ‖x - xN N‖) atTop (𝓝 0) := by
      simpa only [norm_sub_rev] using h0
    exact h1.add_const r
  rw [zero_add] at hlim
  refine ge_of_tendsto' hlim fun N => ?_
  obtain ⟨g, hg, hgb⟩ := h N
  calc ‖x - V.starProjection x‖ ≤ ‖x - g‖ := hmin g hg
    _ = ‖(x - xN N) + (xN N - g)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖x - xN N‖ + ‖xN N - g‖ := norm_add_le _ _
    _ ≤ ‖x - xN N‖ + r := by gcongr

/-- **Density step (proved).** The finite-mode approximation plus Fourier truncation give the
approximation on all zero-mean tests, with the same constants. -/
theorem nzDensity (hT : NzTruncApprox)
    (hfin : NearLerayApproxOn (fun c f => QMeanZero c f ∧ NzFinModes c f)) :
    NearLerayApproxOn (fun c f => QMeanZero c f) := by
  obtain ⟨d, C, hC, hA⟩ := hfin
  refine ⟨d, C, hC, fun c ε hc hε hε1 f F hf hT0 hF => ?_⟩
  obtain ⟨fN, FN, hprop, hlim⟩ := hT c hc f hf hT0 F hF
  have hcoef : 0 ≤ C * (1 + c + c⁻¹) ^ d * Real.sqrt ε :=
    mul_nonneg (mul_nonneg hC (pow_nonneg (by positivity) d)) (Real.sqrt_nonneg ε)
  have hrhs : ∀ N, nearLerayRhs C d c ε (fN N) ≤ nearLerayRhs C d c ε f := by
    intro N
    rw [nearLerayRhs_eq_nzMomSum, nearLerayRhs_eq_nzMomSum]
    exact mul_le_mul_of_nonneg_left (hprop N).2.2.2.2 hcoef
  have hall : ∀ N,
      (∃ g ∈ (solenoidalHC ε c)ᗮ,
        ‖(solenoidalHC 0 c)ᗮ.starProjection (FN N) - g‖ ≤ nearLerayRhs C d c ε f) ∧
      (∃ s ∈ solenoidalHC ε c,
        ‖(solenoidalHC 0 c).starProjection (FN N) - s‖ ≤ nearLerayRhs C d c ε f) := by
    intro N
    obtain ⟨hm, hq, hfm, hae, -⟩ := hprop N
    obtain ⟨⟨g, hg, hgb⟩, ⟨s, hs, hsb⟩⟩ := hA c ε hc hε hε1 (fN N) (FN N) hm ⟨hq, hfm⟩ hae
    exact ⟨⟨g, hg, hgb.trans (hrhs N)⟩, ⟨s, hs, hsb.trans (hrhs N)⟩⟩
  have hc1 : Tendsto (fun N => (solenoidalHC 0 c)ᗮ.starProjection (FN N)) atTop
      (𝓝 ((solenoidalHC 0 c)ᗮ.starProjection F)) :=
    ((solenoidalHC 0 c)ᗮ.starProjection.continuous.tendsto F).comp hlim
  have hc2 : Tendsto (fun N => (solenoidalHC 0 c).starProjection (FN N)) atTop
      (𝓝 ((solenoidalHC 0 c).starProjection F)) :=
    ((solenoidalHC 0 c).starProjection.continuous.tendsto F).comp hlim
  exact ⟨nzApprox_closure _ hc1 (fun N => (hall N).1),
    nzApprox_closure _ hc2 (fun N => (hall N).2)⟩

/-! ### The conditional theorem -/

/-- **`NearLerayNonzeroMode` from the four lemma Props (proved).** -/
theorem nearLerayNonzeroMode_of (hT : NzTruncApprox) (hP : NzFinPotentials)
    (hM : NzFlatMembership) (hD : NzCutoffApprox) : NearLerayNonzeroMode := by
  unfold NearLerayNonzeroMode
  intro hgrad hstream
  exact nzDensity hT (nearLerayFin_of hP hM hD hgrad hstream)

end UnforcedLeray.Short.PartIIa
