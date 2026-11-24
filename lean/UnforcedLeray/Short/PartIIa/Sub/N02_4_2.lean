import UnforcedLeray.Short.PartIIa.Sub.N02_4

/-!
# Part II-a, task `PartII-a:N02/4/2` (`NzTruncApprox`): decomposition into three lemma Props

Source of record: `the November 2 reference manuscript`, lines 1744-1749 ("Initially use
finite Fourier sums, compact log-age support and Schwartz transverse profiles. ... Cutoff, mollification
and Fourier truncation are dense in the displayed norm").

For a smooth test `f` (smooth, `c`-periodic in `q`, compact in the `(s, η)`-band) let
`a_n(s, η) = c⁻¹ ∫_0^c e^{-2π i n q / c} f(s, q, η) dq` (`nzCoeff`) and
`f_N = Σ_{0 < |n| ≤ N} e^{2π i n q / c} a_n(s, η)` (`nzTrunc`). Three facts give `NzTruncApprox`:

* `NzTruncTest`: `f_N` is a finite-mode zero-mean smooth test (parametric integral over the compact
  interval `[0, c]`; the coefficients are supported in the band of `f`);
* `NzTruncMoment`: `nzMomSum c f_N ≤ nzMomSum c f` (`S` and `η` commute with the `q`-coefficients,
  Bessel's inequality in `q` at each `(s, η)`, via `NzQParseval` for `f_N`);
* `NzTruncConverge`: the classes of `f_N` converge to the class of `f` in `H` (Fourier series in `q`
  converge in `L²(dq)` at each `(s, η)`, dominated by `∫_0^c ‖f‖² dq`).

`nzTruncApprox_of` (proved here) assembles `NzTruncApprox`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- The `n`-th `q`-Fourier coefficient `c⁻¹ ∫_0^c e^{-2π i n q / c} f(s, q, η) dq` of a profile, as a
function of `(s, η)`. -/
def nzCoeff (c : ℝ) (n : ℤ) (f : Profile → MeridC) (x : ℝ × ℝ) : MeridC :=
  ((1 / c : ℝ) : ℂ) • ∫ q in (0 : ℝ)..c,
    Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))) •
      f (x.1, q, x.2)

/-- The Fourier truncation `Σ_{0 < |n| ≤ N} e^{2π i n q / c} a_n(s, η)` of a profile. -/
def nzTrunc (c : ℝ) (N : ℕ) (f : Profile → MeridC) : Profile → MeridC := fun p =>
  ∑ n ∈ (Finset.Icc (-(N : ℤ)) N).erase 0,
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) •
      nzCoeff c n f (p.1, p.2.2)

/-- **Lemma NzTruncTest: truncations are finite-mode zero-mean tests.** For a smooth test `f`, each
`f_N` is an `IsMeridTest` with zero `q`-mean and finitely many `q`-modes (`M = {0 < |n| ≤ N}`,
`a_n = nzCoeff c n f`). Smoothness of `a_n`: smoothness of a parametric integral over the compact
interval `[0, c]` (grep `contDiffOn_integral` in `Loc/L09CompactDatum/ParamIntegral.lean`, and the
analogous smoothness of the `q`-average `avgQ` in `Tasks/N02LerayComparison/ModeSplit.lean`); the support of `a_n` lies in the `(s, η)`-band of `f`; periodicity and zero
mean are those of the exponentials `e^{2π i n q / c}`, `n ≠ 0`. -/
def NzTruncTest : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (f : Profile → MeridC), IsMeridTest c f → QMeanZero c f →
    ∀ N : ℕ, IsMeridTest c (nzTrunc c N f) ∧ QMeanZero c (nzTrunc c N f) ∧
      NzFinModes c (nzTrunc c N f)

/-- **Lemma NzTruncMoment: truncation does not increase the moment sum.** `S` and `η` commute with the
`q`-coefficients (differentiation under the integral sign in `s`), and for each `(s, η)` Bessel's
inequality in `q` gives `∫_0^c ‖S^a f_N‖² dq = c Σ_{0<|n|≤N} ‖a_n(S^a f)‖² ≤ ∫_0^c ‖S^a f‖² dq`
(the first equality is `NzQParseval`); then integrate against `(|η|^j)² s^{-3/2} ds dη`. -/
def NzTruncMoment : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (f : Profile → MeridC), IsMeridTest c f → QMeanZero c f →
    ∀ N : ℕ, nzMomSum c (nzTrunc c N f) ≤ nzMomSum c f

/-- **Lemma NzTruncConverge: the truncations converge in `H`.** If `F` is a class of the smooth test
`f` with zero `q`-mean, there are classes `F_N` of `f_N` with `F_N → F` in `H = L²(measureH c; ℂ²)`.
At each `(s, η)` the partial Fourier sums of the smooth periodic function `q ↦ f(s, q, η)` converge in
`L²(0, c)` (Mathlib: `hasSum_fourier_series_L2`, `tsum_sq_fourierCoeff`), with squared error at most
`∫_0^c ‖f‖² dq`, which is integrable against `s^{-3/2} ds dη` (compact support); dominated
convergence. -/
def NzTruncConverge : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (f : Profile → MeridC), IsMeridTest c f → QMeanZero c f →
    ∀ (F : HSpace c MeridC), (F : Profile → MeridC) =ᵐ[measureH c] f →
    ∃ FN : ℕ → HSpace c MeridC,
      (∀ N, (FN N : Profile → MeridC) =ᵐ[measureH c] nzTrunc c N f) ∧
      Tendsto FN atTop (𝓝 F)

/-- **`NzTruncApprox` from the three Props (proved).** -/
theorem nzTruncApprox_of (h1 : NzTruncTest) (h2 : NzTruncMoment) (h3 : NzTruncConverge) :
    NzTruncApprox := by
  intro c hc f hf hT F hF
  obtain ⟨FN, hFN, hlim⟩ := h3 c hc f hf hT F hF
  refine ⟨fun N => nzTrunc c N f, FN, fun N => ?_, hlim⟩
  obtain ⟨ha, hb, hd⟩ := h1 c hc f hf hT N
  exact ⟨ha, hb, hd, hFN N, h2 c hc f hf hT N⟩

end UnforcedLeray.Short.PartIIa
