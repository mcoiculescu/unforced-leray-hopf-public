import UnforcedLeray.Short.PartIIb.Sub.G4_2_2

/-!
# PartII-b:G4/2/2/1, /2, /3 — shared Gaussian-calculus lemmas for the planar quadrupole split

Source: the November 2 reference manuscript
lines 2349-2352 (planar eigenstream = harmonic quadrupole + Gaussian remainder).

This file holds the shared definitions (`GaussAt`, `PolyAt`, `aCoef`) and the shared Props used to
decompose `EigenGaussDecay` (this file, `eigenGaussDecay_of`), `GreenRemDecay` and
`GreenRemSmooth` (files `G4_2_2_2.lean`, `G4_2_2_3.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

/-- `j`-th derivative of `f` is Gaussian bounded on `[1, ∞)`. -/
def GaussAt (f : ℝ → ℂ) (j : ℕ) : Prop :=
  ∃ (C κ : ℝ), 0 < κ ∧ ∀ r : ℝ, 1 ≤ r → ‖iteratedDeriv j f r‖ ≤ C * Real.exp (-(κ * r ^ 2))

/-- `j`-th derivative of `f` is polynomially bounded on `[1, ∞)`. -/
def PolyAt (f : ℝ → ℂ) (j : ℕ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), ∀ r : ℝ, 1 ≤ r → ‖iteratedDeriv j f r‖ ≤ C * r ^ N

/-- The eigen-ratio `a(r) = 2ik(r)/(λ + 2iΩ(r))`, so that an eigenprofile satisfies
`q = a · R q` (source lines 2349-2352; `k = (r²/4-2)e^{-r²/4}`, `Ω = e^{-r²/4}`). -/
def aCoef (lam : ℂ) (r : ℝ) : ℂ :=
  2 * Complex.I * (Planar.strainK r : ℂ) / (lam + 2 * Complex.I * (Planar.vortexOmega r : ℂ))

/-- Leibniz bound: `f` smooth on `(0,∞)` with Gaussian bounded derivatives (orders `< n`), `g`
smooth on `(0,∞)` with polynomially bounded derivatives (orders `< n`); then `f g` has Gaussian
bounded derivatives of orders `< n` (Leibniz rule, `Nat.choose` sum, absorb `r^N` into the
Gaussian by lowering `κ`). -/
def GaussMulPoly : Prop :=
  ∀ (f g : ℝ → ℂ) (n : ℕ), ContDiffOn ℝ ∞ f (Ioi 0) → ContDiffOn ℝ ∞ g (Ioi 0) →
    (∀ j < n, GaussAt f j) → (∀ j < n, PolyAt g j) →
      ∀ j < n, GaussAt (fun r => f r * g r) j

/-- Linear combinations of Gaussian bounded functions (take the smaller `κ`). -/
def GaussLin : Prop :=
  ∀ (a b : ℂ) (f g : ℝ → ℂ) (n : ℕ), ContDiffOn ℝ ∞ f (Ioi 0) → ContDiffOn ℝ ∞ g (Ioi 0) →
    (∀ j < n, GaussAt f j) → (∀ j < n, GaussAt g j) →
      ∀ j < n, GaussAt (fun r => a * f r + b * g r) j

/-- The functions `r ↦ r^m` (`m ∈ ℤ`, complex powers of real `r`) are smooth on `(0,∞)` with
polynomially bounded derivatives on `[1,∞)`. -/
def PolyZpow : Prop :=
  ∀ m : ℤ, ContDiffOn ℝ ∞ (fun r : ℝ => (r : ℂ) ^ m) (Ioi 0) ∧
    ∀ j : ℕ, PolyAt (fun r : ℝ => (r : ℂ) ^ m) j

/-- Tail integrals of a smooth Gaussian-decaying function are smooth on `(0,∞)` and Gaussian
bounded on `[1,∞)` (all derivatives: `d/dr ∫_r^∞ s^k q = -r^k q`, then Leibniz-free induction;
for the zeroth order `∫_r^∞ s^k e^{-κ s²} ≤ C e^{-κ r²/2}`). -/
def GaussTail : Prop :=
  ∀ (q : ℝ → ℂ) (k : ℤ), ContDiffOn ℝ ∞ q (Ioi 0) → (∀ j : ℕ, GaussAt q j) →
    ContDiffOn ℝ ∞ (fun r : ℝ => ∫ s in Ioi r, (s : ℂ) ^ k * q s) (Ioi 0) ∧
      ∀ j : ℕ, GaussAt (fun r : ℝ => ∫ s in Ioi r, (s : ℂ) ^ k * q s) j

/-- For `q ∈ X_G`: `s³ q` is integrable on `(0,∞)` and `s⁻¹ q` is integrable on `(r,∞)`, `r>0`
(AM-GM: `|q| s³ ≤ (|q|² s e^{s²/4} + s⁵ e^{-s²/4})/2`,
`|q| s⁻¹ ≤ (|q|² s e^{s²/4} + s⁻³ e^{-s²/4})/2`). -/
def XGInt : Prop :=
  ∀ q : Planar.Profile, Planar.MemXG q →
    IntegrableOn (fun s : ℝ => (s : ℂ) ^ 3 * q s) (Ioi 0) ∧
      ∀ r : ℝ, 0 < r → IntegrableOn (fun s : ℝ => (s : ℂ)⁻¹ * q s) (Ioi r)

/-- Tail form of the Green remainder for `q ∈ X_G` (the `M r⁻²` term cancels against the
`∫₀^r` part; uses `XGInt`):
`greenRem q r = ¼ r⁻² ∫_r^∞ s³ q - ¼ r² ∫_r^∞ s⁻¹ q`. -/
def GreenRemTail : Prop :=
  ∀ q : Planar.Profile, Planar.MemXG q → ∀ r : ℝ, 0 < r →
    greenRem q r = (1 / 4 : ℂ) * (((r : ℂ) ^ 2)⁻¹ * ∫ s in Ioi r, (s : ℂ) ^ 3 * q s) -
      (1 / 4 : ℂ) * ((r : ℂ) ^ 2 * ∫ s in Ioi r, (s : ℂ)⁻¹ * q s)

/-- `r ↦ ∫₀^r s³ q` is smooth on `(0,∞)` for smooth `q ∈ X_G`
(`intervalIntegral.integral_hasDerivAt_right`, derivative `r³ q`, induction). -/
def SmoothA : Prop :=
  ∀ q : Planar.Profile, Planar.MemXG q → ContDiffOn ℝ ∞ q (Ioi 0) →
    ContDiffOn ℝ ∞ (fun r : ℝ => ∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * q s) (Ioi 0)

/-- `r ↦ ∫_r^∞ s⁻¹ q` is smooth on `(0,∞)` for smooth `q ∈ X_G` (derivative `-r⁻¹ q`). -/
def SmoothB : Prop :=
  ∀ q : Planar.Profile, Planar.MemXG q → ContDiffOn ℝ ∞ q (Ioi 0) →
    ContDiffOn ℝ ∞ (fun r : ℝ => ∫ s in Ioi r, (s : ℂ)⁻¹ * q s) (Ioi 0)

/-- Eigen algebra: from `-2iΩq + 2ik R q = λ q` and `Re λ > 0` (so `λ + 2iΩ ≠ 0`),
`q r = aCoef λ r * greenInverse q r` for `r > 0`. -/
def EigenRep : Prop :=
  ∀ (lam : ℂ) (q : Planar.Profile), Planar.IsGrowingEigenpair lam q →
    ∀ r : ℝ, 0 < r → q r = aCoef lam r * Planar.greenInverse q r

/-- For `Re λ > 0`, `aCoef λ` is smooth on `(0,∞)` (even on `ℝ`: the denominator has real part
`Re λ`) and all its derivatives are Gaussian bounded on `[1,∞)` (`κ = 1/8` after absorbing
polynomial factors; derivatives of `(λ+2iΩ)⁻¹` are polynomially bounded). -/
def ACoefGauss : Prop :=
  ∀ lam : ℂ, 0 < lam.re → ContDiffOn ℝ ∞ (aCoef lam) (Ioi 0) ∧
    ∀ j : ℕ, GaussAt (aCoef lam) j

/-- Bootstrap step: for an eigenpair, if the derivatives of `q` of orders `< j` are Gaussian
bounded then the `j`-th derivative of `R q` is polynomially bounded on `[1,∞)`. For `j = 0`:
`|R q| ≤ C` by the two integrals; for `j ≥ 1`:
`(R q)' = ½ (r⁻³ ∫₀^r s³ q - r ∫_r^∞ s⁻¹ q)` and `(∫₀^r s³ q)' = r³ q`,
`(∫_r^∞ s⁻¹ q)' = -r⁻¹ q`. -/
def RqPolyAt : Prop :=
  ∀ (lam : ℂ) (q : Planar.Profile), Planar.IsGrowingEigenpair lam q → ∀ j : ℕ,
    (∀ i < j, GaussAt q i) → PolyAt (Planar.greenInverse q) j

/-- **`PartII-b:G4/2/2/1`** reduction of `EigenGaussDecay` to the Props above:
`q = a · R q`, `R q` smooth with polynomial derivative bounds (induction on the order) and `a`
Gaussian. -/
theorem eigenGaussDecay_of (hRep : EigenRep) (hA : ACoefGauss) (hP : RqPolyAt)
    (hMul : GaussMulPoly) (h3 : GreenRemSmooth) (hZ : PolyZpow) : EigenGaussDecay := by
  intro lam q hq
  have hGI : ContDiffOn ℝ ∞ (Planar.greenInverse q) (Ioi 0) := by
    have h1 := h3 lam q hq
    have h2 := (hZ (-2)).1
    have hfun : Set.EqOn (Planar.greenInverse q)
        (fun r : ℝ => greenRem q r +
          (-(1 / 4 : ℂ) * Planar.quadrupole q) * (r : ℂ) ^ (-2 : ℤ)) (Ioi 0) := by
      intro r _
      simp [greenRem, zpow_neg]
    exact ContDiffOn.congr (h1.add (contDiffOn_const.mul h2)) hfun
  have key : ∀ n : ℕ, ∀ j < n, GaussAt q j := by
    intro n
    induction n with
    | zero => intro j hj; omega
    | succ n ih =>
      have hPoly : ∀ j < n + 1, PolyAt (Planar.greenInverse q) j := fun j hj =>
        hP lam q hq j (fun i hi => ih i (by omega))
      have hm := hMul (aCoef lam) (Planar.greenInverse q) (n + 1) (hA lam hq.re_pos).1 hGI
        (fun j _ => (hA lam hq.re_pos).2 j) hPoly
      intro j hj
      obtain ⟨C, κ, hκ, hb⟩ := hm j hj
      refine ⟨C, κ, hκ, fun r hr => ?_⟩
      have heq : q =ᶠ[𝓝 r] fun s => aCoef lam s * Planar.greenInverse q s := by
        filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < r by linarith)] with s hs
        exact hRep lam q hq s hs
      rw [heq.iteratedDeriv_eq]
      exact hb r hr
  intro j
  exact key (j + 1) j (by omega)

end UnforcedLeray.Short.IIb
