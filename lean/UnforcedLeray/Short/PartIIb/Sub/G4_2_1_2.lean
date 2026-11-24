import UnforcedLeray.Short.PartIIb.Sub.G4_2_1

/-!
# Part II-b, task `PartII-b:G4/2/1/2` (`GreenInverseSqSmooth`): decomposition into leaves

Source: `the November 2 reference manuscript`
lines 2347-2352.

Write `G = greenInverse q`, `u = r²`, `g(u) = G(√u)/u`.  The formula for `greenInverse`
gives `G'' + G'/r - 4G/r² = q`, and the eigen equation `-2iΩq + 2ikG = λq` gives `q = a G` with
`a(r) = 2ik(r)/(λ+2iΩ(r))` (`Re λ > 0`, so `|λ+2iΩ| ≥ Re λ`).  In the variable `u = r²` with
`G = u g(u)`, the equation reads `u g'' + 3 g' = (a/4) g`, i.e. `(u³ g')' = (u²a/4) g`.  The
solution regular at `0` therefore satisfies the Volterra equation
`g(u) = c + ∫₀^u ¼ ∫₀¹ t² (a g)(v t) dt dv`  (initial-value type, `c = g 0`).  That equation
makes sense and has a unique solution on all of `ℝ` (this is what extends `g` to `u < 0`), and
continuous solutions are `C^∞` by bootstrapping `g ∈ C^k ⇒ g' ∈ C^k`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

/-- The eigen-coefficient `a` as a function of `u = r²`:
`a(u) = 2i (u/4 - 2) e^{-u/4} / (λ + 2i e^{-u/4})`. -/
def sqCoeff (lam : ℂ) (u : ℝ) : ℂ :=
  2 * Complex.I * (((u / 4 - 2) * Real.exp (-u / 4) : ℝ) : ℂ) /
    (lam + 2 * Complex.I * ((Real.exp (-u / 4) : ℝ) : ℂ))

/-- The Volterra right-hand side `c + ∫₀^u ¼ ∫₀¹ t² a(vt) p(vt) dt dv`. -/
def sqVolterra (lam c : ℂ) (p : ℝ → ℂ) (u : ℝ) : ℂ :=
  c + ∫ v in (0 : ℝ)..u, (1 / 4 : ℂ) * ∫ t in (0 : ℝ)..1,
    (t : ℂ) ^ 2 * (sqCoeff lam (v * t) * p (v * t))

/-- **Leaf 1** (continuity of `g(u) = G(√u)/u` up to `u = 0`; SP 2347-2352).  Under the
`O(r²)` bound, `g` is bounded on `(0,1]` and has a limit at `0⁺`: from the integral formula and
`q = aG`, `g(u) = -¼[(u/2)∫₀¹ t² h(ut)dt + ½∫_u^∞ h]` with `h = a g` bounded and (for large `u`)
exponentially small, so the limit `-⅛∫₀^∞ h` exists. -/
def GreenSqContinuous : Prop :=
  ∀ (lam : ℂ) (q : Planar.Profile), Planar.IsGrowingEigenpair lam q →
    (∃ C : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 → ‖Planar.greenInverse q r‖ ≤ C * r ^ 2) →
    ∃ g : ℝ → ℂ, ContinuousOn g (Ici 0) ∧
      ∀ u : ℝ, 0 < u → g u = Planar.greenInverse q (Real.sqrt u) / (u : ℂ)

/-- **Leaf 2** (the ODE in integral form; SP 2347-2352): any continuous-on-`[0,∞)` extension `g`
of `u ↦ G(√u)/u` satisfies the Volterra equation with `c = g 0`.  Differentiating the formula for
`G` twice gives `u g' = ... `, precisely `g'(u) = u⁻³∫₀^u s² (a g)(s)/4 ds = ¼∫₀¹ t²(ag)(ut)dt`
for `u > 0`; integrate from `0` using continuity at `0`. -/
def GreenSqVolterra : Prop :=
  ∀ (lam : ℂ) (q : Planar.Profile), Planar.IsGrowingEigenpair lam q →
    (∃ C : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 → ‖Planar.greenInverse q r‖ ≤ C * r ^ 2) →
    ∀ g : ℝ → ℂ, ContinuousOn g (Ici 0) →
      (∀ u : ℝ, 0 < u → g u = Planar.greenInverse q (Real.sqrt u) / (u : ℂ)) →
      ∃ c : ℂ, ∀ u : ℝ, 0 ≤ u → g u = sqVolterra lam c g u

/-- **Leaf 3** (existence on all of `ℝ`, Picard iteration with `sup |a| ≤ C` on compacts). -/
def SqVolterraExists : Prop :=
  ∀ (lam c : ℂ), 0 < lam.re → ∃ p : ℝ → ℂ, Continuous p ∧ ∀ u : ℝ, p u = sqVolterra lam c p u

/-- **Leaf 4** (bootstrap): a continuous solution of the Volterra equation on `ℝ` is `C^∞`;
`p' = ¼∫₀¹ t²(ap)(ut)dt` is `C^k` whenever `p` is (differentiation under the integral;
`a` is smooth on `ℝ` because `Re(λ+2ie^{-u/4}) = Re λ > 0`... the real part of the denominator is
`Re λ`, hence nonzero). -/
def SqVolterraSmooth : Prop :=
  ∀ (lam c : ℂ), 0 < lam.re → ∀ p : ℝ → ℂ, Continuous p →
    (∀ u : ℝ, p u = sqVolterra lam c p u) → ContDiff ℝ ∞ p

/-- **Leaf 5** (uniqueness on `[0,∞)`): two continuous-on-`[0,∞)` solutions of the same Volterra
equation agree on `[0,∞)` (Gronwall: `|d(u)| ≤ ¼ sup|a| ∫₀^u sup_{[0,v]}|d|`, `a` bounded since
`|λ+2iΩ| ≥ Re λ`). -/
def SqVolterraUnique : Prop :=
  ∀ (lam c : ℂ), 0 < lam.re → ∀ g p : ℝ → ℂ, ContinuousOn g (Ici 0) → ContinuousOn p (Ici 0) →
    (∀ u : ℝ, 0 ≤ u → g u = sqVolterra lam c g u) →
    (∀ u : ℝ, 0 ≤ u → p u = sqVolterra lam c p u) → ∀ u : ℝ, 0 ≤ u → g u = p u

/-- Assembly of `GreenInverseSqSmooth` from the five leaves. -/
theorem greenInverseSqSmooth_of (h1 : GreenSqContinuous) (h2 : GreenSqVolterra)
    (h3 : SqVolterraExists) (h4 : SqVolterraSmooth) (h5 : SqVolterraUnique) :
    GreenInverseSqSmooth := by
  intro lam q h hO
  obtain ⟨g, hgc, hg⟩ := h1 lam q h hO
  obtain ⟨c, hc⟩ := h2 lam q h hO g hgc hg
  obtain ⟨p, hpc, hp⟩ := h3 lam c h.re_pos
  refine ⟨p, h4 lam c h.re_pos p hpc hp, ?_⟩
  intro r hr
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  have hsq : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr.le
  have hgp := h5 lam c h.re_pos g p hgc hpc.continuousOn hc (fun u _ => hp u) (r ^ 2) hr2.le
  have := hg (r ^ 2) hr2
  rw [hsq] at this
  rw [← hgp, this]
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast
  field_simp

end UnforcedLeray.Short.IIb
