import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The planar reference data of the construction (G1–G4)

`paper/main.tex`, Section `sec:gaussian`, lines 631–800: the Gaussian vortex
`Ω(r) = e^{-r²/4}`, `E₀`, `k = E₀'/r` (`eq:st18-t00001`–`t00002`), the Gaussian space `X_G`
and its pairing (`eq:st18-t00005`), the angular-two generator `L₀ = -2iΩ + 2ikR` with the
Green inverse `R = Δ₂⁻¹` (`eq:st18-t00006`–`t00007`), Theorem G1 (`thm:ref-planar-pair`,
`eq:st18-t00008`), the oscillator `D` and the drift exponent `κ = ℓ(Dq)` (G3a,
`eq:st18-t00011`–`t00012`), the canonical branch (G3b, `eq:st18-t00013`, `eq:st18-t00321`),
and the couplings `𝓛`, `𝓙` of G4 (`eq:st18-t00016`–`t00018`, `eq:st18-t00377`). The signed
reference coefficient is `eq:m2-signed-invariant` (line 13217), and `N_ν = e^{λ/ν}ν^{-κ}`
(line 789). Blueprint units: B0085, B0882 (the reference choice), with the G1–G4 units of
Section `sec:gaussian`.

This module only defines objects and characterizing predicates; it proves nothing about
existence. The construction's planar data (`PlanarData`) are pinned by
`IsPlanarReference`: `λ` is an eigenvalue of the explicit `L₀` in the open right half-plane
with a nonzero `X_G` eigenvector (by G1 there is exactly one, so this is G1's `λ`), `q†` is a
left eigenvector normalized by `⟨q,q†⟩ = 1`, and `V_can` solves the canonical equation with
G3b's asymptotics. The remaining freedom is the eigenvector gauge `q ↦ cq`, `q† ↦ q†/c̄`,
which the manuscript also leaves to a choice (line 636: "the fixed eigenvector gauge"); `κ`
and `𝓒 = (63πi/128)𝓛𝓙` do not depend on it.

Junk values: every improper integral below is either guarded by an integrability clause of
`IsPlanarReference` or converges for every `X_G` profile (Cauchy–Schwarz against the
Gaussian weight), so no clause can hold through Lean's value `0` for a divergent integral.
`λ^{μ+5/2}` is the principal power, which is the right-half-plane power of the manuscript
because `Re λ > 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Complex
open scoped ContDiff Topology ComplexConjugate

namespace UnforcedLeray.Blueprint.Planar

/-- An angular-two radial profile `f₂`, standing for `f₂(r)e^{2iϑ}`. -/
abbrev Profile := ℝ → ℂ

/-- `Ω(r) = e^{-r²/4}` (line 639). -/
def vortexOmega (r : ℝ) : ℝ := Real.exp (-(r ^ 2) / 4)

/-- `k(r) = E₀'(r)/r = (r²/4 - 2)e^{-r²/4}` (`eq:st18-t00002`). -/
def strainK (r : ℝ) : ℝ := (r ^ 2 / 4 - 2) * Real.exp (-(r ^ 2) / 4)

/-- The inverse Gaussian weight `G(r)⁻¹ = 4π e^{r²/4}` (`eq:st18-t00002`). -/
def gaussianWeightInv (r : ℝ) : ℝ := 4 * Real.pi * Real.exp (r ^ 2 / 4)

/-- Membership in `X_G` (`eq:st18-t00005`): `∫₀^∞ |f₂|² G⁻¹ r dr < ∞`. -/
structure MemXG (f : Profile) : Prop where
  measurable : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ)))
  integrable : IntegrableOn (fun r : ℝ => ‖f r‖ ^ 2 * gaussianWeightInv r * r) (Ioi 0)

/-- The `X_G` pairing, linear in the first variable, without the angular factor `2π`
(line 676). -/
def gaussianPairing (f g : Profile) : ℂ :=
  ∫ r in Ioi (0 : ℝ), f r * conj (g r) * ((gaussianWeightInv r * r : ℝ) : ℂ)

/-- The `X_G` norm. Consumers apply it only to `X_G` profiles. -/
def gaussianNorm (f : Profile) : ℝ :=
  Real.sqrt (∫ r in Ioi (0 : ℝ), ‖f r‖ ^ 2 * gaussianWeightInv r * r)

/-- The regular-at-zero, decaying Green inverse `R = Δ₂⁻¹` of `eq:st18-t00007`:
`Rf(r) = -¼[r⁻²∫₀^r s³f(s)ds + r²∫_r^∞ s⁻¹f(s)ds]`. Both integrals converge for every `X_G`
profile and `r > 0`. -/
def greenInverse (f : Profile) (r : ℝ) : ℂ :=
  -(1 / 4 : ℂ) * (((r : ℂ) ^ 2)⁻¹ * (∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * f s) +
    (r : ℂ) ^ 2 * ∫ s in Ioi r, (s : ℂ)⁻¹ * f s)

/-- The angular-two generator `L₀f = -2iΩf + 2ikRf` (`eq:st18-t00006`). -/
def generatorL0 (f : Profile) (r : ℝ) : ℂ :=
  -2 * I * (vortexOmega r : ℂ) * f r + 2 * I * (strainK r : ℂ) * greenInverse f r

/-- The oscillator `D = Δ + ½y·∇ + 2` (`eq:st18-t00011`) on `f₂(r)e^{2iϑ}`:
`f₂'' + f₂'/r - 4f₂/r² + ½rf₂' + 2f₂`. -/
def oscillatorD (f : Profile) (r : ℝ) : ℂ :=
  deriv (deriv f) r + deriv f r / r - 4 * f r / (r : ℂ) ^ 2 + (r / 2 : ℂ) * deriv f r + 2 * f r

/-- The profile `r²k(r)` of the harmonic-strain input `H = r²k(r)e^{2iϑ}` (`eq:st18-t00016`). -/
def strainProfile (r : ℝ) : ℂ := ((r ^ 2 * strainK r : ℝ) : ℂ)

/-- The quadrupole `𝔐(f) = ∫₀^∞ r³f₂(r)dr` (`eq:st18-t00009`). -/
def quadrupole (f : Profile) : ℂ := ∫ r in Ioi (0 : ℝ), (r : ℂ) ^ 3 * f r

/-! ## The characterizing predicates -/

/-- G1 (`thm:ref-planar-pair`) in the angular sector `2`: `λ` is an eigenvalue of `L₀` in the
open right half-plane with a smooth nonzero eigenvector `q ∈ X_G`. G1 says there is exactly
one such eigenvalue in sector `2`, so this pins `λ = γ + iω`. -/
structure IsGrowingEigenpair (eigenvalue : ℂ) (q : Profile) : Prop where
  re_pos : 0 < eigenvalue.re
  memXG : MemXG q
  nonzero : ¬ q =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0
  smooth : ContDiffOn ℝ ∞ q (Ioi 0)
  eigen : ∀ r : ℝ, 0 < r → generatorL0 q r = eigenvalue * q r

/-- G3a (`eq:st18-t00012`): `q†` is the `X_G`-adjoint eigenvector, so that
`ℓ = ⟨·, q†⟩_{X_G}` satisfies `ℓ(L₀f) = λℓ(f)` on `X_G`, normalized by `ℓ(q) = 1`. -/
structure IsAdjointEigenvector (eigenvalue : ℂ) (q qdag : Profile) : Prop where
  memXG : MemXG qdag
  left_eigen : ∀ f : Profile, MemXG f →
    gaussianPairing (generatorL0 f) qdag = eigenvalue * gaussianPairing f qdag
  normalized : gaussianPairing q qdag = 1

/-- G3b (`eq:st18-t00013`, `eq:st18-t00321`): the canonical branch `V_can` solves
`-∂_θV = (L₀ + θ⁻¹D)V` on `θ > 0`, is smooth there and bounded in `X_G` near zero, and
`V_can(θ) = e^{-λθ}θ^{-κ}(q + O_{X_G}(θ⁻¹))`. -/
structure IsCanonicalBranch (eigenvalue κ : ℂ) (q : Profile) (V : ℝ → Profile) : Prop where
  memXG : ∀ θ : ℝ, 0 < θ → MemXG (V θ)
  smooth : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => V z.1 z.2) (Ioi 0 ×ˢ Ioi 0)
  equation : ∀ θ : ℝ, 0 < θ → ∀ r : ℝ, 0 < r →
    -deriv (fun t => V t r) θ = generatorL0 (V θ) r + (θ : ℂ)⁻¹ * oscillatorD (V θ) r
  bounded_near_zero : ∃ C : ℝ, ∀ θ : ℝ, 0 < θ → θ ≤ 1 → gaussianNorm (V θ) ≤ C
  asymptotic : ∃ C θ₁ : ℝ, 0 < θ₁ ∧ ∀ θ : ℝ, θ₁ ≤ θ →
    gaussianNorm (fun r => exp (eigenvalue * θ) * (θ : ℂ) ^ κ * V θ r - q r) ≤ C / θ
  xg_continuous : ∀ θ₀ : ℝ, 0 < θ₀ →
    Tendsto (fun θ => gaussianNorm (fun r => V θ r - V θ₀ r)) (𝓝 θ₀) (𝓝 0)

/-- The planar data of the construction: `λ`, the eigenvector `q`, the adjoint eigenvector
`q†` and the canonical branch `V_can`. -/
structure PlanarData where
  /-- `λ = γ + iω` (`eq:st18-t00008`). -/
  eigenvalue : ℂ
  /-- The radial profile of the eigenvorticity `q = h(r)e^{2iϑ}`. -/
  mode : Profile
  /-- The profile of the `X_G`-adjoint eigenvector `q†`. -/
  adjointMode : Profile
  /-- The canonical branch `θ ↦ V_can(θ)` (G3b). -/
  canonical : ℝ → Profile

namespace PlanarData

variable (P : PlanarData)

/-- `κ = ℓ(Dq)` (`eq:st18-t00012`). -/
def kappa : ℂ := gaussianPairing (oscillatorD P.mode) P.adjointMode

/-- `ℓ(H)` (G4). -/
def strainCoupling : ℂ := gaussianPairing strainProfile P.adjointMode

/-- `𝓛(μ) = ℓ(H)Γ(μ+5/2)/λ^{μ+5/2}` (`eq:st18-t00018`, `eq:affine-4-106`). -/
def couplingL (μ : ℝ) : ℂ :=
  P.strainCoupling * Gamma ((μ : ℂ) + 5 / 2) / P.eigenvalue ^ ((μ : ℂ) + 5 / 2)

/-- `𝓙(μ) = ∫₀^∞ θ^{μ+1/2}𝔐(V_can(θ))dθ` (`eq:st18-t00017`, `eq:st18-t00377`). -/
def mellinJ (μ : ℝ) : ℂ :=
  ∫ θ in Ioi (0 : ℝ), ((θ ^ (μ + 1 / 2) : ℝ) : ℂ) * quadrupole (P.canonical θ)

/-- The signed reference coefficient `𝓒(μ) = (63πi/128)𝓛(μ)𝓙(μ)`
(`eq:m2-signed-invariant`, `eq:st18-t00754`). -/
def signedCoeff (μ : ℝ) : ℂ :=
  (63 * Real.pi * I / 128) * P.couplingL μ * P.mellinJ μ

/-- `N_ν = e^{λ/ν}ν^{-κ}` (line 789), with the real logarithm of `ν > 0`. -/
def gaugeFactor (ν : ℝ) : ℂ := exp (P.eigenvalue / ν) * (ν : ℂ) ^ (-P.kappa)

end PlanarData

/-- G1–G4 for one planar data record: the eigenpair (G1), the adjoint eigenvector and the
domain of `D` (G3a), the canonical branch (G3b), and the convergence of the integrals that
define `𝓙` on `Re μ > -3/2` (G4). -/
structure IsPlanarReference (P : PlanarData) : Prop where
  eigenpair : IsGrowingEigenpair P.eigenvalue P.mode
  adjoint : IsAdjointEigenvector P.eigenvalue P.mode P.adjointMode
  oscillator_memXG : MemXG (oscillatorD P.mode)
  canonical : IsCanonicalBranch P.eigenvalue P.kappa P.mode P.canonical
  moment_integrable : ∀ θ : ℝ, 0 < θ →
    IntegrableOn (fun r : ℝ => (r : ℂ) ^ 3 * P.canonical θ r) (Ioi 0)
  mellin_integrable : ∀ μ : ℝ, -(3 / 2) < μ →
    IntegrableOn (fun θ : ℝ => ((θ ^ (μ + 1 / 2) : ℝ) : ℂ) * quadrupole (P.canonical θ))
      (Ioi 0)

/-! ## Continuity of `𝓛` (proved) -/

/-- `𝓛` is continuous at every `μ > -5/2` when `λ ≠ 0`: `Γ` has no pole at `μ + 5/2` and the
power `λ^z` is continuous in `z`. -/
theorem PlanarData.continuousAt_couplingL (P : PlanarData) (hlam : P.eigenvalue ≠ 0) {μ : ℝ}
    (hμ : -(5 / 2) < μ) : ContinuousAt P.couplingL μ := by
  have hz : ContinuousAt (fun x : ℝ => (x : ℂ) + 5 / 2) μ :=
    (continuous_ofReal.add continuous_const).continuousAt
  have hpole : ∀ m : ℕ, (μ : ℂ) + 5 / 2 ≠ -m := by
    intro m h
    have h' := congrArg Complex.re h
    simp only [add_re, ofReal_re, neg_re, natCast_re] at h'
    have : (5 / 2 : ℂ).re = 5 / 2 := by norm_num
    rw [this] at h'
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hG : ContinuousAt (fun x : ℝ => Gamma ((x : ℂ) + 5 / 2)) μ :=
    ContinuousAt.comp (g := Gamma) (differentiableAt_Gamma _ hpole).continuousAt hz
  have hpow : ContinuousAt (fun x : ℝ => P.eigenvalue ^ ((x : ℂ) + 5 / 2)) μ :=
    ContinuousAt.comp (g := fun z : ℂ => P.eigenvalue ^ z) (continuousAt_const_cpow hlam) hz
  have hne : P.eigenvalue ^ ((μ : ℂ) + 5 / 2) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]
    exact fun h => hlam h.1
  exact (continuousAt_const.mul hG).div hpow hne

end UnforcedLeray.Blueprint.Planar
