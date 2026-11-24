import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Leaves

/-!
# Decomposition of `VorticityToVelocity` (source 3511-3514, 3420-3426, 4610-4612)

Source of record: `the November 2 reference manuscript` (73 pages).

A *stream test* is a smooth time-dependent cylinder test `ζ`, compactly supported in age in
`(0,∞)`; `streamField ζ = ∇^⊥ζ = (-∂_ηζ, ∂_qζ)` (indices `0 = q`, `1 = η`) is then a divergence-free
flat test.  The proof has five steps:

* `VtvStreamFlat` : `∇^⊥ζ` is an `IsFlatTest`;
* `VtvSlice` (pointwise algebra at a.e. fixed age, 3511-3514): the cell integral of
  `forcedIntegrand` against `∇^⊥ζ(s)` equals `streamSlice`
  `= ⟨ω,∂_sζ⟩ - (μ/s)⟨ω,ζ⟩ + ∫flowIntegrand + ⟨g,ζ⟩`;
* `VtvTime` (time Fubini from the integrated Duhamel identity 4610): `∫₀^∞ streamSlice ds = 0`;
* `VtvFubini` : the space-time integral of `forcedIntegrand` is the iterated one;
* `VtvFlux` (the flux cutoff, 3511-3514 "the horizontal mean is retained"): stream tests suffice.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (IsCausalEnergySolution flatIntegrand IsFlatTest IsBiotSavart
  flowIntegrand trainVel)

/-- A stream test: jointly smooth, a cylinder test at every age, vanishing outside an age band
`[s₁, s₂] ⊂ (0,∞)` and outside one `η`-band `|η| ≤ R` uniform in the age (audit fix: a per-slice
band is not enough for `IsFlatTest.support`). -/
def IsStreamTest (c : ℝ) (ζ : ℝ → ℝ × ℝ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (ℝ × ℝ) => ζ p.1 p.2) ∧ (∀ s, B0579.IsCylTest c (ζ s)) ∧
    ∃ s₁ s₂ R : ℝ, 0 < s₁ ∧ ∀ s x, (s < s₁ ∨ s₂ < s ∨ R < |x.2|) → ζ s x = 0

/-- `∇^⊥ζ = (-∂_ηζ, ∂_qζ)` as a time-dependent vector test field. -/
def streamField (ζ : ℝ → ℝ × ℝ → ℝ) (s : ℝ) (x : ℝ × ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then -(B0579.pd 1 (ζ s) x) else B0579.pd 0 (ζ s) x

/-- The tested vorticity equation at age `s` against the stream test `ζ`:
`⟨ω,∂_sζ⟩ - (μ/s)⟨ω,ζ⟩ + ∫ flowIntegrand + ⟨g,ζ⟩` (source 3420-3426, 3511-3514; the curl of the
tested flat equation). -/
def streamSlice {ν c : ℝ} (μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (ζ : ℝ → ℝ × ℝ → ℝ) (s : ℝ) : ℂ :=
  (∫ x in B0579.cell c, ω s x * ((deriv (fun s' => ζ s' x) s : ℝ) : ℂ)) -
    ((μ : ℂ) / (s : ℂ)) * (∫ x in B0579.cell c, ω s x * (ζ s x : ℂ)) +
    (∫ x in B0579.cell c, flowIntegrand tr (ω s) (fun x => b (s, x)) s (ζ s) x) +
    (∫ x in B0579.cell c, g s x * (ζ s x : ℂ))

/-- The hypotheses of `VorticityToVelocity`, bundled.  The sixth clause is the force bound: `f`
is in `L²` on every age band `[s₁, s₂] × cell`, `s₁ > 0` (source 3426-3440: the force of the causal
problem lies in the class `𝒯`, weighted `L²` in age and `L²` on the cell; 3511-3514 "This retains
the horizontal mean": the flux cutoff needs the decay of `f` in `η`).  Local integrability on
`{|η| ≤ R}` alone is NOT enough: with `ω = g = b = 0` and the constant force `f = (1, 0)` every other
clause holds and the weak equation holds against all stream tests, but fails against a flat test
with nonzero flux (the former `VtvFluxRefute`). -/
def VtvHyps (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ) : Prop :=
  0 < ν ∧ 0 < c ∧ UnforcedLeray.Short.PartI.IsBUCTrain tr ∧ IsEnergyField c b G ∧
    (∀ s, 0 < s → IsBiotSavart c (ω s) (fun x => b (s, x))) ∧
    (∀ s₁ s₂ : ℝ, 0 < s₁ → ∀ i,
      MemLp (fun p => f p i) 2 (volume.restrict (Icc s₁ s₂ ×ˢ B0579.cell c))) ∧
    (∀ s, 0 < s → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, g s x * (ψ x : ℂ) =
        ∫ x in B0579.cell c, (f (s, x) 0 * (B0579.pd 1 ψ x : ℂ) -
          f (s, x) 1 * (B0579.pd 0 ψ x : ℂ))) ∧
    (∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest c φ → ∀ s : ℝ, 0 < s →
      IntegrableOn (fun t : ℝ => ((t : ℂ) ^ (μ : ℂ)) *
          ∫ x in B0579.cell c, g t x * (φ x : ℂ)) (Ioc 0 s) ∧
      IntegrableOn (fun r : ℝ => ((r : ℂ) ^ (μ : ℂ)) *
          ∫ x in B0579.cell c, flowIntegrand tr (ω r) (fun x => b (r, x)) r φ x) (Ioc 0 s) ∧
      ((s : ℂ) ^ (μ : ℂ)) * ∫ x in B0579.cell c, ω s x * (φ x : ℂ) =
        (∫ t in Ioc 0 s, ((t : ℂ) ^ (μ : ℂ)) * ∫ x in B0579.cell c, g t x * (φ x : ℂ)) +
        ∫ r in Ioc 0 s, ((r : ℂ) ^ (μ : ℂ)) *
          ∫ x in B0579.cell c, flowIntegrand tr (ω r) (fun x => b (r, x)) r φ x) ∧
    (∀ s, 0 < s → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      IntegrableOn (fun x => ω s x * (ψ x : ℂ)) (B0579.cell c))

/-- **`∇^⊥ζ` is a flat test** (smooth; periodic; support in `s ∈ [s₁,s₂]`, `|η| ≤ R` from the
compact `η`-support of the cylinder test; `div ∇^⊥ζ = -∂_q∂_ηζ + ∂_η∂_qζ = 0`, symmetry of second
derivatives for smooth `ζ`). -/
def VtvStreamFlat : Prop :=
  ∀ (c : ℝ) (ζ : ℝ → ℝ × ℝ → ℝ), IsStreamTest c ζ → IsFlatTest c (streamField ζ)

/-- **The pointwise algebra** (source 3511-3514; 3420-3426): for a.e. age `s > 0`, the tested
forced integrand against `∇^⊥ζ(s)` is integrable over the cell and its integral is
`streamSlice` (a.e. because `f(s,·)` is in `L²` of the cell for a.e. `s`, Fubini from the band-`L²`
force hypothesis).  Route: for `ψ` a cylinder test `⟨b,∇^⊥ψ⟩ = -⟨ω,ψ⟩` (third clause of
`IsBiotSavart`), so `-⟨b,∂_s∇^⊥ζ⟩ = ⟨ω,∂_sζ⟩`, `(μ/s)⟨b,∇^⊥ζ⟩ = -(μ/s)⟨ω,ζ⟩`,
`-ν⟨b,Δ∇^⊥ζ⟩ = ν⟨ω,Δζ⟩`, `-⟨f,∇^⊥ζ⟩ = ⟨g,ζ⟩` (curl hypothesis); the stress term is
`-Σ_ij(v_ib_j+b_iv_j)∂_j(∇^⊥ζ)_i`, and with `w = v·∇ζ`, `E = B0238.Ec tr s`, `Π = v₁∂_qζ -
v₀∂_ηζ - Eζ` (a cylinder test) one has the pointwise identity `Σ_ij(v_ib_j+b_iv_j)∂_j(∇^⊥ζ)_i +
[b₀∂_ηw - b₁∂_qw] - (b₀∂_qE + b₁∂_ηE)ζ = b₀∂_qΠ + b₁∂_ηΠ` (uses `div v = 0`); `∫ b·∇Π = 0`
(divergence clause), `∫[b₀∂_ηw - b₁∂_qw] = ⟨ω,w⟩`, so the stress term integrates to
`⟨ω,v·∇ζ⟩ - ⟨b·∇E,ζ⟩` and together with the viscous term to the `flowIntegrand` integral. -/
def VtvSlice : Prop :=
  ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f → ∀ ζ : ℝ → ℝ × ℝ → ℝ, IsStreamTest c ζ →
      ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
        IntegrableOn (fun x => forcedIntegrand ν (μ : ℂ) (trainVel tr) f b (streamField ζ)
          (s, x)) (B0579.cell c) ∧
        ∫ x in B0579.cell c, forcedIntegrand ν (μ : ℂ) (trainVel tr) f b (streamField ζ) (s, x) =
          streamSlice μ tr ω g b ζ s

/-- **The time Fubini** (source 4610, the integrated identity `Y(s,φ) = ∫₀^s R(r,φ)dr` with
`Y = s^μ⟨ω,φ⟩`, `R = r^μ(⟨g,φ⟩ + ∫flowIntegrand)`): for a stream test `ζ`, `s ↦ streamSlice` is
integrable on `(0,∞)` and has integral `0`.  Route: `η(s) = s^{-μ}ζ(s)` is a stream test;
`streamSlice = s^{-μ}(Y(s,∂_sη) + R(s,η))` after expanding `∂_s(s^μη)`; `∫Y(s,∂_sη)ds =
-∫R(s,η)ds` by Fubini on `{r < s}`; integrability from `energyLoc` (`⟨ω,ψ⟩ = ∫b·∇^⊥ψ`), the curl
hypothesis with `f` in `L²` on age bands, and `|μ/s| ≤ |μ|/s₁`
(compare `Short/PartIII-a/T18_FreeCausal/Existence/CausalLimitAE/FlatIntegrandBound.lean`). -/
def VtvTime : Prop :=
  ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f → ∀ ζ : ℝ → ℝ × ℝ → ℝ, IsStreamTest c ζ →
      IntegrableOn (streamSlice μ tr ω g b ζ) (Ioi (0 : ℝ)) ∧
      ∫ s in Ioi (0 : ℝ), streamSlice μ tr ω g b ζ s = 0

/-- **Integrability and Fubini for flat tests**: for a flat test `Φ` (age support in `[s₁,s₂]`,
`|η| ≤ R`), `forcedIntegrand` is integrable on `(0,∞) × cell` (`energyLoc` for `b`, `f` in `L²` on age
bands, bounded smooth `Φ` and `|μ/s| ≤ |μ|/s₁`, the train velocity bounded on the
band) and its space-time integral is the iterated integral. -/
def VtvFubini : Prop :=
  ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f → ∀ Φ, IsFlatTest c Φ →
      IntegrableOn (forcedIntegrand ν (μ : ℂ) (trainVel tr) f b Φ)
        (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, forcedIntegrand ν (μ : ℂ) (trainVel tr) f b Φ p =
        ∫ s in Ioi (0 : ℝ), ∫ x in B0579.cell c, forcedIntegrand ν (μ : ℂ) (trainVel tr) f b Φ
          (s, x)

/-- **The flux cutoff** (source 3511-3514 "this retains the horizontal mean"): if the weak
equation holds against all stream tests then it holds against every flat test `Φ`.  Route:
`ζ(s,q,η) = -∫_{-∞}^η Φ_q(s,q,η')dη'` is smooth, `c`-periodic (the `q`-mean of `Φ_q` vanishes by
`div Φ = 0` and compact support), `∇^⊥ζ = Φ`, `∇ζ` has compact support and `ζ` is constant (the
flux) for `η > R`; with a fixed cutoff `χ`, `ζ_R = ζχ(η/R)` is a stream test (after multiplying by a
fixed age cutoff equal to `1` on the support of `Φ`) and `∇^⊥ζ_R - Φ = O(R⁻¹)` supported in
`R ≤ |η| ≤ 2R`, with its derivatives; since `forcedIntegrand` is linear in `Φ` and bounded by the
`energyLoc` norms of `b` and the band-`L²` norm of `f` (Cauchy-Schwarz on a slab of measure
`O(R)`), the error integral is `O(R^{-1/2}) → 0`.  The decomposition is
`VtvFluxLemmas.lean` (`vtvFlux_of`). -/
def VtvFlux : Prop :=
  ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f →
    (∀ ζ : ℝ → ℝ × ℝ → ℝ, IsStreamTest c ζ →
      IntegrableOn (forcedIntegrand ν (μ : ℂ) (trainVel tr) f b (streamField ζ))
        (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        forcedIntegrand ν (μ : ℂ) (trainVel tr) f b (streamField ζ) p = 0) →
    ∀ Φ, IsFlatTest c Φ →
      IntegrableOn (forcedIntegrand ν (μ : ℂ) (trainVel tr) f b Φ) (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, forcedIntegrand ν (μ : ℂ) (trainVel tr) f b Φ p = 0

theorem vorticityToVelocity_of (h0 : VtvStreamFlat) (h1 : VtvSlice) (h2 : VtvTime)
    (h3 : VtvFubini) (h4 : VtvFlux) : VorticityToVelocity := by
  intro ν c μ tr ω g b G f hν hc hBUC hE hBS hf hcurl hid hOmInt
  have H : VtvHyps ν c μ tr ω g b G f := ⟨hν, hc, hBUC, hE, hBS, hf, hcurl, hid, hOmInt⟩
  refine h4 ν c μ tr ω g b G f H ?_
  intro ζ hζ
  obtain ⟨hI, hEq⟩ := h3 ν c μ tr ω g b G f H _ (h0 c ζ hζ)
  refine ⟨hI, ?_⟩
  rw [hEq]
  have hs := h1 ν c μ tr ω g b G f H ζ hζ
  calc ∫ s in Ioi (0 : ℝ), ∫ x in B0579.cell c,
        forcedIntegrand ν (μ : ℂ) (trainVel tr) f b (streamField ζ) (s, x)
      = ∫ s in Ioi (0 : ℝ), streamSlice μ tr ω g b ζ s :=
        integral_congr_ae (hs.mono fun s h => h.2)
    _ = 0 := (h2 ν c μ tr ω g b G f H ζ hζ).2

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
