import UnforcedLeray.Short.PartIIa.StatementsNear

/-!
# Part II-a, task `PartII-a:N02`: the quantitative Leray comparison, decomposed

Source of record: `the November 2 reference manuscript`, lines 1724-1751
(`near:leray-test`, first paragraph of the proof of `near:compact-free-comparison`).

Structure of the argument (all Props below are lemmas to be proved by separate tasks, except the
reduction `nearLerayComparison_of_approx` and the conditional theorem `nearLerayComparison_of`):

1. (Hilbert reduction, proved here) `‖(P_ε - P_0)F‖ ≤ dist(P_{G_0}F, G_ε) + dist(P_0F, S_ε)`,
   where `G_ε = S_εᗮ` is the closed span of `ε`-gradients and `S_ε` the `ε`-solenoidal subspace.
   Hence `NearLerayComparison` follows from `NearLerayApprox`: exhibit `g ∈ S_εᗮ` approximating the
   flat gradient part and `s ∈ S_ε` approximating the flat solenoidal part.
2. (`NearGradMember`, `NearStreamMember`) The two exact constructions of the source: for a smooth
   compactly supported (in the band) complex potential `Φ`, the `ε`-gradient `(D_εΦ, ∂_ηΦ)` lies in
   `S_εᗮ`; for a potential `ψ`, the stream field `(-ψ_η, (∂_q - εK)ψ + εψ)` lies in `S_ε` (line
   1731-1732: "exact counterparts ... zero exact divergence ... lifts to a Cartesian gradient").
   Weights: `K = 2S + η∂_η` is anti-self-adjoint for `s^{-3/2} ds dq dη`, so the weak `ε`-divergence of
   `b` is `(∂_q - εK) b_r + ∂_η b_z`, and `∂_η ((∂_q - εK)ψ) = (∂_q - εK)ψ_η - εψ_η` gives the `+εψ`.
3. (`NearLerayZeroMode`) q-independent tests (zero frequency, lines 1741-1747): the radial component is
   solenoidal and the axial one a gradient; primitives vanishing at `η = 0`, cutoff at `|η| ~ L_0 = 1/ε`.
4. (`NearLerayNonzeroMode`) tests with zero `q`-mean (nonzero `q`-frequencies, lines 1730-1740): inverse
   `q`-derivative costs `c/(2π)`, flat multiplier bounds `|∂_ξ^j P_0(k, ξ)| ≤ C_j |k|^{-j}`.
5. (`NearLerayModeSplit`) `f = f_0 + f_1` with `f_0` the `q`-average (zero frequency) and `f_1 = f - f_0`
   (zero mean), both smooth tests with `N(f_0) ≤ N(f)`, `N(f_1) ≤ 2 N(f)` (Jensen / Minkowski, `S`
   and `η` commute with the `q`-average); `P_0`, `K^⊥` linear, so approximants add.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-!-/

/-- Abstract projection estimate: for closed submodules `K0, K1` of a complex Hilbert space,
`‖(P_{K1} - P_{K0}) f‖ ≤ ‖P_{K0ᗮ} f - g‖ + ‖P_{K0} f - s‖` for any `g ∈ K1ᗮ` and `s ∈ K1`. -/
theorem nearLerayN02_projection_sub_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (K0 K1 : Submodule ℂ E)
    [K0.HasOrthogonalProjection] [K1.HasOrthogonalProjection]
    [K0ᗮ.HasOrthogonalProjection] [K1ᗮ.HasOrthogonalProjection]
    (f g s : E) (hg : g ∈ K1ᗮ) (hs : s ∈ K1) :
    ‖(K1.starProjection - K0.starProjection) f‖ ≤
      ‖K0ᗮ.starProjection f - g‖ + ‖K0.starProjection f - s‖ := by
  have hsplit : K0.starProjection f + K0ᗮ.starProjection f = f :=
    Submodule.starProjection_add_starProjection_orthogonal f
  have hf : K1.starProjection f =
      K1.starProjection (K0.starProjection f) + K1.starProjection (K0ᗮ.starProjection f) := by
    rw [← map_add, hsplit]
  have h1 : K1ᗮ.starProjection (K0.starProjection f) =
      K0.starProjection f - K1.starProjection (K0.starProjection f) :=
    Submodule.starProjection_orthogonal_val (K := K1) (K0.starProjection f)
  have key : (K1.starProjection - K0.starProjection) f =
      K1.starProjection (K0ᗮ.starProjection f) - K1ᗮ.starProjection (K0.starProjection f) := by
    rw [sub_apply, hf, h1]
    abel
  have hg0 : K1.starProjection g = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff (K := K1)).2 hg
  have hs0 : K1ᗮ.starProjection s = 0 :=
    Submodule.starProjection_orthogonal_apply_eq_zero (K := K1) hs
  have hA : K1.starProjection (K0ᗮ.starProjection f) =
      K1.starProjection (K0ᗮ.starProjection f - g) := by
    rw [map_sub, hg0, sub_zero]
  have hB : K1ᗮ.starProjection (K0.starProjection f) =
      K1ᗮ.starProjection (K0.starProjection f - s) := by
    rw [map_sub, hs0, sub_zero]
  rw [key, hA, hB]
  calc ‖K1.starProjection (K0ᗮ.starProjection f - g) -
        K1ᗮ.starProjection (K0.starProjection f - s)‖
      ≤ ‖K1.starProjection (K0ᗮ.starProjection f - g)‖ +
          ‖K1ᗮ.starProjection (K0.starProjection f - s)‖ := norm_sub_le _ _
    _ ≤ ‖K0ᗮ.starProjection f - g‖ + ‖K0.starProjection f - s‖ :=
        add_le_add (Submodule.norm_starProjection_apply_le (K := K1) _)
          (Submodule.norm_starProjection_apply_le (K := K1ᗮ) _)

/-- The right-hand side of `near:leray-test`:
`C (1 + c + c⁻¹)^d √ε Σ_{a,j ∈ {0,1}} ‖η^j S^a f‖_H`. -/
def nearLerayRhs (C : ℝ) (d : ℕ) (c ε : ℝ) (f : Profile → MeridC) : ℝ :=
  C * (1 + c + c⁻¹) ^ d * Real.sqrt ε *
    ∑ a ∈ Finset.range 2, ∑ j ∈ Finset.range 2,
      (∫ p, (|p.2.2| ^ j) ^ 2 * ‖(opS^[a] f) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ)

/-- **Approximation of the flat gradient and solenoidal parts** for the smooth tests `f` satisfying a
predicate `T c f` (`T = True` gives the full statement; `T` = `q`-independent or `q`-mean-zero gives the
zero- and nonzero-frequency parts): the flat gradient part `P_{G_0}F = (S_0)ᗮ.starProjection F` is within
`nearLerayRhs` of some `g ∈ (S_ε)ᗮ` and the flat solenoidal part `P_0F = S_0.starProjection F` within
`nearLerayRhs` of some `s ∈ S_ε`. -/
def NearLerayApproxOn (T : ℝ → (Profile → MeridC) → Prop) : Prop :=
  ∃ (d : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (c ε : ℝ), 0 < c → 0 < ε → ε ≤ 1 →
    ∀ (f : Profile → MeridC) (F : HSpace c MeridC), IsMeridTest c f → T c f →
      (F : Profile → MeridC) =ᵐ[measureH c] f →
      (∃ g ∈ (solenoidalHC ε c)ᗮ,
        ‖(solenoidalHC 0 c)ᗮ.starProjection F - g‖ ≤ nearLerayRhs C d c ε f) ∧
      (∃ s ∈ solenoidalHC ε c,
        ‖(solenoidalHC 0 c).starProjection F - s‖ ≤ nearLerayRhs C d c ε f)

/-- Reduction: the two approximations give `NearLerayComparison` with constant `2 C`. -/
theorem nearLerayComparison_of_approx (h : NearLerayApproxOn (fun _ _ => True)) :
    NearLerayComparison := by
  obtain ⟨d, C, hC, hA⟩ := h
  refine ⟨d, 2 * C, by linarith, fun c ε hc hε hε1 f F hf hF => ?_⟩
  obtain ⟨⟨g, hg, hgb⟩, ⟨s, hs, hsb⟩⟩ := hA c ε hc hε hε1 f F hf trivial hF
  have hbd := nearLerayN02_projection_sub_le (solenoidalHC 0 c) (solenoidalHC ε c) F g s hg hs
  change ‖((solenoidalHC ε c).starProjection - (solenoidalHC 0 c).starProjection) F‖ ≤ _
  unfold nearLerayRhs at hgb hsb
  linarith [hbd, hgb, hsb]

/-! ### Complex potentials, their gradients and stream fields -/

/-- Complex smooth tests: smooth, `c`-periodic in `q`, supported in a band `s₀ ≤ s ≤ s₁`, `|η| ≤ L`,
`s₀ > 0` (the complexification of `IsProfileTest`). -/
structure IsCTest (c : ℝ) (Φ : Profile → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ Φ
  periodic : QPeriodic c Φ
  band : ∃ s0 s1 L : ℝ, 0 < s0 ∧ ∀ p : Profile, Φ p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L

/-- The `ε`-gradient `(D_εΦ, ∂_ηΦ)`, `D_ε = ∂_q - εK`, of a complex potential (the complexification of
`cgrad`: for real `Φ` it is `cgrad ε Φ`). -/
def cgradC (ε : ℝ) (Φ : Profile → ℂ) : Profile → MeridC := fun p =>
  !₂[pdQ Φ p - (ε : ℂ) * opK Φ p, pdEta Φ p]

/-- The stream field `(-ψ_η, (∂_q - εK)ψ + εψ)` of a complex potential `ψ` (line 1731). -/
def streamC (ε : ℝ) (ψ : Profile → ℂ) : Profile → MeridC := fun p =>
  !₂[-pdEta ψ p, pdQ ψ p - (ε : ℂ) * opK ψ p + (ε : ℂ) * ψ p]

/-- `q`-independent (zero `q`-frequency) profiles. -/
def QInvariant (_c : ℝ) (f : Profile → MeridC) : Prop :=
  ∀ (s q q' η : ℝ), f (s, q, η) = f (s, q', η)

/-- Profiles with zero `q`-mean over the cell `(0, c]` (nonzero `q`-frequencies only). -/
def QMeanZero (c : ℝ) (f : Profile → MeridC) : Prop :=
  ∀ (s η : ℝ), ∫ q in (0 : ℝ)..c, f (s, q, η) = 0

/-! ### The lemma Props -/

/-- **`ε`-gradients of band potentials lie in the closed span of gradients.** For a complex band
potential `Φ`, `cgradC ε Φ` is in `L²(measureH c)` (continuous, band support, finite measure) and its
class lies in `(solenoidalHC ε c)ᗮ`: write `Φ = Φ₁ + iΦ₂` with real `IsProfileTest` parts; then
`cgradC ε Φ = cgrad ε Φ₁ + i cgrad ε Φ₂` and each `toLp (cgrad ε Φ_k)` is a generator of the span
whose orthogonal complement is `solenoidalHC ε c` (`Submodule.le_orthogonal_orthogonal`). -/
def NearGradMember : Prop :=
  ∀ (ε c : ℝ) (Φ : Profile → ℂ), IsCTest c Φ →
    ∃ hm : MemLp (cgradC ε Φ) 2 (measureH c), hm.toLp _ ∈ (solenoidalHC ε c)ᗮ

/-- **Stream fields of band potentials are `ε`-solenoidal.** For a complex band potential `ψ`, `streamC ε ψ`
is in `L²(measureH c)` and its class lies in `solenoidalHC ε c`: it is orthogonal to every
`toLp (cgrad ε Φ)`, `Φ` a real profile test. Integrate by parts in `q` (periodicity), `η` (compact support)
and `s` (band support): with the weight `s^{-3/2}`, `∫ (Kψ) Φ = -∫ ψ (KΦ)` and `∂_ηK = K∂_η + ∂_η`, the
`∂_q∂_η` terms cancel and the `ε` terms cancel (`ε[-∫K(ψ_η)Φ + ∫(Kψ_η + ψ_η)Φ - ∫ψ_ηΦ] = 0`);
complex conjugation maps `streamC ε ψ` to `streamC ε ψ̄` (real coefficients), so it suffices to test
the bilinear pairing. -/
def NearStreamMember : Prop :=
  ∀ (ε c : ℝ) (ψ : Profile → ℂ), IsCTest c ψ →
    ∃ hm : MemLp (streamC ε ψ) 2 (measureH c), hm.toLp _ ∈ solenoidalHC ε c

/-- **Zero-frequency part** (lines 1741-1747), using `NearGradMember` and `NearStreamMember`:
for `q`-independent smooth tests `f = (f_r, f_z)`, `(I - P_0)F = (0, f_z)` and `P_0F = (f_r, 0)` (the
latter is orthogonal to flat gradients by `q`-independence, the former is a limit of flat gradients by a
cutoff of the primitive). Approximate `(0, f_z)` by `cgradC ε (χ_L Φ)` with `Φ(s, η) = ∫_0^η f_z`
(vanishing at `η = 0`) and `χ_L = χ(εη)`, and `(f_r, 0)` by `streamC ε (χ_L ψ)` with
`ψ(s, η) = -∫_0^η f_r`; the errors are `sup |Φ|, sup |SΦ| ≤ C ‖⟨η⟩ S^a f‖₂`, cutoff differentiation
`L_0^{-1/2} = √ε`, geometric correction `ε L_0^{1/2} = √ε`, tail `L_0^{-1} = ε`. -/
def NearLerayZeroMode : Prop :=
  NearGradMember → NearStreamMember → NearLerayApproxOn (fun c f => QInvariant c f)

/-- **Nonzero-frequency part** (lines 1730-1740), using `NearGradMember` and `NearStreamMember`:
for smooth tests with zero `q`-mean. On each nonzero `q`-frequency `k` the flat decomposition is
`f = (φ_q, φ_η) + (-ψ_η, ψ_q)`; the exact counterparts are `cgradC ε φ̃` and `streamC ε ψ̃` for the
`η`-cutoffs `φ̃, ψ̃` of the potentials (band potentials: `s`-support is that of `f`); the inverse
`q`-derivative costs `c/(2π)`, the flat Fourier multiplier satisfies `|∂_ξ^jP_0(k, ξ)| ≤ C_j |k|^{-j}`
(`Units/B0493*`), and `η`-moments and `S` commute with the projections. -/
def NearLerayNonzeroMode : Prop :=
  NearGradMember → NearStreamMember → NearLerayApproxOn (fun c f => QMeanZero c f)

/-- **Mode splitting.** The full approximation follows from the zero-frequency and zero-mean ones:
`f_0 = c⁻¹ ∫_0^c f dq` and `f_1 = f - f_0` are smooth tests (parametric integral over a compact
`q`-interval of a smooth band-supported function), `f_0` is `q`-independent and `f_1` has zero mean
(`c`-periodicity), `opS` and `|η|^j` commute with the average, `N(f_0) ≤ N(f)` (Jensen) and
`N(f_1) ≤ 2N(f)` (triangle inequality), the `H`-projection of `F` splits as the sum of the projections of
`F_0 = toLp f_0` and `F_1 = toLp f_1` and `g = g_0 + g_1`, `s = s_0 + s_1` work. -/
def NearLerayModeSplit : Prop :=
  NearLerayApproxOn (fun c f => QInvariant c f) → NearLerayApproxOn (fun c f => QMeanZero c f) →
    NearLerayApproxOn (fun _ _ => True)

/-- `NearLerayComparison` from the five lemma Props. -/
theorem nearLerayComparison_of
    (hg : NearGradMember) (hs : NearStreamMember) (hz : NearLerayZeroMode)
    (hn : NearLerayNonzeroMode) (hm : NearLerayModeSplit) : NearLerayComparison :=
  nearLerayComparison_of_approx (hm (hz hg hs) (hn hg hs))

end UnforcedLeray.Short.PartIIa
