import UnforcedLeray.Short.PartIIa.Sub.N02

/-!
# Part II-a, task `PartII-a:N02/3` (`NearLerayZeroMode`): decomposition

Source of record: `the November 2 reference manuscript`, lines 1728-1737
(the zero-frequency paragraph of the proof of `near:leray-test`: "For the zero frequency, the radial
component is solenoidal and the axial component is a gradient. Take the corresponding primitives to
vanish at `η = 0`, and cut them off at `|η| ~ L₀`. Their suprema, including one `S` derivative, are
bounded by `C‖⟨η⟩f‖₂` and `C‖⟨η⟩Sf‖₂`. Cutoff differentiation costs `L₀^{-1/2}`, geometric correction
costs `ε L₀^{1/2}`, and the omitted field tail costs `L₀^{-1}`. Choose `L₀ = ε^{-1}`.").
(The task brief cited lines 1741-1747; in the current copy of the source the paragraph is at 1728-1737.)

Target: `NearLerayZeroMode` (`Sub/N02.lean`) `:= NearGradMember → NearStreamMember →
NearLerayApproxOn (fun c f => QInvariant c f)`.

## Structure

For a `q`-independent smooth test `f = (f_r, f_z)`, `Φ_z = ∫_0^η f_z` and `Φ_r = ∫_0^η f_r` are the
primitives vanishing at `η = 0`, `χ_L(η) = χ(η/L)` is the cutoff (`zChi`, `zCut`).

* Top layer (proved here, no placeholder proofs): `nearLerayZeroMode_of` reduces the target to
  `ZeroFlatProj` (flat projections, L3), `ZeroGradApprox` (L2a), `ZeroStreamApprox` (L2b), and
  `zeroFlatProj_of`, `zeroGradApprox_of`, `zeroStreamApprox_of` reduce these to the lemma Props below.
* Lemma Props (each proved by its own task): `ZeroCutoff`, `ZeroPrimSmooth`, `ZeroPrimComm`,
  `ZeroPrimBound`, `ZeroWindowBound`, `ZeroCutTest`, `ZeroGradCutError`, `ZeroStreamCutError`,
  `ZeroFlatSolenoid`, `ZeroFlatGradient`.

All constants are uniform in `c` and in `ε`: the cell measure contributes the same factor `c` to both
sides (everything is `q`-independent), the errors are `O(√ε)` for `ε ≤ 1` and `d = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-! ### Definitions -/

/-- The `η`-primitive of a complex profile function, vanishing at `η = 0`:
`(zPrimC g)(s, q, η) = ∫_0^η g(s, q, t) dt`. -/
def zPrimC (g : Profile → ℂ) : Profile → ℂ := fun p =>
  ∫ t in (0 : ℝ)..p.2.2, g (p.1, p.2.1, t)

/-- A fixed smooth cutoff: `χ = 1` on `|t| ≤ 1`, `χ = 0` for `|t| ≥ 2` (`√2 ≤ 2`), `0 ≤ χ ≤ 1`. -/
def zChi (t : ℝ) : ℝ := Real.smoothTransition (2 - t ^ 2)

/-- The `η`-cutoff at scale `L`: `(zCut L Φ)(s, q, η) = χ(η/L) Φ(s, q, η)`. -/
def zCut (L : ℝ) (Φ : Profile → ℂ) : Profile → ℂ := fun p =>
  ((zChi (p.2.2 / L) : ℝ) : ℂ) * Φ p

/-- The weighted moment `‖η^j S^a f‖_H = (∫ (|η|^j)^2 ‖S^a f‖^2 d(measureH c))^{1/2}`. -/
def zMom (c : ℝ) (a j : ℕ) (f : Profile → MeridC) : ℝ :=
  (∫ p, (|p.2.2| ^ j) ^ 2 * ‖(opS^[a] f) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ)

/-- `Σ_{a,j ∈ {0,1}} ‖η^j S^a f‖_H`, the sum appearing in `nearLerayRhs`. -/
def zMomSum (c : ℝ) (f : Profile → MeridC) : ℝ :=
  ∑ a ∈ Finset.range 2, ∑ j ∈ Finset.range 2, zMom c a j f

theorem nearLerayRhs_zero_d (C c ε : ℝ) (f : Profile → MeridC) :
    nearLerayRhs C 0 c ε f = C * Real.sqrt ε * zMomSum c f := by
  unfold nearLerayRhs zMomSum zMom
  simp

theorem zMomSum_nonneg (c : ℝ) (f : Profile → MeridC) : 0 ≤ zMomSum c f :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Real.rpow_nonneg
    (integral_nonneg fun p => by positivity) _

/-- The right-hand side `nearLerayRhs C d c ε f` is monotone in the constant `C` (for `d` arbitrary,
since its remaining factors are nonnegative). -/
theorem nearLerayRhs_mono {C C' : ℝ} (d : ℕ) (c ε : ℝ) (f : Profile → MeridC) (hc : 0 < c)
    (hCC : C ≤ C') : nearLerayRhs C d c ε f ≤ nearLerayRhs C' d c ε f := by
  unfold nearLerayRhs
  have hA : 0 ≤ (1 + c + c⁻¹) ^ d :=
    pow_nonneg (by have := inv_nonneg.2 hc.le; linarith [hc.le]) d
  have hB : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hS : 0 ≤ ∑ a ∈ Finset.range 2, ∑ j ∈ Finset.range 2,
      (∫ p, (|p.2.2| ^ j) ^ 2 * ‖(opS^[a] f) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun j _ =>
      Real.rpow_nonneg (integral_nonneg fun p => by positivity) _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCC hA) hB) hS

/-- The norm of an element of `H` is the `L²` integral of any a.e.-representative. -/
theorem zLpNorm_eq {c : ℝ} (D : HSpace c MeridC) (h : Profile → MeridC)
    (hD : (D : Profile → MeridC) =ᵐ[measureH c] h) :
    ‖D‖ = (∫ p, ‖h p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) := by
  have hm : MemLp (D : Profile → MeridC) 2 (measureH c) := Lp.memLp D
  rw [Lp.norm_def, hm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have h2 : (2 : ENNReal).toReal = 2 := by norm_num
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun p => by positivity) _), h2]
  have hint : ∫ a, ‖(D : Profile → MeridC) a‖ ^ (2 : ℝ) ∂(measureH c)
      = ∫ p, ‖h p‖ ^ 2 ∂(measureH c) := by
    refine integral_congr_ae ?_
    filter_upwards [hD] with p hp
    rw [hp, Real.rpow_two]
  rw [hint]
  norm_num

/-! ### The lemma Props -/

/-- **L0 (cutoff).** `zChi` is smooth, `0 ≤ zChi ≤ 1`, equals `1` on `|t| ≤ 1` and `0` for `|t| ≥ 2`,
and has bounded derivative. -/
def ZeroCutoff : Prop :=
  ContDiff ℝ ∞ zChi ∧ (∀ t, 0 ≤ zChi t ∧ zChi t ≤ 1) ∧ (∀ t, |t| ≤ 1 → zChi t = 1) ∧
    (∀ t, 2 ≤ |t| → zChi t = 0) ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |deriv zChi t| ≤ M

/-- **L1a (primitive: smoothness).** For a smooth band function `g`, the primitive `zPrimC g` is
smooth and `∂_η (zPrimC g) = g`. (No periodicity is needed: differentiation under the integral over
the compact range `[0, η]` is local.) -/
def ZeroPrimSmooth : Prop :=
  ∀ (g : Profile → ℂ), ContDiff ℝ ∞ g →
    (∃ s0 s1 L : ℝ, 0 < s0 ∧ ∀ p : Profile, g p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) →
      ContDiff ℝ ∞ (zPrimC g) ∧ ∀ p : Profile, pdEta (zPrimC g) p = g p

/-- **L1b (primitive commutes with `S = s∂_s`).** For a smooth band function `g`,
`opS (zPrimC g) = zPrimC (opS g)` (differentiation under the integral over the compact `η`-range). -/
def ZeroPrimComm : Prop :=
  ∀ (g : Profile → ℂ), ContDiff ℝ ∞ g →
    (∃ s0 s1 L : ℝ, 0 < s0 ∧ ∀ p : Profile, g p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) →
      opS (zPrimC g) = zPrimC (opS g)

/-- **L1c (primitive: fiber bound).** `|zPrimC g(s,q,η)| ≤ √π (A + B)` with `A = (∫ |g|² dt)^{1/2}`,
`B = (∫ t² |g|² dt)^{1/2}` on the fiber over `(s, q)` (Cauchy-Schwarz with weight `1 + t²`,
`∫ (1 + t²)⁻¹ = π`; tex 1731-1732, "suprema ... bounded by `C‖⟨η⟩f‖₂`"). -/
def ZeroPrimBound : Prop :=
  ∀ (g : Profile → ℂ), ContDiff ℝ ∞ g →
    (∃ s0 s1 L : ℝ, 0 < s0 ∧ ∀ p : Profile, g p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) →
      ∀ p : Profile, ‖zPrimC g p‖ ≤ Real.sqrt Real.pi *
        ((∫ t, ‖g (p.1, p.2.1, t)‖ ^ 2 ∂volume) ^ (1 / 2 : ℝ) +
          (∫ t, t ^ 2 * ‖g (p.1, p.2.1, t)‖ ^ 2 ∂volume) ^ (1 / 2 : ℝ))

/-- **L2 core (window bound in `H`).** The primitive on the window `|η| ≤ R` has `L²(measureH c)` norm
`≤ C R^{1/2} (‖g‖_H + ‖η g‖_H)`, with `C` universal (fiberwise `L1c`, then integrate `s^{-3/2} ds dq`
over the cell; the window has length `2R`). -/
def ZeroWindowBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (c R : ℝ) (g : Profile → ℂ), 0 < c → 0 < R → ContDiff ℝ ∞ g →
    (∃ s0 s1 L : ℝ, 0 < s0 ∧ ∀ p : Profile, g p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) →
      (∫ p, {p : Profile | |p.2.2| ≤ R}.indicator (fun p => ‖zPrimC g p‖ ^ 2) p
          ∂(measureH c)) ^ (1 / 2 : ℝ) ≤
        C * R ^ (1 / 2 : ℝ) *
          ((∫ p, ‖g p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) +
            (∫ p, p.2.2 ^ 2 * ‖g p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ))

/-- **L2 (cut-off primitives are complex band potentials).** For a smooth periodic band test `f` and
`L > 0`, `χ_L Φ_i` and `-χ_L Φ_i` (`Φ_i = ∫_0^η f_i`) are `IsCTest`s (smooth by `L1a`; periodic;
band: the `s`-support is that of `f`, and `|η| < 2L` on the support of `χ_L`). -/
def ZeroCutTest : Prop :=
  ∀ (c L : ℝ) (f : Profile → MeridC), 0 < c → 0 < L → IsMeridTest c f →
    ∀ i : Fin 2, IsCTest c (zCut L (zPrimC (fun p => f p i))) ∧
      IsCTest c (zCut L (fun p => -zPrimC (fun r => f r i) p))

/-- **L2a core (error of the gradient ansatz).** For a `q`-independent smooth test `f`, the field
`cgradC ε (χ_L Φ_z)` (`Φ_z = ∫_0^η f_z`) approximates `(0, f_z)` in `L²(measureH c)` with error
`C (L⁻¹ + L^{-1/2} + ε L^{1/2} + ε) Σ_{a,j} ‖η^j S^a f‖_H`, for every `ε ≥ 0` and `L > 0`
(tail `L⁻¹`, cutoff differentiation `L^{-1/2}`, geometric correction `ε L^{1/2}`, and
`ε ‖η χ_L f_z‖ ≤ ε ‖η f_z‖`; tex 1731-1735). Pointwise `∂_q = 0`,
`cgradC ε (χ_L Φ_z) = (-ε K(χ_L Φ_z), χ_L f_z + L⁻¹ χ'(η/L) Φ_z)`. -/
def ZeroGradCutError : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (c ε L : ℝ) (f : Profile → MeridC), 0 < c → 0 ≤ ε → 0 < L →
    IsMeridTest c f → QInvariant c f →
      (∫ p, ‖(!₂[0, f p 1] : MeridC) -
          cgradC ε (zCut L (zPrimC (fun r => f r 1))) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) ≤
        C * (L⁻¹ + L ^ (-(1 / 2 : ℝ)) + ε * L ^ (1 / 2 : ℝ) + ε) * zMomSum c f

/-- **L2b core (error of the stream ansatz).** For a `q`-independent smooth test `f`, the field
`streamC ε (χ_L ψ)` with `ψ = -Φ_r = -∫_0^η f_r` (so `-ψ_η = f_r`) approximates `(f_r, 0)` in
`L²(measureH c)` with the same error as `ZeroGradCutError` (the extra term is
`ε ‖χ_L ψ‖ ≤ ε C (2L)^{1/2} (‖f_r‖ + ‖η f_r‖)` by `ZeroWindowBound`). -/
def ZeroStreamCutError : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (c ε L : ℝ) (f : Profile → MeridC), 0 < c → 0 ≤ ε → 0 < L →
    IsMeridTest c f → QInvariant c f →
      (∫ p, ‖(!₂[f p 0, 0] : MeridC) -
          streamC ε (zCut L (fun r => -zPrimC (fun r' => f r' 0) r)) p‖ ^ 2 ∂(measureH c)) ^
          (1 / 2 : ℝ) ≤
        C * (L⁻¹ + L ^ (-(1 / 2 : ℝ)) + ε * L ^ (1 / 2 : ℝ) + ε) * zMomSum c f

/-- **L3a (the radial component is flat-solenoidal).** For a `q`-independent smooth test `f`,
`(f_r, 0) ∈ (S_0)` : it is orthogonal to every flat gradient `(∂_qΦ, ∂_ηΦ)` because `f_r` does not
depend on `q` and `Φ` is `q`-periodic (`∫_0^c ∂_qΦ dq = 0`, Fubini on the cell; tex 1728-1729). -/
def ZeroFlatSolenoid : Prop :=
  ∀ (c : ℝ) (f : Profile → MeridC), 0 < c → IsMeridTest c f → QInvariant c f →
    ∃ hm : MemLp (fun p => (!₂[f p 0, 0] : MeridC)) 2 (measureH c),
      hm.toLp _ ∈ solenoidalHC 0 c

/-- **L3b (the axial component is a flat gradient).** For a `q`-independent smooth test `f`,
`(0, f_z) ∈ (S_0)ᗮ`: it is the `H`-limit of `cgradC 0 (χ_L Φ_z)` as `L → ∞`
(`ZeroCutTest`, `NearGradMember` and `ZeroGradCutError` with `ε = 0`, error `C (L⁻¹ + L^{-1/2}) → 0`;
tex 1728-1729). -/
def ZeroFlatGradient : Prop :=
  ∀ (c : ℝ) (f : Profile → MeridC), 0 < c → IsMeridTest c f → QInvariant c f →
    ∃ hm : MemLp (fun p => (!₂[0, f p 1] : MeridC)) 2 (measureH c),
      hm.toLp _ ∈ (solenoidalHC 0 c)ᗮ

/-- **L3 (flat projections).** For a `q`-independent smooth band test `f = (f_r, f_z)` and `F ∈ H` with
`F = f` a.e., the flat solenoidal projection `P_0 F` is `(f_r, 0)` and the flat gradient projection
`(S_0)ᗮ.starProjection F` is `(0, f_z)` (tex 1728-1729). -/
def ZeroFlatProj : Prop :=
  ∀ (c : ℝ) (f : Profile → MeridC) (F : HSpace c MeridC), 0 < c → IsMeridTest c f →
    QInvariant c f → (F : Profile → MeridC) =ᵐ[measureH c] f →
      (((solenoidalHC 0 c).starProjection F : HSpace c MeridC) : Profile → MeridC)
          =ᵐ[measureH c] (fun p => (!₂[f p 0, 0] : MeridC)) ∧
        ((((solenoidalHC 0 c)ᗮ).starProjection F : HSpace c MeridC) : Profile → MeridC)
          =ᵐ[measureH c] (fun p => (!₂[0, f p 1] : MeridC))

/-- **L2a (zero-frequency gradient approximant).** Given `NearGradMember`, for a `q`-independent
smooth test `f` and any `B ∈ H` with `B = (0, f_z)` a.e., there is `g ∈ (S_ε)ᗮ` within
`nearLerayRhs C 0` of `B`, with a constant `C` uniform in `c` and `ε`. The witness is
`g = cgradC ε (χ_L Φ_z)` with `Φ_z = ∫_0^η f_z` and `L = ε⁻¹` (tex 1731-1736). -/
def ZeroGradApprox : Prop :=
  NearGradMember → ∃ C : ℝ, 0 ≤ C ∧ ∀ (c ε : ℝ), 0 < c → 0 < ε → ε ≤ 1 →
    ∀ (f : Profile → MeridC) (B : HSpace c MeridC), IsMeridTest c f → QInvariant c f →
      (B : Profile → MeridC) =ᵐ[measureH c] (fun p => (!₂[0, f p 1] : MeridC)) →
        ∃ g ∈ (solenoidalHC ε c)ᗮ, ‖B - g‖ ≤ nearLerayRhs C 0 c ε f

/-- **L2b (zero-frequency solenoidal approximant).** Given `NearStreamMember`, for a
`q`-independent smooth test `f` and any `A ∈ H` with `A = (f_r, 0)` a.e., there is `s ∈ S_ε`
within `nearLerayRhs C 0` of `A`, with a constant `C` uniform in `c` and `ε`. The witness is
`s = streamC ε (χ_L ψ)` with `ψ = -∫_0^η f_r` and `L = ε⁻¹` (tex 1731-1736). -/
def ZeroStreamApprox : Prop :=
  NearStreamMember → ∃ C : ℝ, 0 ≤ C ∧ ∀ (c ε : ℝ), 0 < c → 0 < ε → ε ≤ 1 →
    ∀ (f : Profile → MeridC) (A : HSpace c MeridC), IsMeridTest c f → QInvariant c f →
      (A : Profile → MeridC) =ᵐ[measureH c] (fun p => (!₂[f p 0, 0] : MeridC)) →
        ∃ s ∈ solenoidalHC ε c, ‖A - s‖ ≤ nearLerayRhs C 0 c ε f

/-! ### Conditional theorems -/

/-- **Assembly (top layer).** The target `NearLerayZeroMode` follows from the flat projections
(`ZeroFlatProj`) and the two zero-frequency approximants (`ZeroGradApprox`, `ZeroStreamApprox`), with
`d = 0` and constant `C₁ + C₂`. -/
theorem nearLerayZeroMode_of (hF : ZeroFlatProj) (hG : ZeroGradApprox)
    (hS : ZeroStreamApprox) : NearLerayZeroMode := by
  intro hg hs
  obtain ⟨C1, hC1, hA⟩ := hG hg
  obtain ⟨C2, hC2, hB⟩ := hS hs
  refine ⟨0, C1 + C2, by linarith, fun c ε hc hε hε1 f F hf hT hFf => ?_⟩
  obtain ⟨hP0, hPG⟩ := hF c f F hc hf hT hFf
  obtain ⟨g, hgS, hgb⟩ := hA c ε hc hε hε1 f (((solenoidalHC 0 c)ᗮ).starProjection F) hf hT hPG
  obtain ⟨s, hsS, hsb⟩ := hB c ε hc hε hε1 f ((solenoidalHC 0 c).starProjection F) hf hT hP0
  exact ⟨⟨g, hgS, hgb.trans (nearLerayRhs_mono (C := C1) (C' := C1 + C2) 0 c ε f hc (by linarith))⟩,
    ⟨s, hsS, hsb.trans (nearLerayRhs_mono (C := C2) (C' := C1 + C2) 0 c ε f hc (by linarith))⟩⟩

/-- **L3 from L3a, L3b.** `F = (f_r, 0) + (0, f_z)` with the first summand in `S_0` and the second in
`(S_0)ᗮ`, so the two projections are the summands. -/
theorem zeroFlatProj_of (hS : ZeroFlatSolenoid) (hG : ZeroFlatGradient) : ZeroFlatProj := by
  intro c f F hc hf hT hFf
  obtain ⟨hu, hum⟩ := hS c f hc hf hT
  obtain ⟨hv, hvm⟩ := hG c f hc hf hT
  have hFuv : F = hu.toLp _ + hv.toLp _ := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_add (hu.toLp _) (hv.toLp _), hu.coeFn_toLp, hv.coeFn_toLp, hFf]
      with p h1 h2 h3 h4
    rw [h1, h4]
    show f p = (hu.toLp _) p + (hv.toLp _) p
    rw [h2, h3]
    ext i
    fin_cases i <;> simp
  have hSproj : (solenoidalHC 0 c).starProjection F = hu.toLp _ :=
    Submodule.eq_starProjection_of_mem_orthogonal' hum hvm hFuv
  have hGproj : ((solenoidalHC 0 c)ᗮ).starProjection F = hv.toLp _ :=
    Submodule.eq_starProjection_of_mem_orthogonal' hvm
      (Submodule.le_orthogonal_orthogonal _ hum) (by rw [hFuv, add_comm])
  refine ⟨?_, ?_⟩
  · rw [hSproj]; exact hu.coeFn_toLp
  · rw [hGproj]; exact hv.coeFn_toLp

/-- Elementary arithmetic for `L = ε⁻¹`, `0 < ε ≤ 1`:
`ε + ε^{1/2} + ε·(ε⁻¹)^{1/2} + ε ≤ 4 √ε`. -/
theorem zeroErr_arith {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (ε⁻¹)⁻¹ + (ε⁻¹) ^ (-(1 / 2 : ℝ)) + ε * (ε⁻¹) ^ (1 / 2 : ℝ) + ε ≤ 4 * Real.sqrt ε := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have h1 : (ε⁻¹)⁻¹ = ε := inv_inv ε
  have h2 : (ε⁻¹) ^ (-(1 / 2 : ℝ)) = Real.sqrt ε := by
    rw [Real.rpow_neg (inv_nonneg.2 hε.le), Real.inv_rpow hε.le, inv_inv, Real.sqrt_eq_rpow]
  have h3 : ε * (ε⁻¹) ^ (1 / 2 : ℝ) = Real.sqrt ε := by
    rw [Real.inv_rpow hε.le, ← Real.sqrt_eq_rpow]
    have hsq : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε.le
    field_simp
    linarith
  have h4 : ε ≤ Real.sqrt ε := by
    have hsq : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε.le
    have : Real.sqrt ε ≤ 1 := by
      rw [Real.sqrt_le_one]; exact hε1
    nlinarith
  rw [h1, h2, h3]
  linarith

/-- **L2a from `NearGradMember`, `ZeroCutTest`, `ZeroGradCutError`.** Take `L = ε⁻¹`,
`g = cgradC ε (χ_L Φ_z)`; the `H`-distance is the `L²` integral of the pointwise error. -/
theorem zeroGradApprox_of (hT : ZeroCutTest) (hE : ZeroGradCutError) : ZeroGradApprox := by
  intro hN
  obtain ⟨C, hC, hE⟩ := hE
  refine ⟨4 * C, by positivity, fun c ε hc hε hε1 f B hf hq hB => ?_⟩
  have hL : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  obtain ⟨hm, hmem⟩ := hN ε c _ (hT c ε⁻¹ f hc hL hf 1).1
  refine ⟨hm.toLp _, hmem, ?_⟩
  have hnorm : ‖B - hm.toLp _‖ = (∫ p, ‖(!₂[0, f p 1] : MeridC) -
      cgradC ε (zCut ε⁻¹ (zPrimC (fun r => f r 1))) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) := by
    apply zLpNorm_eq
    filter_upwards [Lp.coeFn_sub B (hm.toLp _), hm.coeFn_toLp, hB] with p h1 h2 h3
    rw [h1]
    show B p - (hm.toLp _) p = _
    rw [h2, h3]
  rw [hnorm, nearLerayRhs_zero_d]
  refine (hE c ε ε⁻¹ f hc hε.le hL hf hq).trans ?_
  have hs : 0 ≤ zMomSum c f := zMomSum_nonneg c f
  have hA := zeroErr_arith hε hε1
  calc C * ((ε⁻¹)⁻¹ + (ε⁻¹) ^ (-(1 / 2 : ℝ)) + ε * (ε⁻¹) ^ (1 / 2 : ℝ) + ε) * zMomSum c f
      ≤ C * (4 * Real.sqrt ε) * zMomSum c f := by gcongr
    _ = 4 * C * Real.sqrt ε * zMomSum c f := by ring

/-- **L2b from `NearStreamMember`, `ZeroCutTest`, `ZeroStreamCutError`.** Take `L = ε⁻¹`,
`s = streamC ε (χ_L ψ)`, `ψ = -Φ_r`. -/
theorem zeroStreamApprox_of (hT : ZeroCutTest) (hE : ZeroStreamCutError) : ZeroStreamApprox := by
  intro hN
  obtain ⟨C, hC, hE⟩ := hE
  refine ⟨4 * C, by positivity, fun c ε hc hε hε1 f A hf hq hA => ?_⟩
  have hL : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  obtain ⟨hm, hmem⟩ := hN ε c _ (hT c ε⁻¹ f hc hL hf 0).2
  refine ⟨hm.toLp _, hmem, ?_⟩
  have hnorm : ‖A - hm.toLp _‖ = (∫ p, ‖(!₂[f p 0, 0] : MeridC) -
      streamC ε (zCut ε⁻¹ (fun r => -zPrimC (fun r' => f r' 0) r)) p‖ ^ 2 ∂(measureH c)) ^
        (1 / 2 : ℝ) := by
    apply zLpNorm_eq
    filter_upwards [Lp.coeFn_sub A (hm.toLp _), hm.coeFn_toLp, hA] with p h1 h2 h3
    rw [h1]
    show A p - (hm.toLp _) p = _
    rw [h2, h3]
  rw [hnorm, nearLerayRhs_zero_d]
  refine (hE c ε ε⁻¹ f hc hε.le hL hf hq).trans ?_
  have hs : 0 ≤ zMomSum c f := zMomSum_nonneg c f
  have hA := zeroErr_arith hε hε1
  calc C * ((ε⁻¹)⁻¹ + (ε⁻¹) ^ (-(1 / 2 : ℝ)) + ε * (ε⁻¹) ^ (1 / 2 : ℝ) + ε) * zMomSum c f
      ≤ C * (4 * Real.sqrt ε) * zMomSum c f := by gcongr
    _ = 4 * C * Real.sqrt ε * zMomSum c f := by ring

end UnforcedLeray.Short.PartIIa
