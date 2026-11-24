import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1_of
import UnforcedLeray.Short.PartIIa.Sub.N02_3
import UnforcedLeray.Short.PartIIa.Sub.N02_4_2
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N02_4_4
import UnforcedLeray.Short.PartIIa.Sub.N02_4_5.Cond
import UnforcedLeray.Short.PartIIa.Sub.N02_5.Cond
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.FlatSolenoid
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.FlatGradient
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.TruncConverge
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ModeSplit.IntervalParamSmooth

/-!
# The flat Leray part of a smooth force (organize task
`PartIII-b:C/flatset/col/7/1/1/2/4/2/4/2/1/1/org`)

Source of record `the November 2 reference manuscript`:
lines 1650-1656 (`A₀ = -S + νsΔ_{q,η}`, flat equation), 1676 (`P₀` the ordinary planar cylinder
projection), 1684-1689 (classical case of the flat equation), and the mode-by-mode description of
`P₀` in the proof of `near:compact-free-comparison`, lines 1713-1737: "on each nonzero
`q`-frequency, a flat solenoidal field and gradient have forms `(-ψ_η, ψ_q)`, `(φ_q, φ_η)`" and
"for the zero frequency, the radial component is solenoidal and the axial component is a gradient".

`P₀ = PepsC 0 c` is the orthogonal projection of `H = L²(s^{-3/2} ds dq dη)` onto `solenoidalHC 0 c`;
the weight depends only on `s`, so `P₀` acts in `(q, η)` at fixed age.  For a smooth band test `f`
(`IsMeridTest c f`) we write the explicit flat Leray part

`lerayPart c f = (f̄_r, 0) + Σ_{n ≠ 0} e^{2πinq/c} (-∂_η ψ_n, i k_n ψ_n)`,

where `f̄ = avgQ c f` is the zero frequency, `k_n = 2πn/c`, `(a_n, b_n)` are the `q`-Fourier
coefficients of the oscillating part `f - f̄` (`nzCoeff`), and `ψ_n = G_{k_n} * (i k_n b_n - ∂_η a_n)`
is the Green convolution in `η` (`nzConv`, `nzmsH2`) of `PartII-a:N02/4/5`.

The route reuses the compiled `PartII-a:N02` development:
* zero frequency: `zeroFlatProj_of zeroFlatSolenoid zeroFlatGradient` (`P₀ (f̄_r, f̄_z) = (f̄_r, 0)`);
* nonzero frequencies: the Fourier truncations `nzTrunc c N (f - f̄)` converge in `H`
  (`nzTruncConverge`); each truncation is `cgradC 0 Φ_N + streamC 0 Ψ_N` with smooth exponentially
  decaying potentials (`nzFpIdentity`, `nzFlatMembership`), so `P₀` of it is the finite stream sum
  `lerayTrunc c f N`; these converge pointwise to `lerayTail c f` (summable sup bounds `C/(1+n²)`),
  and an `L²` limit agrees a.e. with a pointwise limit.

`flatProjSmoothRegular_of` assembles `FlatProjSmoothRegular` from six lemma Props; the remaining
lemma Props below feed those six (each is one task).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.Short.PartIIa

/-! ### Concrete objects -/

/-- The complexified real field of a smooth force (`merC` pointwise). -/
def cplxField (F : Chart → Fin 2 → ℝ) : Profile → MeridC := fun p =>
  WithLp.toLp 2 fun i => ((F p i : ℝ) : ℂ)

/-- The oscillating part `f - f̄` of a profile (zero `q`-mean, source 1738). -/
def fOsc (c : ℝ) (f : Profile → MeridC) : Profile → MeridC := fun p => f p - avgQ c f p

/-- The radial `q`-Fourier coefficient `a_n(s, η)` of the oscillating part. -/
def coefR (c : ℝ) (f : Profile → MeridC) (n : ℤ) : ℝ × ℝ → ℂ := fun x =>
  nzCoeff c n (fOsc c f) x 0

/-- The axial `q`-Fourier coefficient `b_n(s, η)` of the oscillating part. -/
def coefZ (c : ℝ) (f : Profile → MeridC) (n : ℤ) : ℝ × ℝ → ℂ := fun x =>
  nzCoeff c n (fOsc c f) x 1

/-- `∂_η` of a function of `(s, η)`. -/
def dEta2 (a : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ := fderiv ℝ a x (0, 1)

/-- The flat stream potential of mode `n` (source 1713-1716): `ψ_n = G_{k_n} * (i k_n b_n - ∂_η a_n)`. -/
def psiN (c : ℝ) (f : Profile → MeridC) (n : ℤ) : ℝ × ℝ → ℂ :=
  nzConv (nzk c n) (nzmsH2 (nzk c n) (coefR c f n) (coefZ c f n))

/-- The flat gradient potential of mode `n` (source 1713-1716): `φ_n = G_{k_n} * (i k_n a_n + ∂_η b_n)`. -/
def phiN (c : ℝ) (f : Profile → MeridC) (n : ℤ) : ℝ × ℝ → ℂ :=
  nzConv (nzk c n) (nzmsH1 (nzk c n) (coefR c f n) (coefZ c f n))

/-- The flat solenoidal coefficient `(-∂_η ψ_n, i k_n ψ_n)` of mode `n ≠ 0`; `0` for `n = 0`
(the zero frequency is carried by `(f̄_r, 0)`). -/
def lerayMode (c : ℝ) (f : Profile → MeridC) (n : ℤ) (x : ℝ × ℝ) : MeridC :=
  if n = 0 then 0
  else !₂[-dEta2 (psiN c f n) x, Complex.I * ((nzk c n : ℂ) * psiN c f n x)]

/-- The Fourier character `e^{2πinq/c}` (the convention of `nzModeSum`, `nzTrunc`). -/
def eN (c : ℝ) (n : ℤ) (q : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))

/-- The nonzero frequencies `0 < |n| ≤ N` of `nzTrunc c N`. -/
def truncSet (N : ℕ) : Finset ℤ := (Finset.Icc (-(N : ℤ)) N).erase 0

/-- The flat Leray part of the truncation `nzTrunc c N (f - f̄)`: `Σ_{0<|n|≤N} e_n (-∂_ηψ_n, i k_n ψ_n)`. -/
def lerayTrunc (c : ℝ) (f : Profile → MeridC) (N : ℕ) (p : Profile) : MeridC :=
  ∑ n ∈ truncSet N, eN c n p.2.1 • lerayMode c f n (p.1, p.2.2)

/-- The flat Leray part of the oscillating part: `Σ_{n ∈ ℤ} e_n (-∂_ηψ_n, i k_n ψ_n)`. -/
def lerayTail (c : ℝ) (f : Profile → MeridC) (p : Profile) : MeridC :=
  ∑' n : ℤ, eN c n p.2.1 • lerayMode c f n (p.1, p.2.2)

/-- **The flat Leray part** `G = P₀ f` of a smooth band test (source 1676, 1713-1737):
`(f̄_r, 0)` plus the stream fields of the nonzero frequencies. -/
def lerayPart (c : ℝ) (f : Profile → MeridC) (p : Profile) : MeridC :=
  !₂[avgQ c f p 0, 0] + lerayTail c f p

/-! ### Lemma Props: the six inputs of the assembly -/

/-- **(A) Lift.** For a smooth force `g` with smooth representative `F` (`ageμ c (-3/2)`-a.e.,
`IsSmoothForce`), a lift `f'` of `g` (`SFCLift`) is `measureH c`-a.e. the complexified field
`cplxField F` (source 1641-1646: `H` on the cell `(0, c]`; `cellPt` recentres the cell and `F` is
`c`-periodic; `Masked.cpc_map_cellPt` maps `measureH c` to `c • ageμ c (-3/2)`). -/
def LiftAe : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (g : Hsp c) (f' : HSpace c MeridC) (F : Chart → Fin 2 → ℝ),
    (∀ s q η, F (s, (q + c, η)) = F (s, (q, η))) →
    (∀ᵐ p ∂(UnforcedLeray.Axi.ageμ c (-3 / 2)), ∀ i,
      UnforcedLeray.Short.PartIIIb.NearInst.velC g p i = ((F p i : ℝ) : ℂ)) →
    SFCLift g f' →
    (f' : Profile → MeridC) =ᵐ[measureH c] cplxField F

/-- **(B) Smooth forces are band tests.** The complexification of a smooth `c`-periodic band field is
an `IsMeridTest` (source 1684-1689). -/
def CplxMeridTest : Prop :=
  ∀ (c : ℝ) (F : Chart → Fin 2 → ℝ), (∀ i, ContDiff ℝ ∞ fun p => F p i) →
    (∀ s q η, F (s, (q + c, η)) = F (s, (q, η))) →
    (∃ s0 s1 L : ℝ, 0 < s0 ∧ ∀ p, F p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) →
    IsMeridTest c (cplxField F)

/-- **(C) Regularity of the flat Leray part** (source 1676, 1713-1737): `lerayPart c f` is continuous,
`c`-periodic in `q`, bounded, and vanishes below the age band of `f`. -/
def LerayPartBasic : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ f : Profile → MeridC, IsMeridTest c f →
    Continuous (lerayPart c f) ∧
      (∀ σ q η, lerayPart c f (σ, (q + c, η)) = lerayPart c f (σ, (q, η))) ∧
      (∃ M : ℝ, ∀ p, ‖lerayPart c f p‖ ≤ M) ∧
      (∃ s0 : ℝ, 0 < s0 ∧ ∀ p : Profile, p.1 < s0 → lerayPart c f p = 0)

/-- **(D) `P₀` of a Fourier truncation** (source 1713-1716, 1744-1745): the truncation
`nzTrunc c N (f - f̄) = cgradC 0 Φ_N + streamC 0 Ψ_N` (`nzFpIdentity`, potentials `phiN`, `psiN`),
`cgradC 0 Φ_N ∈ (solenoidalHC 0 c)ᗮ` and `streamC 0 Ψ_N ∈ solenoidalHC 0 c` (`nzFlatMembership`),
so `P₀` of any class of the truncation is the stream part `lerayTrunc c f N`. -/
def FinModeProj : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ f : Profile → MeridC, IsMeridTest c f → ∀ (N : ℕ) (F : HSpace c MeridC),
    (F : Profile → MeridC) =ᵐ[measureH c] nzTrunc c N (fOsc c f) →
    (PepsC 0 c F : Profile → MeridC) =ᵐ[measureH c] lerayTrunc c f N

/-- **(E) The stream sums converge pointwise** (summable bounds `C/(1+n²)`, `|e_n| = 1`). -/
def TruncTendsto : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ f : Profile → MeridC, IsMeridTest c f → ∀ p : Profile,
    Tendsto (fun N : ℕ => lerayTrunc c f N p) atTop (𝓝 (lerayTail c f p))

/-- **(F) An `L²` limit agrees a.e. with a pointwise limit of representatives** (a subsequence of an
`L²`-convergent sequence converges a.e.). -/
def AeLimitOfLp : Prop :=
  ∀ (c : ℝ) (X : ℕ → HSpace c MeridC) (Y : HSpace c MeridC) (S : ℕ → Profile → MeridC)
    (T : Profile → MeridC), Tendsto X atTop (𝓝 Y) →
    (∀ N, (X N : Profile → MeridC) =ᵐ[measureH c] S N) →
    (∀ p, Tendsto (fun N => S N p) atTop (𝓝 (T p))) →
    (Y : Profile → MeridC) =ᵐ[measureH c] T

/-! ### Lemma Props feeding (C), (D), (E) -/

/-- Derivatives `∂_q`, `∂_η` of a band test are band tests (the band is closed, so the test vanishes
near every point outside it; derivatives of a `c`-periodic function are `c`-periodic). -/
def MeridTestDeriv : Prop :=
  ∀ (c : ℝ) (g : Profile → MeridC), IsMeridTest c g → IsMeridTest c (pdQ g) ∧ IsMeridTest c (pdEta g)

/-- A band test is bounded (continuous; periodic in `q`; supported in a compact `(s, η)`-band). -/
def MeridTestBounded : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ g : Profile → MeridC, IsMeridTest c g → ∃ M : ℝ, ∀ p, ‖g p‖ ≤ M

/-- One integration by parts in `q` over the period `[0, c]`: `(∂_q g)^(n) = i k_n g^(n)` (the boundary
terms cancel by periodicity, `e^{-i k_n c} = 1`). -/
def CoeffPdQ : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ g : Profile → MeridC, IsMeridTest c g → ∀ (n : ℤ) (x : ℝ × ℝ),
    nzCoeff c n (pdQ g) x = (Complex.I * (nzk c n : ℂ)) • nzCoeff c n g x

/-- `∂_η` commutes with the `q`-coefficient (differentiation under the integral over `[0, c]`,
`IntervalParamSmooth`). -/
def CoeffDEta : Prop :=
  ∀ (c : ℝ) (g : Profile → MeridC), ContDiff ℝ ∞ g → ∀ (n : ℤ) (x : ℝ × ℝ),
    fderiv ℝ (nzCoeff c n g) x (0, 1) = nzCoeff c n (pdEta g) x

/-- The trivial bound `‖g^(n)‖ ≤ sup ‖g‖` (`|e^{-i k_n q}| = 1`, average over `[0, c]`). -/
def CoeffNormLe : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (g : Profile → MeridC) (M : ℝ), Continuous g → (∀ p, ‖g p‖ ≤ M) →
    ∀ (n : ℤ) (x : ℝ × ℝ), ‖nzCoeff c n g x‖ ≤ M

/-- Sup bound of the Green convolution: `∫ |G_k| = 1/k²`. -/
def GreenSup : Prop :=
  ∀ (k : ℝ), k ≠ 0 → ∀ (h : ℝ × ℝ → ℂ) (M : ℝ), Continuous h → (∀ y, ‖h y‖ ≤ M) →
    ∀ x : ℝ × ℝ, ‖nzConv k h x‖ ≤ M / k ^ 2

/-- The mode coefficients of the oscillating part are smooth and supported in one common
`(s, η)`-band (`nztt_coeff_smooth`, `nztt_coeff_zero`, band of `f - f̄`). -/
def CoefSmoothBand : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ f : Profile → MeridC, IsMeridTest c f →
    ∃ s0 s1 L : ℝ, 0 < s0 ∧ ∀ n : ℤ,
      ContDiff ℝ ∞ (coefR c f n) ∧ ContDiff ℝ ∞ (coefZ c f n) ∧
        NzBandJ s0 s1 L (coefR c f n) ∧ NzBandJ s0 s1 L (coefZ c f n)

/-- The explicit mode potentials are `NzDecay2` and solve the one-mode flat Hodge equations
(source 1713-1716; the construction of `nzModeSolve_of`, `Sub/N02_4_5/Cond.lean`). -/
def ModePotentials : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ f : Profile → MeridC, IsMeridTest c f → ∀ n : ℤ, n ≠ 0 →
    NzDecay2 (phiN c f n) ∧ NzDecay2 (psiN c f n) ∧
      NzModeEq (nzk c n) (coefR c f n) (coefZ c f n) (phiN c f n) (psiN c f n)

/-- Each solenoidal mode coefficient is continuous in `(s, η)`. -/
def LerayModeCont : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ f : Profile → MeridC, IsMeridTest c f → ∀ n : ℤ,
    Continuous (lerayMode c f n)

/-- The solenoidal mode coefficients vanish below the age band of `f` (`nzConv_eq_zero`). -/
def LerayModeSupp : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ f : Profile → MeridC, IsMeridTest c f →
    ∃ s0 : ℝ, 0 < s0 ∧ ∀ (n : ℤ) (x : ℝ × ℝ), x.1 < s0 → lerayMode c f n x = 0

/-- The stream field of the finite potential sum is the finite solenoidal sum (`nzFpDeriv`). -/
def TruncStreamEq : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ f : Profile → MeridC, IsMeridTest c f → ∀ (N : ℕ) (p : Profile),
    streamC 0 (nzModeSum c (truncSet N) (psiN c f)) p = lerayTrunc c f N p

/-- Fourier decay of the data entering `ψ_n` (two integrations by parts in `q`): `b_n`, `∂_η a_n`,
`∂_η b_n`, `∂_η² a_n` are `O(k_n⁻²)` uniformly in `(s, η)`. -/
def ModeDataBounds : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ f : Profile → MeridC, IsMeridTest c f → ∃ D : ℝ, ∀ n : ℤ, n ≠ 0 →
    ∀ x : ℝ × ℝ,
      ‖coefZ c f n x‖ ≤ D / nzk c n ^ 2 ∧ ‖dEta2 (coefR c f n) x‖ ≤ D / nzk c n ^ 2 ∧
        ‖dEta2 (coefZ c f n) x‖ ≤ D / nzk c n ^ 2 ∧
          ‖dEta2 (dEta2 (coefR c f n)) x‖ ≤ D / nzk c n ^ 2

/-- Summable sup bound of the solenoidal mode coefficients: `‖(-∂_ηψ_n, i k_n ψ_n)‖ ≤ C/(1+n²)`. -/
def LerayModeBound : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ f : Profile → MeridC, IsMeridTest c f → ∃ C : ℝ,
    ∀ (n : ℤ) (x : ℝ × ℝ), ‖lerayMode c f n x‖ ≤ C / (1 + (n : ℝ) ^ 2)

/-! ### Assembly -/

theorem fOsc_isMeridTest {c : ℝ} (hc : 0 < c) {f : Profile → MeridC} (hf : IsMeridTest c f) :
    IsMeridTest c (avgQ c f) ∧ IsMeridTest c (fOsc c f) ∧ QMeanZero c (fOsc c f) := by
  have hA : IsMeridTest c (avgQ c f) :=
    isMeridTest_avgQ hf (avgSmooth_of intervalParamSmooth_proof c hc f hf)
  exact ⟨hA, isMeridTest_sub_avgQ hf hA, qMeanZero_sub_avgQ hc hf⟩

/-- **`FlatProjSmoothRegular` from the six lemma Props (proved).** `f' = f̄ + (f - f̄)` in `H`;
`P₀ f̄ = (f̄_r, 0)` (`zeroFlatProj_of`); `P₀ (f - f̄) = lim P₀ (truncations) = lerayTail` a.e. -/
theorem flatProjSmoothRegular_of (hLift : LiftAe) (hCplx : CplxMeridTest)
    (hBasic : LerayPartBasic) (hFin : FinModeProj) (hTend : TruncTendsto) (hAe : AeLimitOfLp) :
    FlatProjSmoothRegular := by
  intro c hc g f' hs hl
  obtain ⟨F, hFs, hFp, hFb, hFae⟩ := hs
  have hf : IsMeridTest c (cplxField F) := hCplx c F hFs hFp hFb
  have hf' : (f' : Profile → MeridC) =ᵐ[measureH c] cplxField F := hLift c hc g f' F hFp hFae hl
  obtain ⟨hcont, hper, hbd, hsupp⟩ := hBasic c hc _ hf
  refine ⟨lerayPart c (cplxField F), hcont, hper, hbd, hsupp, ?_⟩
  obtain ⟨hA, hO, hOm⟩ := fOsc_isMeridTest hc hf
  have mA : MemLp (avgQ c (cplxField F)) 2 (measureH c) := avgMemLp_of_isMeridTest hA
  have mO : MemLp (fOsc c (cplxField F)) 2 (measureH c) := avgMemLp_of_isMeridTest hO
  have hsplit : f' = mA.toLp _ + mO.toLp _ := by
    apply Lp.ext
    filter_upwards [hf', Lp.coeFn_add (mA.toLp _) (mO.toLp _), mA.coeFn_toLp, mO.coeFn_toLp]
      with p h1 h2 h3 h4
    rw [h1, h2, Pi.add_apply, h3, h4]
    simp [fOsc]
  have hZ := (zeroFlatProj_of zeroFlatSolenoid zeroFlatGradient c (avgQ c (cplxField F))
    (mA.toLp _) hc hA (qInvariant_avgQ c _) mA.coeFn_toLp).1
  obtain ⟨FN, hFN, hlim⟩ := nzTruncConverge c hc (fOsc c (cplxField F)) hO hOm (mO.toLp _)
    mO.coeFn_toLp
  have hlimP : Tendsto (fun N => PepsC 0 c (FN N)) atTop (𝓝 (PepsC 0 c (mO.toLp _))) :=
    ((PepsC 0 c).continuous.tendsto _).comp hlim
  have hO' : (PepsC 0 c (mO.toLp _) : Profile → MeridC) =ᵐ[measureH c]
      lerayTail c (cplxField F) :=
    hAe c _ _ _ _ hlimP (fun N => hFin c hc _ hf N (FN N) (hFN N)) (hTend c hc _ hf)
  have hP : PepsC 0 c f' = PepsC 0 c (mA.toLp _) + PepsC 0 c (mO.toLp _) := by
    rw [hsplit, map_add]
  rw [hP]
  filter_upwards [Lp.coeFn_add (PepsC 0 c (mA.toLp _)) (PepsC 0 c (mO.toLp _)), hZ, hO']
    with p h1 h2 h3
  rw [h1, Pi.add_apply, h3]
  unfold PepsC
  rw [h2]
  rfl

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray
