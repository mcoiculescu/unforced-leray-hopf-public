import UnforcedLeray.Blueprint.Construction.Planar
import UnforcedLeray.Lib.PlanarSpectralB.XGSpectrum
import UnforcedLeray.Lib.PlanarSpectralB.Complement
import UnforcedLeray.Lib.PlanarSectorsB.DilationPlane
import UnforcedLeray.Units.B0009
import UnforcedLeray.Units.B0094
import UnforcedLeray.Units.B0121

/-!
# Part I, module `seed-train/lin-seed.tex`: the Gaussian seed (statements)

Source of record: `the November 2 reference manuscript`, lines 556-958
(Proposition `prop:short-gaussian-seed`, statement lines 592-624, proof 626-929;
Corollary `cor:short-seed-dilation`, lines 931-953).  All declarations are `Prop`-valued
definitions (no `sorry`, no axioms).

## Reused Lean objects (existing names)

* `B0010.XG` and `Planar.L0 : XG →L[ℂ] XG` (`Lib/PlanarSectors/XG.lean`): the Gaussian space
  `X_G` of angular-two profiles and `L_0 = -2iΩ + 2ikR`.
* `Infra.Dunford.IsSimpleSpectralProj`, `Infra.Dunford.rankOneProj` (`Lib/Semigroups/Dunford`):
  the Riesz projection of a simple isolated eigenvalue, and `f ↦ ℓ(f) q`.
* `B0008.HjM, B0008.XjM, B0008.MemHjM`; `B0009.generator j hM : XjM j M →ₗ.[ℂ] (ℂ →ₘ ℂ)`,
  the full Euler generator `𝓛f = -Ω∂_ϑ f - (Kf)·∇E₀` on `𝒟(𝓛) = {f ∈ 𝒳_{j,M} : Ω∂_ϑ f ∈ H^j_M}`;
  `B0009.biotSavart` (planar Biot-Savart velocity `K`).
* `Planar.eulerGroupW hM t : L2w M →L L2w M`, the Euler evolution `e^{t𝓛}` on `L²_M` (sector
  sums of `exp(t 𝓛_n)`); for `f ∈ 𝒳_{j,M} ⊆ L²_M` the evolution on `H^j_M` is its restriction
  (the source: "resolvents, hence Riesz projections, agree on intersections of weighted spaces").
* `Planar.LsecDil, Planar.dilP, Planar.dilX0, Planar.eulerSemigroupDil`: the frozen generators.
* `B0094.D` (the selfadjoint `D = Δ + ½y·∇ + 2` on `X_G`), `B0094.isSelfAdjoint_D`,
  `B0094.D_nonpos`, `B0094.opSpectrum_D`; `B0121.XGj j = X_{G,j} = 𝒟((I-D)^{j/2})`.
* `Planar.NUE.Polar.angularSector g n r = g_n(r)` (the angular Fourier coefficient).

## How the unique objects are pinned down (no free data)

`IsSeedXG lam q ℓ` says: `Re lam > 0`, `q ≠ 0` is an eigenvector of `L_0` for `lam`, and
`rankOneProj ℓ q` is the (Laurent-form) Riesz projection of the simple isolated eigenvalue `lam`.
By `B0088` (`Planar.spectrum_L0_rightHalf_eq_singleton`) the growing spectrum is a single point,
so `(lam, q, ℓ)` is the source's `(λ, q, ℓ)` up to the eigenvector gauge `q ↦ cq`, `ℓ ↦ c⁻¹ℓ`.
All results below are universally quantified over such triples (and over a profile `h` of `q`),
and `SeedXGExists` asserts that a triple exists.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology ComplexConjugate

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Infra.Dunford (IsSimpleSpectralProj rankOneProj)

/-- The planar function `q = h(r) e^{2iϑ}` of the angular-two profile `h`. -/
abbrev seedPlanar (h : ℝ → ℂ) : ℂ → ℂ := Planar.NUE.Ang.ofProfile 2 h

/-- `J_q = ∫₀^∞ h(r)²/k(r) r dr` (line 603, eq. `short-seed-functional`); `k = E₀'/r`
(`Blueprint.Planar.strainK`).  The integrand is defined off the single zero `r = √8` of `k`
(the source: "the quotients at `k = 0` are removable"). -/
def seedJ (h : ℝ → ℂ) : ℂ :=
  ∫ r in Ioi (0 : ℝ), h r ^ 2 / (Blueprint.Planar.strainK r : ℂ) * (r : ℂ)

/-- `ℓ(f) = J_q⁻¹ ∫₀^∞ h(r) f₂(r)/k(r) r dr` (eq. `short-seed-functional`, lines 601-604), for
the angular-two profile `f₂` of `f`. -/
def seedEll (h f : ℝ → ℂ) : ℂ :=
  (seedJ h)⁻¹ * ∫ r in Ioi (0 : ℝ), h r * f r / (Blueprint.Planar.strainK r : ℂ) * (r : ℂ)

/-- The projection `𝒫` onto the growing pair, on planar functions: `𝒫f = ℓ(f₂) q + \overline{ℓ(\bar f_{-2})}\,\bar q`
(sector `2` gets `q ℓ`, sector `-2` its complex conjugate). -/
def seedProjFun (h : ℝ → ℂ) (f : ℂ → ℂ) (y : ℂ) : ℂ :=
  seedEll h (Planar.NUE.Polar.angularSector f 2) * seedPlanar h y +
    (starRingEnd ℂ) (seedEll h (fun r => (starRingEnd ℂ) (Planar.NUE.Polar.angularSector f (-2) r))) *
      (starRingEnd ℂ) (seedPlanar h y)

/-- The data `(λ, q, ℓ)` of Proposition `short-gaussian-seed` on `X_G`: `Re λ > 0`, `q ≠ 0` with
`L_0 q = λ q`, and `P = qℓ` the Riesz projection of the simple isolated eigenvalue `λ` of `L_0`. -/
structure IsSeedXG (lam : ℂ) (q : B0010.XG) (ℓ : B0010.XG →L[ℂ] ℂ) : Prop where
  re_pos : 0 < lam.re
  ne_zero : q ≠ 0
  eigen : Planar.L0 q = lam • q
  ell_q : ℓ q = 1
  proj : IsSimpleSpectralProj Planar.L0 (rankOneProj ℓ q) lam

/-- **Existence of the growing pair** (Prop. `short-gaussian-seed`, lines 593-597; proof: lines
626-808 and 841-929). -/
def SeedXGExists : Prop :=
  ∃ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
    IsSeedXG lam (hh.toLp h) ℓ

/-- **Regularity and decay of the mode** (lines 593-601): `-2 < ω < 0`; `q = h(r)e^{2iϑ}` has
every derivative bounded by a polynomial times `e^{-r²/4}`, `∫ q = 0`, the velocity `Kq` is in
`L²`, `q ∈ H^j_M` for all `j, M`, and the quadrupole `M_q = ∫₀^∞ r³ h dr` is a convergent
integral and `≠ 0`. -/
def SeedModeRegularity : Prop :=
  ∀ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
    IsSeedXG lam (hh.toLp h) ℓ →
      -2 < lam.im ∧ lam.im < 0 ∧
      ∃ h' : ℝ → ℂ, h' =ᵐ[volume.restrict (Ioi (0 : ℝ))] h ∧
        ContDiff ℝ ∞ (seedPlanar h') ∧
        (∀ k : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∀ y : ℂ,
          ‖iteratedFDeriv ℝ k (seedPlanar h') y‖ ≤ C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4)) ∧
        Integrable (seedPlanar h') volume ∧ (∫ y, seedPlanar h' y = 0) ∧
        (∀ (j : ℕ) (M : ℝ), B0008.MemHjM j M (seedPlanar h')) ∧
        (∀ i : Fin 2, MemLp (B0009.biotSavart (seedPlanar h') i) 2 volume) ∧
        IntegrableOn (fun r : ℝ => (r : ℂ) ^ 3 * h' r) (Ioi 0) volume ∧
        Blueprint.Planar.quadrupole h' ≠ 0

/-- **Growing spectrum of `L_0` on `X_G`** (line 602: "the same `λ` is the sole growing spectral
value of `L_0` on `X_G`"). -/
def SeedXGSpectrum : Prop :=
  ∀ (lam : ℂ) (q : B0010.XG) (ℓ : B0010.XG →L[ℂ] ℂ), IsSeedXG lam q ℓ →
    {z : ℂ | 0 < z.re} ∩ spectrum ℂ Planar.L0 = {lam}

/-- **The explicit functional `ℓ`** (eq. `short-seed-functional`, lines 603-609): `J_q ≠ 0`, the
integrals defining `J_q` and `ℓ(f)`, `f ∈ X_G`, converge, `ℓ(f) = J_q⁻¹ ∫ h f₂ / k r dr` for all
`f ∈ X_G`, and for the smooth representative `h` the quotient `h/k` extends to a smooth function
on `(0,∞)` that is `O(r⁻²)` at infinity (removable singularity at `k = 0`). -/
def SeedFunctional : Prop :=
  ∀ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
    IsSeedXG lam (hh.toLp h) ℓ →
      seedJ h ≠ 0 ∧
      IntegrableOn (fun r : ℝ => h r ^ 2 / (Blueprint.Planar.strainK r : ℂ) * (r : ℂ)) (Ioi 0) volume ∧
      (∀ f : B0010.XG, IntegrableOn
        (fun r : ℝ => h r * (f : ℝ → ℂ) r / (Blueprint.Planar.strainK r : ℂ) * (r : ℂ))
        (Ioi 0) volume) ∧
      (∀ f : B0010.XG, ℓ f = seedEll h (f : ℝ → ℂ)) ∧
      (ContDiffOn ℝ ∞ h (Ioi 0) →
        ∃ g : ℝ → ℂ, ContDiffOn ℝ ∞ g (Ioi 0) ∧
          (∀ r : ℝ, 0 < r → Blueprint.Planar.strainK r ≠ 0 → g r = h r / (Blueprint.Planar.strainK r : ℂ)) ∧
          ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r → ‖g r‖ ≤ C / r ^ 2)

/-- **The harmonic-strain input** (lines 609-610): `H = r² k(r) e^{2iϑ}` has
`ℓ(H) = M_q/J_q ≠ 0`. -/
def SeedStrainCoupling : Prop :=
  ∀ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
    IsSeedXG lam (hh.toLp h) ℓ →
      seedEll h Blueprint.Planar.strainProfile = Blueprint.Planar.quadrupole h / seedJ h ∧
      seedEll h Blueprint.Planar.strainProfile ≠ 0

/-! ### The full Euler generator on `𝒳_{j,M}` -/

/-- The value (a function on the plane) of an element of `𝒳_{j,M}`. -/
def xValue {j : ℕ} {M : ℝ} (F : B0008.XjM j M) : ℂ → ℂ :=
  ⇑((F : B0008.HjM j M).value)

/-- `F` is an eigenvector of the full Euler generator `𝓛` on `𝒳_{j,M}` for the eigenvalue `z`:
`F ∈ 𝒟(𝓛)`, `F ≠ 0`, `𝓛F = zF` a.e. -/
def IsEulerEigen (j : ℕ) {M : ℝ} (hM : 1 < M) (z : ℂ) (F : (B0009.generator j hM).domain) : Prop :=
  F ≠ 0 ∧ (⇑(B0009.generator j hM F) : ℂ → ℂ) =ᵐ[volume] fun y => z * xValue (F : B0008.XjM j M) y

/-- `z` lies in the resolvent set of the full Euler generator on `𝒳_{j,M}`: `z - 𝓛` is injective
on `𝒟(𝓛)` and has a bounded right inverse onto `𝒳_{j,M}`. -/
def EulerResolvent (j : ℕ) {M : ℝ} (hM : 1 < M) (z : ℂ) : Prop :=
  (∀ F : (B0009.generator j hM).domain, ¬ IsEulerEigen j hM z F) ∧
  ∃ C : ℝ, ∀ g : B0008.XjM j M, ∃ F : (B0009.generator j hM).domain,
    (⇑(B0009.generator j hM F) : ℂ → ℂ) =ᵐ[volume]
      (fun y => z * xValue (F : B0008.XjM j M) y - xValue g y) ∧
    ‖(F : B0008.XjM j M)‖ ≤ C * ‖g‖

/-- **Spectrum of `𝓛` on every `𝒳_{j,M}`** (lines 593-598): in `{Re z > 0}` the spectrum is the
conjugate pair `λ, \bar λ`; the eigenspaces are `ℂq` and `ℂ\bar q`; both eigenvalues are
algebraically simple (no Jordan vector). -/
def SeedEulerSpectrum : Prop :=
  ∀ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
    IsSeedXG lam (hh.toLp h) ℓ → ∀ (j : ℕ) (M : ℝ) (hM : 1 < M),
      (∀ z : ℂ, 0 < z.re → z ≠ lam → z ≠ (starRingEnd ℂ) lam → EulerResolvent j hM z) ∧
      (∃ F, IsEulerEigen j hM lam F) ∧ (∃ F, IsEulerEigen j hM ((starRingEnd ℂ) lam) F) ∧
      (∀ F : (B0009.generator j hM).domain, IsEulerEigen j hM lam F ↔
        ∃ c : ℂ, c ≠ 0 ∧ xValue (F : B0008.XjM j M) =ᵐ[volume] fun y => c * seedPlanar h y) ∧
      (∀ F : (B0009.generator j hM).domain, IsEulerEigen j hM ((starRingEnd ℂ) lam) F ↔
        ∃ c : ℂ, c ≠ 0 ∧ xValue (F : B0008.XjM j M) =ᵐ[volume]
          fun y => c * (starRingEnd ℂ) (seedPlanar h y)) ∧
      (∀ F : (B0009.generator j hM).domain, IsEulerEigen j hM lam F →
        ¬ ∃ G : (B0009.generator j hM).domain, (⇑(B0009.generator j hM G) : ℂ → ℂ) =ᵐ[volume]
          fun y => lam * xValue (G : B0008.XjM j M) y + xValue (F : B0008.XjM j M) y) ∧
      (∀ F : (B0009.generator j hM).domain, IsEulerEigen j hM ((starRingEnd ℂ) lam) F →
        ¬ ∃ G : (B0009.generator j hM).domain, (⇑(B0009.generator j hM G) : ℂ → ℂ) =ᵐ[volume]
          fun y => (starRingEnd ℂ) lam * xValue (G : B0008.XjM j M) y + xValue (F : B0008.XjM j M) y)

/-- **First complement estimate, eq. `short-seed-complement`** (lines 612-615): for every
`η > 0` there is `C_{j,M,η}` with `‖e^{t𝓛}(I - 𝒫)‖_{H^j_M → H^j_M} ≤ C e^{ηt}` for `t ≥ 0`; here
`e^{t𝓛}` on `H^j_M` is the restriction of the Euler group on `L²_M`, and `𝒫` the projection onto the
growing pair (`seedProjFun`); the statement includes that `H^j_M` is invariant. -/
def SeedEulerComplement : Prop :=
  ∀ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
    IsSeedXG lam (hh.toLp h) ℓ → ∀ (j : ℕ) (M : ℝ) (hM : 1 < M) (η : ℝ), 0 < η →
      ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ f : B0008.XjM j M,
        ∃ (u : Planar.L2w M) (g : B0008.XjM j M),
          (⇑u =ᵐ[volume] fun y => xValue f y - seedProjFun h (xValue f) y) ∧
          xValue g =ᵐ[volume] ⇑(Planar.eulerGroupW hM t u) ∧
          ‖g‖ ≤ C * Real.exp (η * t) * ‖f‖

/-- **Second complement estimate, eq. `short-seed-complement`** (lines 616-617): with
`Q = I - P`, `‖e^{t(L₀-λ)}Q‖_{X_G → X_G} ≤ C_η e^{-(γ-η)t}` for all `η > 0`, `t ≥ 0`,
`γ = Re λ`. -/
def SeedXGComplement : Prop :=
  ∀ (lam : ℂ) (q : B0010.XG) (ℓ : B0010.XG →L[ℂ] ℂ), IsSeedXG lam q ℓ →
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp ((t : ℂ) • (Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG))) *
          (1 - rankOneProj ℓ q)‖ ≤ C * Real.exp (-(lam.re - δ) * t)

/-- **The oscillator `D`** (lines 619-623, proof 890-929): `D = Δ + ½ y·∇ + 2` is selfadjoint and
nonpositive on `X_G` with spectrum `{0,-1,-2,…}`; `q` and the normalized Gaussian adjoint vector
`q†` (`ℓ = ⟨·, q†⟩`) lie in every power domain `X_{G,j}`, and `DP`, `PD` extend boundedly: `DP` is
everywhere defined and bounded, and there is a bounded `B` with `B f = P(Df)` on `𝒟(D)`. -/
def SeedOscillator : Prop :=
  IsSelfAdjoint B0094.D ∧
  (∀ f : B0094.D.domain, (inner ℂ (f : B0010.XG) (B0094.D f)).re ≤ 0) ∧
  B0094.opSpectrum B0094.D = Set.range (fun n : ℕ => -(n : ℂ)) ∧
  ∀ (lam : ℂ) (q : B0010.XG) (ℓ : B0010.XG →L[ℂ] ℂ), IsSeedXG lam q ℓ →
    (∀ j : ℕ, q ∈ B0121.XGj j) ∧
    (∀ qd : B0010.XG, (∀ f, ℓ f = inner ℂ qd f) → ∀ j : ℕ, qd ∈ B0121.XGj j) ∧
    (∃ hq : q ∈ B0094.D.domain, ∃ T : B0010.XG →L[ℂ] B0010.XG,
        ∀ f : B0010.XG, T f = ℓ f • B0094.D ⟨q, hq⟩) ∧
    (∃ T : B0010.XG →L[ℂ] B0010.XG, ∀ (f : B0010.XG) (hf : f ∈ B0094.D.domain),
        T f = ℓ (B0094.D ⟨f, hf⟩) • q)

/-! ### Corollary `short-seed-dilation` -/

/-- **Frozen heat profiles, generators** (lines 931-953): `J_af = a⁻²f(·/√a)`; the Euler
generators `𝓛_a` of the frozen vortices satisfy `𝓛_a = a⁻²J_a𝓛J_a⁻¹` (sector by sector, `n ∈ ℤ`),
and the unstable eigenvalues are `a⁻²λ`, `a⁻²\bar λ` with eigenvectors `J_aq`, `J_a\bar q`. -/
def SeedDilationGenerator : Prop :=
  (∀ (M : ℝ) (hM : 1 < M) (a : ℝ) (ha : 0 < a) (n : ℤ),
    Planar.LsecDil hM ha n =
      (((a ^ 2)⁻¹ : ℝ) : ℂ) •
        (Planar.dilP hM ha ∘L Planar.Lsec hM n ∘L Planar.dilP hM (inv_pos.2 ha))) ∧
  ∀ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
    IsSeedXG lam (hh.toLp h) ℓ → ∀ (M : ℝ) (hM : 1 < M) (a : ℝ) (ha : 0 < a),
      ∃ (hq : MemLp h 2 (Planar.profileMeasure M))
        (hq' : MemLp (fun r => (starRingEnd ℂ) (h r)) 2 (Planar.profileMeasure M)),
        Planar.LsecDil hM ha 2 (Planar.dilP hM ha (hq.toLp h)) =
          ((((a ^ 2)⁻¹ : ℝ) : ℂ) * lam) • Planar.dilP hM ha (hq.toLp h) ∧
        Planar.LsecDil hM ha (-2) (Planar.dilP hM ha (hq'.toLp _)) =
          ((((a ^ 2)⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) lam) • Planar.dilP hM ha (hq'.toLp _)

/-- **Frozen heat profiles, projections and uniform complement** (lines 931-953): `𝒫_a =
J_a𝒫J_a⁻¹` depends continuously on `a ∈ [1,A]` in operator norm (on `𝒳_{0,M}`) and the
complementary estimates `‖e^{t𝓛_a}(I - 𝒫_a)‖ ≤ C e^{ηt}` are uniform for `1 ≤ a ≤ A`. -/
def SeedDilationProjection : Prop :=
  ∀ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
    IsSeedXG lam (hh.toLp h) ℓ → ∀ (M : ℝ) (hM : 1 < M) (A : ℝ), 1 ≤ A →
      ∃ P : Planar.X0 hM →L[ℂ] Planar.X0 hM,
        (∀ f : Planar.X0 hM, ⇑((P f : Planar.X0 hM) : Planar.L2w M) =ᵐ[volume]
          fun y => seedProjFun h (⇑((f : Planar.X0 hM) : Planar.L2w M)) y) ∧
        Continuous (fun a : Icc (1 : ℝ) A =>
          Planar.dilX0 hM (lt_of_lt_of_le one_pos a.2.1) ∘L P ∘L
            Planar.dilX0 hM (inv_pos.2 (lt_of_lt_of_le one_pos a.2.1))) ∧
        ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (ha : 0 < a), 1 ≤ a → a ≤ A →
          ∀ t : ℝ, 0 ≤ t →
            ‖Planar.eulerSemigroupDil hM ha t ∘L
                (1 - Planar.dilX0 hM ha ∘L P ∘L Planar.dilX0 hM (inv_pos.2 ha))‖ ≤
              C * Real.exp (η * t)

end UnforcedLeray.Short.PartI
