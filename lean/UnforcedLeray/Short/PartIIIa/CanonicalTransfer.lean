import UnforcedLeray.Short.PartIIIa.FullClock
import UnforcedLeray.Short.PartI.TrainClass

/-!
# Part III-a, module `tails/canonical-transfer.tex` (SP 3106-3404)

From the plane branch to the actual train output: the actual bare column
`w(s) = 𝒰_{ν,c}(s,0)P_c q_{1/ν}` (a weak linearised flow, `IsLinearisedFlow`, from the prepared
datum), its heat coordinates `Z(θ)`, the periodized canonical branch `V_d = P_d V_can`, and the
results `eq:ct-embeddings`, `-kinetic-impulse`, `-partial-moment`, `-tested-impulse`,
`-long-comparison`, `-compact-comparison`, `-mellin`, `-absolute-stress`, `-stress-defect`,
`-anisotropy`.

Reused Lean: `Blueprint.Planar.PlanarData`, `IsPlanarReference` (λ, κ, `V_can`, `quadrupole`,
`gaugeFactor`), `B0140.TrainSol`, `IsLinearisedFlow`, `IsBiotSavart`, `xNorm` (`Defs.lean`).

Omitted (documented in the report): `eq:ct-moving-period`, `eq:ct-base-error`,
`eq:ct-long-residual`, `eq:ct-late-residual` (the residual of `V_d` in the heat-coordinate
generator `𝓛_θ = θ⁻¹D + L_{ν,c}`, to be stated against Part I's generator), `eq:ct-absolute-impulse`,
and the negative-channel versions (complex conjugates). The periodization is a `tsum`; it is
summable for the canonical branch (Gaussian pointwise tails, Part I), so no junk value enters.

The train. Every statement over the actual train assumes the BUC class `PartI.IsBUCTrain tr`
(`Short/PartI/TrainClass.lean`, the train of `sct:train`, source lines 270-288): the proofs use the
train comparison `sct:comparison` (lines 3164-3168), the integrated strain `sct:integrated`
(line 3243) and the train energy bounds before and after overlap (lines 3260-3264, 3374-3376),
none of which follows from `B0140.IsTrain`. The `ν → 0` statements (`eq:ct-compact-comparison`,
`-mellin`, `-absolute-stress`, `-stress-defect`, `-anisotropy`) are stated for every small `ν`,
every BUC train `tr` and every actual column `w` from the prepared datum (uniformly in `tr`, `w`);
they are not stated over families `ν ↦ TrainSol ν (ν^{-2})` indexed by all real `ν`, which
would also need trains at `ν ≤ 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- `e^{2iϑ} = (x₁ + i x₂)²/|x|²` on the plane. -/
def angTwo (x : ℝ × ℝ) : ℂ :=
  ((x.1 : ℂ) + (x.2 : ℂ) * Complex.I) ^ 2 / ((x.1 ^ 2 + x.2 ^ 2 : ℝ) : ℂ)

/-- The planar angular-two function `f₂(r)e^{2iϑ}` of a radial profile. -/
def planarMode (f : Profile) (x : ℝ × ℝ) : ℂ :=
  f (Real.sqrt (x.1 ^ 2 + x.2 ^ 2)) * angTwo x

/-- The periodization `(P_d g)(q, η) = ∑_n g(q - nd, η)` (SP 3114). -/
def periodizeC (d : ℝ) (g : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  ∑' n : ℤ, g (x.1 - n * d, x.2)

/-- The prepared datum `φ_{ν,c} = P_c q_{1/ν}`, `q_R = e^{λR}R^κ V_can(R)`, `c = ν^{-2}`
(SP 3127-3130, B0314). -/
def preparedDatum (P : PlanarData) (ν : ℝ) : ℝ × ℝ → ℂ :=
  periodizeC (ν ^ (-2 : ℝ)) (planarMode (fun r =>
    Complex.exp (P.eigenvalue * ((ν⁻¹ : ℝ) : ℂ)) * ((ν⁻¹ : ℝ) : ℂ) ^ P.kappa *
      P.canonical ν⁻¹ r))

/-- The cell length `d(θ) = √(θ/e)`, `e = ν³` (SP 3109-3110). -/
def dOfTheta (ν θ : ℝ) : ℝ := Real.sqrt (θ / ν ^ 3)

/-- The heat-coordinate column `Z(θ, y) = (a²/N) w(s, √a y)`, `a = (νθ)⁻¹`,
`s = clockAge ν θ`, `N = e^{λ/ν}ν^{-κ}` (SP 3127-3130, 3296-3303). -/
def heatColumn (P : PlanarData) (ν : ℝ) (w : ℝ → ℝ × ℝ → ℂ) (θ : ℝ) : ℝ × ℝ → ℂ :=
  fun y => (P.gaugeFactor ν)⁻¹ * JscaleInv (ν * θ)⁻¹ (w (clockAge ν θ)) y

/-- The periodized canonical branch `V_d(θ) = P_{d(θ)} V_can(θ)`. -/
def canonicalPeriodized (P : PlanarData) (ν θ : ℝ) : ℝ × ℝ → ℂ :=
  periodizeC (dOfTheta ν θ) (planarMode (P.canonical θ))

/-- `Q_d f = -(2/π)∫_{cell d} η² f` (SP 3178). -/
def quadQ (d : ℝ) (f : ℝ × ℝ → ℂ) : ℂ :=
  -((2 / Real.pi : ℝ) : ℂ) * ∫ x in B0579.cell d, ((x.2 ^ 2 : ℝ) : ℂ) * f x

/-- Central evenness `f(-x) = f(x)`. -/
def IsCentrallyEven (f : ℝ × ℝ → ℂ) : Prop := ∀ x, f (-x) = f x

/-- The `L²(cell d)` norm of a velocity field. -/
def velNorm (d : ℝ) (u : ℝ × ℝ → Fin 2 → ℂ) : ℝ≥0∞ :=
  (∑ j : Fin 2, eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell d)) ^ 2) ^ (1 / 2 : ℝ)

/-- `‖K_d f‖₂`: the `L²` norm of the (unique) Biot-Savart velocity; `⊤` if there is none. -/
def kinNorm (d : ℝ) (f : ℝ × ℝ → ℂ) : ℝ≥0∞ :=
  ⨅ (u : ℝ × ℝ → Fin 2 → ℂ) (_ : IsBiotSavart d f u), velNorm d u

/-- `Zh = 𝒰_Z(θ, r)h`: the heat-coordinate evolution from clock `r` to clock `θ ≤ r` of the datum
`h` (on the cell of length `d(r)`) along the actual linearised flow (SP 3190-3195). -/
def HeatEvolvesTo (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r θ : ℝ)
    (h Zh : ℝ × ℝ → ℂ) : Prop :=
  ∃ w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr (clockAge ν r) (Jscale (ν * r)⁻¹ h) w u ∧
    Zh = JscaleInv (ν * θ)⁻¹ (w (clockAge ν θ))

/-- **`eq:ct-embeddings`** (SP 3176-3184): `|Q_d f| + ‖K_d f‖₂ ≤ C_m ‖f‖_{X_{m,d}}`, uniformly in
`d ≥ 1`, on the centrally even zero-circulation class. -/
def CTEmbeddings : Prop :=
  ∀ m : ℝ, 8 < m → ∃ C : ℝ, ∀ d : ℝ, 1 ≤ d → ∀ f : ℝ × ℝ → ℂ,
    MemLp f 2 (B0579.cellMeasure d m) → HasZeroCirculation d f → IsCentrallyEven f →
      ∀ u, IsBiotSavart d f u →
        ENNReal.ofReal ‖quadQ d f‖ + velNorm d u ≤ ENNReal.ofReal C * xNorm d m f

/-- **`eq:ct-long-comparison`** (source lines 3193-3224), for every BUC train `tr`, with the
existence of the actual column: for
`b ≤ θ ≤ Θ = ν⁻¹`,
`‖e^{λθ}θ^κ(Z - V_d)(θ)‖_{X_{m,d(θ)}} ≤ C_b{ν + e²/θ + e^{-a₁θ/e}}`, `e = ν³`. -/
def CTLongComparison : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ m : ℝ, 8 < m → ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b →
    ∃ (C a₁ ν₀ : ℝ), 0 < a₁ ∧ 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr →
        (∃ w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr 0 (preparedDatum P ν) w u) ∧
        ∀ w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr 0 (preparedDatum P ν) w u →
          ∀ θ : ℝ, b ≤ θ → θ ≤ ν⁻¹ →
            ENNReal.ofReal (Real.exp (P.eigenvalue.re * θ) * θ ^ P.kappa.re) *
                xNorm (dOfTheta ν θ) m (heatColumn P ν w θ - canonicalPeriodized P ν θ) ≤
              ENNReal.ofReal (C * (ν + (ν ^ 3) ^ 2 / θ + Real.exp (-a₁ * θ / ν ^ 3)))

/-- **`eq:ct-kinetic-impulse`** (source lines 3242-3251; `sct:integrated`), for every BUC train
`tr`: for `0 < θ ≤ r ≤ b`,
`‖K_{d(θ)}𝒰_Z(θ,r)h‖₂ ≤ C_b (r/θ)‖K_{d(r)}h‖₂`. -/
def CTKineticImpulse : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ m : ℝ, 8 < m → ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b →
    ∃ (C ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ r θ : ℝ, 0 < θ → θ ≤ r → r ≤ b →
          ∀ h Zh : ℝ × ℝ → ℂ, MemLp h 2 (B0579.cellMeasure (dOfTheta ν r) m) →
            HasZeroCirculation (dOfTheta ν r) h → IsCentrallyEven h →
            HeatEvolvesTo ν m tr r θ h Zh →
              kinNorm (dOfTheta ν θ) Zh ≤ ENNReal.ofReal (C * (r / θ)) * kinNorm (dOfTheta ν r) h

/-- **`eq:ct-partial-moment`** (source lines 3252-3270; the train energy bounds
lines 3260-3264), for every BUC train `tr`: for `0 < θ ≤ r ≤ b`,
`|Q 𝒰_Z(θ,r)h| ≤ |Qh| + C_b r log(r/θ) ‖K_{d(r)}h‖₂`. -/
def CTPartialMoment : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ m : ℝ, 8 < m → ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b →
    ∃ (C ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ r θ : ℝ, 0 < θ → θ ≤ r → r ≤ b →
          ∀ h Zh : ℝ × ℝ → ℂ, MemLp h 2 (B0579.cellMeasure (dOfTheta ν r) m) →
            HasZeroCirculation (dOfTheta ν r) h → IsCentrallyEven h →
            HeatEvolvesTo ν m tr r θ h Zh →
              ENNReal.ofReal ‖quadQ (dOfTheta ν θ) Zh‖ ≤
                ENNReal.ofReal ‖quadQ (dOfTheta ν r) h‖ +
                  ENNReal.ofReal (C * r * Real.log (r / θ)) * kinNorm (dOfTheta ν r) h

/-- **`eq:ct-tested-impulse`** (source lines 3266-3274), for every BUC train `tr`: for `p > 0`,
`0 < r ≤ b`,
`∫_0^r θ^{p-1}|Q 𝒰_Z(θ,r)h| dθ ≤ C_{b,p} r^p(|Qh| + r‖K_{d(r)}h‖₂)`. -/
def CTTestedImpulse : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ m : ℝ, 8 < m → ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b →
    ∀ p : ℝ, 0 < p → ∃ (C ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ r : ℝ, 0 < r → r ≤ b →
          ∀ h : ℝ × ℝ → ℂ, MemLp h 2 (B0579.cellMeasure (dOfTheta ν r) m) →
            HasZeroCirculation (dOfTheta ν r) h → IsCentrallyEven h →
            ∀ Zh : ℝ → ℝ × ℝ → ℂ, (∀ θ ∈ Ioc 0 r, HeatEvolvesTo ν m tr r θ h (Zh θ)) →
              ∫⁻ θ in Ioo 0 r, ENNReal.ofReal (θ ^ (p - 1)) *
                  ENNReal.ofReal ‖quadQ (dOfTheta ν θ) (Zh θ)‖ ≤
                ENNReal.ofReal (C * r ^ p) *
                  (ENNReal.ofReal ‖quadQ (dOfTheta ν r) h‖ +
                    ENNReal.ofReal r * kinNorm (dOfTheta ν r) h)

/-- **`eq:ct-compact-comparison`** (source lines 3290-3298): for every fixed `0 < r ≤ b`,
`sup_{r≤θ≤b}(‖K_d(Z - V_d)(θ)‖₂ + |Q_d(Z - V_d)(θ)|) → 0` as `ν → 0`, uniformly over the BUC
trains `tr` and the actual columns `w` from the prepared datum. -/
def CTCompactComparison : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ m : ℝ, 8 < m → ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b →
    ∀ r : ℝ, 0 < r → r ≤ b → ∀ ε : ℝ, 0 < ε → ∀ᶠ ν in 𝓝[>] (0 : ℝ),
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr 0 (preparedDatum P ν) w u →
          ∀ θ ∈ Icc r b,
            kinNorm (dOfTheta ν θ) (heatColumn P ν w θ - canonicalPeriodized P ν θ) ≤
                ENNReal.ofReal ε ∧
              ENNReal.ofReal ‖quadQ (dOfTheta ν θ)
                (heatColumn P ν w θ - canonicalPeriodized P ν θ)‖ ≤ ENNReal.ofReal ε

/-! ## Mellin output and stress defects (SP 3262-3404) -/

/-- The complex Mellin coefficient `𝓙(μ) = ∫_0^∞ θ^{μ+1/2} 𝔐(V_can(θ)) dθ` (SP 3256; the
`Planar.PlanarData.mellinJ` of the library is the real-`μ` restriction). -/
def mellinJc (P : PlanarData) (μ : ℂ) : ℂ :=
  ∫ θ in Ioi (0 : ℝ), ((θ : ℂ) ^ (μ + 1 / 2)) * quadrupole (P.canonical θ)

/-- The onset age `u_o = ν^{-3/2}` (SP 3264). -/
def onsetAge (ν : ℝ) : ℝ := ν ^ (-3 / 2 : ℝ)

/-- `A_+(s) = -π s^{-μ} Q_c(w(s))/(4c)` (SP 3267). -/
def aPlus (ν : ℝ) (μ : ℂ) (w : ℝ → ℝ × ℝ → ℂ) (s : ℝ) : ℂ :=
  -((Real.pi : ℝ) : ℂ) * (s : ℂ) ^ (-μ) * quadQ (ν ^ (-2 : ℝ)) (w s) /
    (4 * ((ν ^ (-2 : ℝ) : ℝ) : ℂ))

/-- `I_A = ∫_{u_o}^∞ A_+(s) s^{-5/2} ds` (SP 3268). -/
def iA (ν : ℝ) (μ : ℂ) (w : ℝ → ℝ × ℝ → ℂ) : ℂ :=
  ∫ s in Ioi (onsetAge ν), aPlus ν μ w s * ((s ^ (-5 / 2 : ℝ) : ℝ) : ℂ)

/-- The scale `𝒜_ν = |N| ν^{3+2σ}/c`, `σ = Re μ` (SP 3329). -/
def scaleA (P : PlanarData) (ν : ℝ) (μ : ℂ) : ℝ :=
  ‖P.gaugeFactor ν‖ * ν ^ (3 + 2 * μ.re) / ν ^ (-2 : ℝ)

/-- `E_η = (2/c)∫ v₁ u_{μ,1}` (SP 3316; components `1, 2` are `q, η`, i.e. indices `0, 1`),
`u_μ = s^{-μ}u`. -/
def pairEta {ν : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (μ : ℂ)
    (u : ℝ × ℝ → Fin 2 → ℂ) (s : ℝ) : ℂ :=
  (2 / ((ν ^ (-2 : ℝ) : ℝ) : ℂ)) *
    ∫ x in B0579.cell (ν ^ (-2 : ℝ)), ((tr.v s x 0 : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x 0)

/-- `E_q = (2/c)∫ v₂ u_{μ,2}`. -/
def pairQ {ν : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (μ : ℂ)
    (u : ℝ × ℝ → Fin 2 → ℂ) (s : ℝ) : ℂ :=
  (2 / ((ν ^ (-2 : ℝ) : ℝ) : ℂ)) *
    ∫ x in B0579.cell (ν ^ (-2 : ℝ)), ((tr.v s x 1 : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x 1)

/-- `C = (1/c)∫(v₁u_{μ,2} + v₂u_{μ,1})`. -/
def pairC {ν : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (μ : ℂ)
    (u : ℝ × ℝ → Fin 2 → ℂ) (s : ℝ) : ℂ :=
  (1 / ((ν ^ (-2 : ℝ) : ℝ) : ℂ)) *
    ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
      (((tr.v s x 0 : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x 1) +
        ((tr.v s x 1 : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x 0))

/-- The absolute stress `S_abs(s) = c⁻¹∫|v ⊗ u_μ + u_μ ⊗ v| dq dη` (SP 3333-3335), Frobenius
norm of the `2×2` tensor. -/
def sAbs {ν : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (μ : ℂ)
    (u : ℝ × ℝ → Fin 2 → ℂ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in B0579.cell (ν ^ (-2 : ℝ)), ENNReal.ofReal (ν ^ (-2 : ℝ))⁻¹ *
    ENNReal.ofReal (Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2,
      ‖((tr.v s x i : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x j) +
          ((s : ℂ) ^ (-μ) * u x i) * ((tr.v s x j : ℝ) : ℂ)‖ ^ 2))

/-- **`eq:ct-mellin`** (source lines 3314-3343): for `K ⋐ {0 < Re μ < 1/4}`,
`I_A = -(πN/(4c)) ν^{3+2μ}[𝓙(μ) + o_K(1)]` for the actual column `w` (the integral converges),
uniformly on `K` and over the BUC trains `tr` and the actual columns `w` from the prepared datum. -/
def CTMellin : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ m : ℝ, 8 < m → ∀ K : Set ℂ, IsAdmissibleK K →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ ν in 𝓝[>] (0 : ℝ),
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr 0 (preparedDatum P ν) w u →
          ∀ μ ∈ K,
            IntegrableOn (fun s => aPlus ν μ w s * ((s ^ (-5 / 2 : ℝ) : ℝ) : ℂ))
                (Ioi (onsetAge ν)) ∧
              ‖iA ν μ w /
                  (-((Real.pi : ℝ) : ℂ) * P.gaugeFactor ν / (4 * ((ν ^ (-2 : ℝ) : ℝ) : ℂ)) *
                    (ν : ℂ) ^ (3 + 2 * μ)) - mellinJc P μ‖ ≤ ε

/-- **`eq:ct-absolute-stress`** (source lines 3345-3379; the train energy bounds lines 3374-3376):
for `k = 0, 1`, `∫_{u_o}^∞ s^{-3/2-k/2} S_abs(s) ds ≤ C_{K,k} 𝒜_ν ν^k`, uniformly on `K`, for
small `ν`, every BUC train `tr` and every actual column `w` (velocity `u`) from the prepared
datum. -/
def CTAbsoluteStress : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ m : ℝ, 8 < m → ∀ K : Set ℂ, IsAdmissibleK K →
    ∀ k : ℕ, k ≤ 1 → ∃ (C ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr 0 (preparedDatum P ν) w u →
          ∀ μ ∈ K,
            ∫⁻ s in Ioi (onsetAge ν), ENNReal.ofReal (s ^ (-3 / 2 - (k : ℝ) / 2)) *
                sAbs tr μ (u s) s ≤
              ENNReal.ofReal (C * scaleA P ν μ * ν ^ k)

/-- **`eq:ct-stress-defect`** (source lines 3380-3391): with `D_c = E_η + E_q`, `R_c = E_q - iC`,
`∫_{u_o}^∞ (D_c - 3R_c) s^{-3/2} ds = o_K(𝒜_ν)` uniformly on `K` and over the BUC trains `tr` and
the actual columns `w` (velocity `u`) from the prepared datum. -/
def CTStressDefect : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ m : ℝ, 8 < m → ∀ K : Set ℂ, IsAdmissibleK K →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ ν in 𝓝[>] (0 : ℝ),
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr 0 (preparedDatum P ν) w u →
          ∀ μ ∈ K,
            IntegrableOn (fun s => ((pairEta tr μ (u s) s + pairQ tr μ (u s) s) -
                3 * (pairQ tr μ (u s) s - Complex.I * pairC tr μ (u s) s)) *
                  ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) (Ioi (onsetAge ν)) ∧
              ‖∫ s in Ioi (onsetAge ν), ((pairEta tr μ (u s) s + pairQ tr μ (u s) s) -
                3 * (pairQ tr μ (u s) s - Complex.I * pairC tr μ (u s) s)) *
                  ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)‖ ≤ ε * scaleA P ν μ

/-- **`eq:ct-anisotropy`** (source lines 3392-3401):
`∫_{u_o}^∞ (2E_q - E_η) s^{-3/2} ds = 3i(μ + 3/2) I_A + o_K(𝒜_ν)` uniformly on `K` and over the
BUC trains `tr` and the actual columns `w` (velocity `u`) from the prepared datum. -/
def CTAnisotropy : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ m : ℝ, 8 < m → ∀ K : Set ℂ, IsAdmissibleK K →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ ν in 𝓝[>] (0 : ℝ),
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr 0 (preparedDatum P ν) w u →
          ∀ μ ∈ K,
            IntegrableOn (fun s => (2 * pairQ tr μ (u s) s - pairEta tr μ (u s) s) *
                ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) (Ioi (onsetAge ν)) ∧
              ‖(∫ s in Ioi (onsetAge ν), (2 * pairQ tr μ (u s) s -
                  pairEta tr μ (u s) s) * ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) -
                3 * Complex.I * (μ + 3 / 2) * iA ν μ w‖ ≤ ε * scaleA P ν μ

end UnforcedLeray.Short.IIIa
