import UnforcedLeray.Short.PartIIb.Sub.G4
import UnforcedLeray.Short.PartIIb.StatementsMixed
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.PairCont
import UnforcedLeray.Short.PartIIb.Tasks.BodyLift.Norm

/-!
# Part II-b, `PartII-b:G4/3/org`: the unprojected affine column `𝒞_ε` (definitions, decomposition)

Source of record: `the November 2 reference manuscript` (SP), lines 2347-2383
(`Exact geometry and the nonlinear correction`, display `short-bg:affine` at 2378-2384), with the
chart conventions of SP 1651-1660, 1919-1921 and the raw lift of SP 1206-1216, 1292, 2042-2046, 2419.

## The column

For one inlet stream `ψ = ψ_i` (the frozen stream of `p.mode`, cut off by `χ(s)`), SP 2360-2366
writes the normalized lift `e_ε = e_0 + εe_1`, `e_0 = χ(-ψ_η, ψ_q)`,
`e_1 = (0, (χ - 2sχ')ψ - χηψ_η)`; this is `p.inletProfile i = Axi.ringStreamProfile p.R
(p.cutStream i)`, and `inletE0 p i` (`StatementsMixed.lean`) is `e_0`. With `K = 2s∂_s + η∂_η`
the exact vector diffusion is (SP 2367-2369)
`L_ε = Δ - 2ε(K+1)∂_q + ε²[(K+1)² - diag(1,0)]`, `Δ = ∂_q² + ∂_η²` (`vecDiffEps`), and the complete
unprojected source column is (SP 2370-2374)
`𝒞_εα = s[(∂_s - νL_ε)e_ε + B_εe_ε]α`.
Here `B_ε` is the raw-background interaction in the chart: with `b_raw = (v₁, v₂ + εH)` the profile
of `U_raw = N_v b_raw` (`Params.raw`, `C03.rawProfile`; SP 1206-1216, 1292, 2042-2046, 2419) and
`∇_ε = (Q_ε, ∂_η)`, `Q_ε = ∂_q - ε(K+1)` (SP 1651-1653; `∂_ρ(√s f) = sQ_εf`, `∂_z(√s f) = s∂_ηf`,
SP 1919-1921), `B_εF = (b_raw·∇_ε)F + (F·∇_ε)b_raw` (`bEps`), so that
`B_{U_raw}(N_vF) = N_v(sB_εF)` off the axis (no hoop term: the fields have no swirl).
`T₀(√s F) = √s(S + 1/2)F` and `νΔ(N_vF) = N_v(νsL_εF)` give `L₀(N_vF) = N_v(s(∂_s - νL_ε)F)`.
`colEps p i` is the complex profile of `𝒞_εe_i` (`colEpsR`, real; zero for `s ≤ 0`, where
profiles do not matter); `flatColumn p i` (`StatementsMixed.lean`) is its `ε = 0` analogue.
These are the actual objects of `IsCop`: `IsCop p C` says that `N_v(toProf (Cα))` is the
distribution `(L₀ + B_{U_raw})(E_εα)` tested on phase tests.

## Decomposition of `AffineColumnComparison`

* `ColumnIdentification` (`IsCop p C ↔ toProf (Cα) = Σα_i 𝒞_εe_i` a.e.) from
  - `ColumnPairing` (change of variables `(τ, y) ↔ (s, q, η)` and integration by parts), itself
    from `InletIBP` (integration by parts against the smooth inlet), `InletL0Ptw` (from the drift
    part `InletT0Ptw` and the Laplacian part `InletLapPtw`) and `InletBPtw` (the pointwise chart
    identities for `L₀` and `B_{U_raw}` of the ring lift);
  - `ProfileUnique` (density of the phase tests in the dual of `H_p`, through the chart);
  - `ColumnMem` (`𝒞_εe_i ∈ H_p`).
* `ColumnMem` (SP 2385: "The integrability exponent is `-9/8 + p = 13/8 > -1`").
* `ColumnDifference` (`‖𝒞_εe_i - 𝒞_0e_i‖_{H_p} ≤ Cν^{-k}ε`, from `𝒞_ε - 𝒞_0 = εsr_ε`, SP 2375-2379).
* `RawJetBound`: the polynomial jet bounds of `b_raw` on `0 < s ≤ Σ/ν` used by the last two
  (Part I: `sct:train`, `sct:transverse`, `sct:fixed-band`, SP 261-291, 463-478; SP 2419-2423), to be proved from
  `PartI.TrainTransverseTails` and `PartI.TrainFixedBand`.

Proved here (no sorry): `inletL0Ptw_of`, `columnPairing_of`, `columnIdentification_of`,
`affineColumnComparison_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

/-! ## The chart operators (SP 1651-1653, 2360-2369) -/

/-- `K = 2s∂_s + η∂_η` on a chart function (SP 2360). -/
def kAge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Coord → E) (x : Coord) : E :=
  (2 * x.1) • Axi.dS F x + x.2.2 • Axi.dEta F x

/-- `Q_ε = ∂_q - ε(K+1)` on a meridional profile (SP 1651-1653, 2420). -/
def qEps (ε : ℝ) (F : Coord → Axi.Merid) (x : Coord) : Axi.Merid :=
  Axi.dQ F x - ε • (kAge F x + F x)

/-- `diag(1,0)` on the meridional pair `(b_r, b_z)` (SP 2369; the hoop term `-b_r/ρ²` acts on the
radial component only). -/
def hoopR (v : Axi.Merid) : Axi.Merid := v 0 • Axi.m0

/-- **The exact vector diffusion** (SP 2367-2369):
`L_εF = ΔF - 2ε(K+1)∂_qF + ε²[(K+1)²F - diag(1,0)F]`, `Δ = ∂_q² + ∂_η²`
(`(K+1)²F = K((K+1)F) + (K+1)F`). For `C²` profiles it equals `Q_ε²F + ∂_η²F - ε²diag(1,0)F`,
the `lapProf` form of `Sub/T09.lean` (SP 1651-1653). -/
def vecDiffEps (ε : ℝ) (F : Coord → Axi.Merid) (x : Coord) : Axi.Merid :=
  Axi.dQ (Axi.dQ F) x + Axi.dEta (Axi.dEta F) x -
    (2 * ε) • (kAge (Axi.dQ F) x + Axi.dQ F x) +
    ε ^ 2 • (kAge (fun y => kAge F y + F y) x + (kAge F x + F x) - hoopR (F x))

/-- The chart profile `b_raw = (v₁, v₂ + εH)`, `H = (1 - K)ψ`, of the raw background
`U_raw = N_v b_raw` (SP 1206-1216, 1292, 2042-2046, 2419; `Params.raw_eq_off_axis`). -/
def rawProf (p : Params) : Coord → Axi.Merid :=
  UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ

/-- **The raw interaction in the chart** (SP 2007-2012, 2370-2374):
`B_εF = (b_raw·∇_ε)F + (F·∇_ε)b_raw`, `∇_ε = (Q_ε, ∂_η)`, so that
`U_raw·∇(N_vF) + (N_vF)·∇U_raw = N_v(sB_εF)` off the axis. -/
def bEps (p : Params) (F : Coord → Axi.Merid) (x : Coord) : Axi.Merid :=
  rawProf p x 0 • qEps p.ε F x + rawProf p x 1 • Axi.dEta F x +
    (F x 0 • qEps p.ε (rawProf p) x + F x 1 • Axi.dEta (rawProf p) x)

/-- The drift-diffusion part `s(∂_s - νL_ε)e_ε` of the column of inlet `i` (SP 2370-2374). -/
def colDiffR (p : Params) (i : Fin 2) (x : Coord) : Axi.Merid :=
  x.1 • (Axi.dS (p.inletProfile i) x - p.ν • vecDiffEps p.ε (p.inletProfile i) x)

/-- The interaction part `sB_εe_ε` of the column of inlet `i` (SP 2370-2374). -/
def colIntR (p : Params) (i : Fin 2) (x : Coord) : Axi.Merid :=
  x.1 • bEps p (p.inletProfile i) x

/-- **The complete unprojected affine column** of inlet `i`, real form (SP 2370-2374):
`𝒞_εe_i = s[(∂_s - νL_ε)e_ε + B_εe_ε]` on `s > 0`, zero on `s ≤ 0`. -/
def colEpsR (p : Params) (i : Fin 2) (x : Coord) : Axi.Merid :=
  if 0 < x.1 then colDiffR p i x + colIntR p i x else 0

/-- **`colEps p i`**: the complex profile of the unprojected column `𝒞_εe_i` (SP 2370-2374);
`flatColumn p i` is its `ε = 0` analogue. -/
def colEps (p : Params) (i : Fin 2) : CProf := cplx (colEpsR p i)

/-- The affine inlet `E_εα = Σ α_iE_i` as a complex field (the field tested in `IsCop`). -/
def inletC (p : Params) (α : E2) (x : ℝ × Space) : CVec3 :=
  ∑ i : Fin 2, ((α i : ℝ) : ℂ) • p.Efun i x

/-- `𝒞_εα = Σ α_i 𝒞_εe_i` (complex profile). -/
def colEpsSum (p : Params) (α : E2) (x : Coord) : CMerid :=
  ∑ i : Fin 2, ((α i : ℝ) : ℂ) • colEps p i x

/-- The train velocity `v(s, q, η)` as a chart profile. -/
def trainProf (p : Params) : Coord → Axi.Merid := fun x => p.train.v x.1 x.2

/-- The raised stream `H = (1 - K)ψ = ψ - η∂_ηψ - 2s∂_sψ` as a chart function
(`C03.raisedStream`, SP 1206-1216, 2419). -/
def raisedProf (p : Params) : Coord → ℝ := fun x =>
  UnforcedLeray.Cons.C03.raisedStream p.train.ψ x.1 x.2.1 x.2.2

/-! ## The leaf statements -/

/-- **Integration by parts against the inlet** (SP 2370-2382, the identity behind `IsCop`): the
affine inlet `E_εα` is smooth on `ℝ × ℝ³` (it vanishes near the axis, where `s ≥ H/2` and the age
cutoff vanishes), `P`-periodic in the phase, and `U_raw` is solenoidal there; hence for every
phase test `Φ`,
`⟪L₀ᵗΦ + (∇U_raw)ᵀΦ - (U_raw·∇)Φ, E_εα⟫ = ⟪Φ, L₀E_εα + (U_raw·∇)E_εα + (E_εα·∇)U_raw⟫`
with the pointwise operators `B0411.L0`, `advT`. -/
def InletIBP : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ (α : E2) (Φ : ℝ × Space → CVec3), IsPhaseTest p.period Φ →
        pairF p.period (fun x => L0T p.ν Φ x + convT p.raw Φ x) (inletC p α) =
          pairF p.period Φ (fun x => B0411.L0 p.ν (inletC p α) x + advT p.Ufun (inletC p α) x +
            advT (inletC p α) p.Ufun x)

/-- **The drift-diffusion part in the chart** (SP 1919-1921, 2367-2374): off the axis,
`L₀(N_v e_ε) = N_v(s(∂_s - νL_ε)e_ε)` (`T₀(√s F) = √s(S + 1/2)F`, `νΔ(N_vF) = N_v(νsL_εF)`),
for the affine inlet `E_εα = N_v(Σα_i e_ε^{(i)})`. -/
def InletL0Ptw : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ (α : E2) (τ : ℝ) (y : Space), y ∉ Axi.axis →
        B0411.L0 p.ν (inletC p α) (τ, y) =
          NvC p.R (fun m => ∑ i : Fin 2, ((α i : ℝ) : ℂ) • cplx (colDiffR p i) m) (τ, y)

/-- **The drift in the chart** (SP 1919; `T₀ = ∂_τ - ½y·∇`): off the axis,
`T₀(N_ve) - ½N_ve = N_v(s∂_se)` for the inlet profiles (`∂_τ q = R/2`, `y·∇s = -2s`, `y·∇q = R`,
`η` and the frame are dilation invariant, `√s` gives the `1/2`; cf. `NvCDriftOffAxis`, T08). -/
def InletT0Ptw : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ (α : E2) (τ : ℝ) (y : Space), y ∉ Axi.axis →
        T0 (inletC p α) (τ, y) - (1 / 2 : ℝ) • inletC p α (τ, y) =
          NvC p.R (fun m => ∑ i : Fin 2, ((α i : ℝ) : ℂ) •
            cplx (fun x => x.1 • Axi.dS (p.inletProfile i) x) m) (τ, y)

/-- **The vector Laplacian in the chart** (SP 1651-1658, 1919-1921, 2367-2369): off the axis,
`νΔ(N_ve) = N_v(νsL_εe)` for the inlet profiles (`Δ(fe_r) = (Δf - f/ρ²)e_r`, `Δ(ge_z) = (Δg)e_z`,
`Δ(√sF) = √s s(Q_ε² + ∂_η²)F`, and `Q_ε² + ∂_η² - ε²diag(1,0) = L_ε` on `C²` profiles;
cf. `LapPtwise`, T09/5). -/
def InletLapPtw : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ (α : E2) (τ : ℝ) (y : Space), y ∉ Axi.axis →
        nuLapT p.ν (inletC p α) (τ, y) =
          NvC p.R (fun m => ∑ i : Fin 2, ((α i : ℝ) : ℂ) •
            cplx (fun x => x.1 • (p.ν • vecDiffEps p.ε (p.inletProfile i) x)) m) (τ, y)

/-- **The interaction part in the chart** (SP 1919-1921, 2007-2012, 2370-2374): off the axis,
`(U_raw·∇)E_εα + (E_εα·∇)U_raw = N_v(sB_ε(Σα_i e_ε^{(i)}))` (`U_raw = N_v b_raw` near every
off-axis point; `∂_ρ(√s f) = sQ_εf`, `∂_z(√s f) = s∂_ηf`; no hoop term without swirl). -/
def InletBPtw : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ (α : E2) (τ : ℝ) (y : Space), y ∉ Axi.axis →
        advT p.Ufun (inletC p α) (τ, y) + advT (inletC p α) p.Ufun (τ, y) =
          NvC p.R (fun m => ∑ i : Fin 2, ((α i : ℝ) : ℂ) • cplx (colIntR p i) m) (τ, y)

/-- **The change of variables** (SP 2370-2382): the distribution `(L₀ + B_{U_raw})(E_εα)` is the
ring lift of the column `𝒞_εα`, tested on every phase test. -/
def ColumnPairing : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ (α : E2) (Φ : ℝ × Space → CVec3), IsPhaseTest p.period Φ →
        pairF p.period (fun x => L0T p.ν Φ x + convT p.raw Φ x) (inletC p α) =
          pairF p.period Φ (NvC p.R (colEpsSum p α))

/-- **Density of the phase tests / uniqueness of the profile** (SP 1902-1906, 2370-2382): two
profiles of `H_p` whose ring lifts have the same pairing with every phase test agree a.e. (the
chart `(τ, y) ↦ (s, q, η)` is a local diffeomorphism off the axis; window tests as in
`Sub/PartII-b_T09_4.lean`; `c`-periodicity in `q`). -/
def ProfileUnique : Prop :=
  ∀ (c ε : ℝ), 0 < c → 0 < ε → ∀ b b' : CProf, InHr c bgp b → InHr c bgp b' →
    (∀ Φ : ℝ × Space → CVec3, IsPhaseTest (2 * ε * c) Φ →
      pairF (2 * ε * c) Φ (NvC ε⁻¹ b) = pairF (2 * ε * c) Φ (NvC ε⁻¹ b')) →
    b =ᵐ[hMeas c bgp] b'

/-- **`𝒞_εe_i ∈ H_p`** (SP 2347-2348, 2370-2385): the column is `c`-periodic, measurable and of finite
`H_p` norm ("The integrability exponent is `-9/8 + p = 13/8 > -1`": the column carries the factor
`s` and vanishes for `s ≥ H/2 = Σ/(2ν)`, the frozen stream bounds `FrozenStreamBounds` give
exponential transverse decay with polynomial `c` costs). Equivalently, `colEps p i` is the profile
of an element of `HpR p.c` (`memLp_colEpsR`). -/
def ColumnMem : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ i : Fin 2, InHr p.c bgp (colEps p i)

/-- **Identification of the unprojected column** (SP 2370-2382): a bounded `C : ℝ² → H_p`
represents the complete source `(A₀ + B_{U_raw})(E_εα)` (`IsCop`) iff `C α` has the profile
`Σα_i 𝒞_εe_i`. -/
def ColumnIdentification : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ C : E2 →L[ℝ] HpR p.c, IsCop p C ↔
        ∀ α : E2, toProf p.c (C α) =ᵐ[hMeas p.c bgp] colEpsSum p α

/-- **Polynomial jet bounds of the raw profile** on the slow band `0 < s ≤ H = Σ/ν` (SP 2419-2423;
Part I `sct:train` (BUC class, SP 261-291), `sct:transverse`, `sct:fixed-band` (SP 463-478), with the polynomial convention
of SP 255-258): the train velocity `v`, the raised stream `H = (1 - K)ψ` and their first chart
derivatives `∂_q, ∂_η, K` are bounded by `Cν^{-k}(1 + |η|)^N`. These bound `b_raw = v + εHe_z`,
`Q_εb_raw` and `∂_ηb_raw`. -/
def RawJetBound : Prop :=
  ∀ Sig : ℝ, 0 < Sig → ∀ dm dp : ℝ, 0 < dm → ∃ (C : ℝ) (k N : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig →
      ∀ x : Coord, 0 < x.1 → x.1 ≤ p.H →
        ‖trainProf p x‖ + ‖Axi.dQ (trainProf p) x‖ + ‖Axi.dEta (trainProf p) x‖ +
            ‖kAge (trainProf p) x‖ +
          (|raisedProf p x| + |Axi.dQ (raisedProf p) x| + |Axi.dEta (raisedProf p) x| +
            |kAge (raisedProf p) x|) ≤
          C * (p.ν ^ k)⁻¹ * (1 + |x.2.2|) ^ N

/-- **`‖𝒞_ε - 𝒞_0‖_{ℝ²→H_p} ≤ ε𝒫_ν`, column by column** (SP 2375-2379): `𝒞_ε - 𝒞_0 = εsr_ε` with
`r_ε` smooth at zero, compact in upper age (`s ≤ Σ/(2ν)`) and polynomially bounded, so
`‖colEps p i - flatColumn p i‖_{H_p} ≤ Cν^{-k}ε`. -/
def ColumnDifference : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ i : Fin 2, hNorm p.c bgp (fun x => colEps p i x - flatColumn p i x) ≤
        ENNReal.ofReal (C * (p.ν ^ k)⁻¹ * p.ε)

/-! ## Algebraic helpers -/

theorem NvC_add_apply (R : ℝ) (f g : CProf) (x : ℝ × Space) :
    NvC R (fun m => f m + g m) x = NvC R f x + NvC R g x := by
  have h1 : (fun w => reM (f w + g w)) = (fun w => reM (f w)) + (fun w => reM (g w)) := by
    funext w; ext i; simp [reM]
  have h2 : (fun w => imM (f w + g w)) = (fun w => imM (f w)) + (fun w => imM (g w)) := by
    funext w; ext i; simp [imM]
  have hr : ∀ a b : Space, B0412.realC (a + b) = B0412.realC a + B0412.realC b := by
    intro a b; ext i; simp [B0412.realC_apply]
  simp only [NvC, h1, h2, Axi.Nv_add, hr, smul_add]
  abel

/-- `N_v b` at `(τ, y)` only sees `b` at the chart point. -/
theorem NvC_apply_congr (R : ℝ) (b b' : CProf) (τ : ℝ) (y : Space)
    (h : b (Axi.chart R τ y) = b' (Axi.chart R τ y)) : NvC R b (τ, y) = NvC R b' (τ, y) := by
  simp only [NvC, Axi.Nv, h]

theorem colEps_of_pos (p : Params) (i : Fin 2) {x : Coord} (hx : 0 < x.1) :
    colEps p i x = cplx (colDiffR p i) x + cplx (colIntR p i) x := by
  ext j
  simp [colEps, cplx, colEpsR, hx]

theorem liftM_lin (a b : ℝ) (v w : Axi.Merid) :
    liftM (a • v + b • w) = ((a : ℝ) : ℂ) • liftM v + ((b : ℝ) : ℂ) • liftM w := by
  ext j
  simp [liftM]

theorem liftM_sub' (v w : Axi.Merid) : liftM (v - w) = liftM v - liftM w := by
  ext j
  simp [liftM]

/-- A phase pairing only sees its field off the axis. -/
theorem pairF_congr_offAxis {P : ℝ} (Φ u v : ℝ × Space → CVec3)
    (h : ∀ (τ : ℝ) (y : Space), y ∉ Axi.axis → u (τ, y) = v (τ, y)) :
    pairF P Φ u = pairF P Φ v := by
  unfold pairF phaseInt
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  refine integral_congr_ae ?_
  filter_upwards [Axi.ae_not_mem_axis] with y hy
  simp only [h t y hy]

theorem inHr_add_of {c r : ℝ} (hr : 1 ≤ r) {f g : CProf} (hf : InHr c r f) (hg : InHr c r g) :
    InHr c r (fun x => f x + g x) := by
  refine ⟨?_, hf.meas.add hg.meas, ?_⟩
  · filter_upwards [hf.periodic, hg.periodic] with x h1 h2
    simp only [h1, h2]
  · have hr1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr
    exact lt_of_le_of_lt (eLpNorm_add_le hf.meas hg.meas hr1)
      (ENNReal.add_lt_top.2 ⟨hf.finite, hg.finite⟩)

theorem inHr_const_smul_of {c r : ℝ} (a : ℂ) {f : CProf} (hf : InHr c r f) :
    InHr c r (fun x => a • f x) := by
  refine ⟨?_, hf.meas.const_smul a, ?_⟩
  · filter_upwards [hf.periodic] with x h1
    simp only [h1]
  · have h := eLpNorm_const_smul_le (c := a) (f := f) (p := ENNReal.ofReal r) (μ := hMeas c r)
    exact lt_of_le_of_lt h (ENNReal.mul_lt_top enorm_lt_top hf.finite)

theorem inHr_toProf {c : ℝ} (hc : 0 < c) (g : HpR c) : InHr c bgp (toProf c g) :=
  ⟨toProf_periodic hc g, toProf_aestronglyMeasurable hc g, by
    rw [hNorm_toProf hc g]; exact enorm_lt_top⟩

theorem inHr_colEpsSum {p : Params} (h0 : InHr p.c bgp (colEps p 0))
    (h1 : InHr p.c bgp (colEps p 1)) (α : E2) : InHr p.c bgp (colEpsSum p α) := by
  have hr : (1 : ℝ) ≤ bgp := by norm_num [bgp]
  have e : colEpsSum p α =
      fun x => ((α 0 : ℝ) : ℂ) • colEps p 0 x + ((α 1 : ℝ) : ℂ) • colEps p 1 x := by
    funext x; simp [colEpsSum, Fin.sum_univ_two]
  rw [e]
  exact inHr_add_of hr (inHr_const_smul_of _ h0) (inHr_const_smul_of _ h1)

/-- Two a.e.-equal profiles of `H_p` have the same phase pairings (`DriftPairCont`, `T08/3`, with a
constant sequence). -/
theorem pairF_NvC_congr_ae {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) {b b' : CProf}
    (hb : InHr c bgp b) (hb' : InHr c bgp b') (h : b =ᵐ[hMeas c bgp] b')
    (Φ : ℝ × Space → CVec3) (hΦ : IsPhaseTest (2 * ε * c) Φ) :
    pairF (2 * ε * c) Φ (NvC ε⁻¹ b) = pairF (2 * ε * c) Φ (NvC ε⁻¹ b') := by
  have hr : (1 : ℝ) < bgp := by norm_num [bgp]
  have h0 : hNorm c bgp (fun x => b x - b' x) = 0 := by
    unfold hNorm
    rw [eLpNorm_congr_ae (g := (0 : CProf)) (by filter_upwards [h] with x hx; simp [hx])]
    exact eLpNorm_zero
  have hlim := driftPairCont_proof c bgp ε Φ hc hε hr hΦ b' (fun _ => b) hb' (fun _ => hb)
    (by simp only [h0]; exact tendsto_const_nhds)
  exact tendsto_nhds_unique tendsto_const_nhds hlim

/-- The real column is the real part of the complex one, and has the same `H_p` norm; so a column
in `H_p` is the profile of an element of `HpR`. -/
theorem memLp_colEpsR {p : Params} {i : Fin 2} (h : InHr p.c bgp (colEps p i)) :
    MemLp (colEpsR p i) (ENNReal.ofReal bgp) (hMeas p.c bgp) := by
  have hre : colEpsR p i = fun x => reM (colEps p i x) := by
    funext x; ext j; simp [colEps, cplx, reM]
  refine ⟨?_, ?_⟩
  · rw [hre]; exact continuous_reM.comp_aestronglyMeasurable h.meas
  · have e : eLpNorm (colEpsR p i) (ENNReal.ofReal bgp) (hMeas p.c bgp) =
        hNorm p.c bgp (colEps p i) := by
      unfold hNorm
      exact eLpNorm_congr_norm_ae (Eventually.of_forall fun x => (liftM_norm _).symm)
    rw [e]; exact h.finite

/-- The operator `α ↦ α₀g₀ + α₁g₁`. -/
def colOp {c : ℝ} (g : Fin 2 → HpR c) : E2 →L[ℝ] HpR c :=
  (EuclideanSpace.proj (0 : Fin 2) : E2 →L[ℝ] ℝ).smulRight (g 0) +
    (EuclideanSpace.proj (1 : Fin 2) : E2 →L[ℝ] ℝ).smulRight (g 1)

theorem colOp_apply {c : ℝ} (g : Fin 2 → HpR c) (α : E2) :
    colOp g α = α 0 • g 0 + α 1 • g 1 := by
  simp [colOp]

theorem sum_single_smul {M : Type*} [AddCommMonoid M] [Module ℂ M] (i : Fin 2) (f : Fin 2 → M) :
    ∑ j : Fin 2, ((((EuclideanSpace.single i (1 : ℝ) : E2) j : ℝ) : ℂ)) • f j = f i := by
  fin_cases i <;> simp [Fin.sum_univ_two]

theorem NvC_sub_apply (R : ℝ) (f g : CProf) (x : ℝ × Space) :
    NvC R (fun m => f m - g m) x = NvC R f x - NvC R g x :=
  congrFun (NvC_sub R f g) x

/-! ## The decomposition -/

/-- **`InletL0Ptw`** from the drift and the Laplacian parts: `L₀ = (T₀ - ½) - νΔ`. -/
theorem inletL0Ptw_of (hT : InletT0Ptw) (hL : InletLapPtw) : InletL0Ptw := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₁, hν₁, HT⟩ := hT Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₂, hν₂, HL⟩ := hL Sig lam q hSig hq dm dp hdm
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, ?_⟩
  intro p d hreg hν hS hm α τ y hy
  have e1 := HT p d hreg (hν.trans (min_le_left _ _)) hS hm α τ y hy
  have e2 := HL p d hreg (hν.trans (min_le_right _ _)) hS hm α τ y hy
  have hL0 : B0411.L0 p.ν (inletC p α) (τ, y) =
      (T0 (inletC p α) (τ, y) - (1 / 2 : ℝ) • inletC p α (τ, y)) -
        nuLapT p.ν (inletC p α) (τ, y) := by
    simp only [B0411.L0, nuLapT, Pi.smul_apply]
    abel
  rw [hL0, e1, e2, ← NvC_sub_apply]
  refine NvC_apply_congr _ _ _ τ y ?_
  ext j
  simp [Fin.sum_univ_two, cplx, colDiffR, smul_sub]
  ring

/-- **`ColumnPairing`** from the integration by parts and the two pointwise chart identities. -/
theorem columnPairing_of (h1 : InletIBP) (h2 : InletL0Ptw) (h3 : InletBPtw) : ColumnPairing := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₁, hν₁, H1⟩ := h1 Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₂, hν₂, H2⟩ := h2 Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₃, hν₃, H3⟩ := h3 Sig lam q hSig hq dm dp hdm
  refine ⟨min ν₁ (min ν₂ ν₃), lt_min hν₁ (lt_min hν₂ hν₃), ?_⟩
  intro p d hreg hν hS hm α Φ hΦ
  have hν1 : p.ν ≤ ν₁ := hν.trans (min_le_left _ _)
  have hν2 : p.ν ≤ ν₂ := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν3 : p.ν ≤ ν₃ := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  rw [H1 p d hreg hν1 hS hm α Φ hΦ]
  refine pairF_congr_offAxis Φ _ _ fun τ y hy => ?_
  have hR : 0 < p.R := p.R_pos
  have hpos : 0 < (Axi.chart p.R τ y).1 := Axi.age_pos hR.ne' hy
  show B0411.L0 p.ν (inletC p α) (τ, y) + advT p.Ufun (inletC p α) (τ, y) +
      advT (inletC p α) p.Ufun (τ, y) = NvC p.R (colEpsSum p α) (τ, y)
  rw [add_assoc, H2 p d hreg hν2 hS hm α τ y hy, H3 p d hreg hν3 hS hm α τ y hy,
    ← NvC_add_apply]
  refine NvC_apply_congr _ _ _ τ y ?_
  have hce : ∀ i : Fin 2, colEps p i (Axi.chart p.R τ y) =
      cplx (colDiffR p i) (Axi.chart p.R τ y) + cplx (colIntR p i) (Axi.chart p.R τ y) :=
    fun i => colEps_of_pos p i hpos
  simp only [colEpsSum, hce, smul_add, Finset.sum_add_distrib]

/-- **`ColumnIdentification`** from the change of variables, the uniqueness of profiles and
`ColumnMem`. -/
theorem columnIdentification_of (hP : ColumnPairing) (hU : ProfileUnique) (hM : ColumnMem) :
    ColumnIdentification := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₁, hν₁, HP⟩ := hP Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₂, hν₂, HM⟩ := hM Sig lam q hSig hq dm dp hdm
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, ?_⟩
  intro p d hreg hν hS hm C
  have hP' := HP p d hreg (hν.trans (min_le_left _ _)) hS hm
  have hM' := HM p d hreg (hν.trans (min_le_right _ _)) hS hm
  have hc : 0 < p.c := p.c_pos
  have hε : 0 < p.ε := p.ε_pos
  have hsum : ∀ α : E2, InHr p.c bgp (colEpsSum p α) := inHr_colEpsSum (hM' 0) (hM' 1)
  constructor
  · intro hCop α
    refine hU p.c p.ε hc hε _ _ (inHr_toProf hc (C α)) (hsum α) fun Φ hΦ => ?_
    have e1 := hCop α Φ hΦ
    have e2 := hP' α Φ hΦ
    exact e1.symm.trans e2
  · intro hae α Φ hΦ
    have e2 := hP' α Φ hΦ
    exact e2.trans
      (pairF_NvC_congr_ae hc hε (hsum α) (inHr_toProf hc (C α)) (hae α).symm Φ hΦ)

/-- **`PartII-b:G4/3`, conditional form**: `AffineColumnComparison` from the identification of the
column, its membership in `H_p`, and the column difference bound. The constant is `2C` (two
columns). -/
theorem affineColumnComparison_of (hI : ColumnIdentification) (hM : ColumnMem)
    (hD : ColumnDifference) : AffineColumnComparison := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₁, hν₁, HI⟩ := hI Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₂, hν₂, HM⟩ := hM Sig lam q hSig hq dm dp hdm
  obtain ⟨C, k, ν₃, hC, hν₃, HD⟩ := hD Sig lam q hSig hq dm dp hdm
  refine ⟨2 * C, k, min ν₁ (min ν₂ ν₃), by positivity, lt_min hν₁ (lt_min hν₂ hν₃), ?_⟩
  intro p d hreg hν hS hm
  have hν1 : p.ν ≤ ν₁ := hν.trans (min_le_left _ _)
  have hν2 : p.ν ≤ ν₂ := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν3 : p.ν ≤ ν₃ := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hI' := HI p d hreg hν1 hS hm
  have hM' := HM p d hreg hν2 hS hm
  have hD' := HD p d hreg hν3 hS hm
  have hc : 0 < p.c := p.c_pos
  refine ⟨?_, ?_⟩
  · -- the two column elements of `H_p` and the operator they span
    let g : Fin 2 → HpR p.c := fun i => (memLp_colEpsR (hM' i)).toLp (colEpsR p i)
    have hg : ∀ i, toProf p.c (g i) =ᵐ[hMeas p.c bgp] colEps p i := by
      intro i
      filter_upwards [toProf_ae_eq hc (g i), MemLp.coeFn_toLp (memLp_colEpsR (hM' i))]
        with x h1 h2
      rw [h1, h2]
      rfl
    refine ⟨colOp g, (hI' (colOp g)).2 fun α => ?_⟩
    have h2 : ((colOp g α : HpR p.c) : Coord → Axi.Merid) =ᵐ[hMeas p.c bgp]
        fun x => α 0 • (g 0 : Coord → Axi.Merid) x + α 1 • (g 1 : Coord → Axi.Merid) x := by
      rw [colOp_apply]
      filter_upwards [Lp.coeFn_add (α 0 • g 0) (α 1 • g 1), Lp.coeFn_smul (α 0) (g 0),
        Lp.coeFn_smul (α 1) (g 1)] with x hx h0 h1
      rw [hx, Pi.add_apply, h0, h1]
      rfl
    filter_upwards [toProf_ae_eq hc (colOp g α), h2, hg 0, hg 1, toProf_ae_eq hc (g 0),
      toProf_ae_eq hc (g 1)] with x a b c0 c1 d0 d1
    rw [a, b, colEpsSum, Fin.sum_univ_two, ← c0, ← c1, d0, d1, liftM_lin]
  · intro Ce C0 hCe hC0
    have hid := (hI' Ce).1 hCe
    have hM0 : 0 ≤ C * (p.ν ^ k)⁻¹ * p.ε := by
      have := p.ν_pos; have := p.ε_pos; positivity
    have hbasis : ∀ i : Fin 2,
        ‖(Ce - C0) (EuclideanSpace.single i 1)‖ ≤ C * (p.ν ^ k)⁻¹ * p.ε := by
      intro i
      have hae : toProf p.c ((Ce - C0) (EuclideanSpace.single i 1)) =ᵐ[hMeas p.c bgp]
          fun x => colEps p i x - flatColumn p i x := by
        have hs : ((Ce - C0) (EuclideanSpace.single i 1) : HpR p.c) =
            Ce (EuclideanSpace.single i 1) - C0 (EuclideanSpace.single i 1) :=
          ContinuousLinearMap.sub_apply _ _ _
        filter_upwards [toProf_ae_eq hc ((Ce - C0) (EuclideanSpace.single i 1)),
          Lp.coeFn_sub (Ce (EuclideanSpace.single i 1)) (C0 (EuclideanSpace.single i 1)),
          toProf_ae_eq hc (Ce (EuclideanSpace.single i 1)),
          toProf_ae_eq hc (C0 (EuclideanSpace.single i 1)), hid (EuclideanSpace.single i 1),
          hC0 (EuclideanSpace.single i 1)] with x h1 h2 h3 h4 h5 h6
        rw [h1, hs, h2, Pi.sub_apply, liftM_sub', ← h3, ← h4, h5, h6, colEpsSum,
          sum_single_smul, sum_single_smul]
      have hn : ‖(Ce - C0) (EuclideanSpace.single i 1)‖ₑ =
          hNorm p.c bgp (fun x => colEps p i x - flatColumn p i x) := by
        rw [← hNorm_toProf hc]
        exact eLpNorm_congr_ae hae
      have hb := hD' i
      rw [← hn, ← ofReal_norm] at hb
      exact (ENNReal.ofReal_le_ofReal_iff hM0).1 hb
    refine ContinuousLinearMap.opNorm_le_bound _ (by have := p.ν_pos; have := p.ε_pos; positivity)
      fun α => ?_
    have hdec : α = α 0 • EuclideanSpace.single 0 1 + α 1 • EuclideanSpace.single 1 1 := by
      ext j; fin_cases j <;> simp
    have hsplit : (Ce - C0) α = α 0 • (Ce - C0) (EuclideanSpace.single 0 1) +
        α 1 • (Ce - C0) (EuclideanSpace.single 1 1) := by
      conv_lhs => rw [hdec]
      rw [map_add, map_smul, map_smul]
    rw [hsplit]
    have a0 : |α 0| ≤ ‖α‖ := by simpa using PiLp.norm_apply_le α 0
    have a1 : |α 1| ≤ ‖α‖ := by simpa using PiLp.norm_apply_le α 1
    have b0 := hbasis 0
    have b1 := hbasis 1
    calc ‖α 0 • (Ce - C0) (EuclideanSpace.single 0 1) +
          α 1 • (Ce - C0) (EuclideanSpace.single 1 1)‖
        ≤ ‖α 0 • (Ce - C0) (EuclideanSpace.single 0 1)‖ +
            ‖α 1 • (Ce - C0) (EuclideanSpace.single 1 1)‖ := norm_add_le _ _
      _ = |α 0| * ‖(Ce - C0) (EuclideanSpace.single 0 1)‖ +
            |α 1| * ‖(Ce - C0) (EuclideanSpace.single 1 1)‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ ‖α‖ * (C * (p.ν ^ k)⁻¹ * p.ε) + ‖α‖ * (C * (p.ν ^ k)⁻¹ * p.ε) := by
          gcongr
      _ = 2 * C * (p.ν ^ k)⁻¹ * p.ε * ‖α‖ := by ring

end UnforcedLeray.Short.IIb

end

#print axioms UnforcedLeray.Short.IIb.affineColumnComparison_of
#print axioms UnforcedLeray.Short.IIb.columnIdentification_of
#print axioms UnforcedLeray.Short.IIb.columnPairing_of
#print axioms UnforcedLeray.Short.IIb.inletL0Ptw_of
