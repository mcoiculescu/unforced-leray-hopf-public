import UnforcedLeray.Cons.L2.BackgroundConcrete.Operators
import UnforcedLeray.Units.B0579
import UnforcedLeray.Units.B0238
import UnforcedLeray.Short.PartI.TrainClass

/-!
# Part II-b: shared definitions (free comparison, ordinary mixed solve, nonlinear correction)

Source of record: `the November 2 reference manuscript` (SP), modules
`background/free-comparison.tex` (SP 1897-2024) and `background/short-background.tex`
(SP 2026-2643).

## What is reused (existing Lean)

* The parameter record `Cons.C03.Concrete.Params` (`ν, c, ε`, the actual train, `period = 2εc`,
  `R = ε⁻¹`, `raw = U_raw`, `inlet`, ...), the state space `Params.Z = X_{q₀} × ℝ²`, the body
  space `Params.Y`, the pairing relations `RawRel`, `OrdRel`, `QuadRel` and the pairings
  `pairF`, `IsSolTest` (`Cons/L2/BackgroundConcrete/{Fields,Spaces,Operators}.lean`).
* The age-weighted cylinder measure `Axi.ageμ` (`H_r` has measure `ageμ c (r/2 - 5/2)`) and the
  ring lift `Axi.Nv` with `eLpNorm_Nv` (`Lib/AxisymmetricB/Lift.lean`).
* The phase-space transposes `driftT`, `nuLapT`, `L0T`, `gradT`, `IsPhaseTest`
  (`Lib/PhaseSpace`, `Units/B0411`), the cylinder cell data `B0579.cellMeasure`, `B0579.IsCylTest`,
  `B0579.pd` and the train `B0140.TrainSol`.

## What is new here

* `BgRegime`: the standing parameters of SP 2028-2031.
* Weak first-order calculus in the chart `(s, (q, η))` (`HasWeakFO`), the profile spaces `H_r`
  (`hNorm`, `InHr`), the complex ring lift `NvC` and the *free responses* `T_εF` (`IsResponse`,
  physical, via the Cartesian projected equation `(μ + L)w = 𝔓 f` on the graph `D_r`) and
  `T_0F` (`IsFlatResponse`, the flat equation `(S + μ - νsΔ_{q,η}) b = P_0 F`).

Conventions. Profiles are complex 2-vectors `(b_r, b_z)` on `Coord = ℝ × (ℝ × ℝ) = (s, (q, η))`,
`c`-periodic in `q` (almost everywhere); only values on `s > 0` matter. Equations are tested
with smooth compactly supported tests in the open set `s > 0`. A "response" is characterised by
its defining equation in distributions; uniqueness of the response is the bijectivity statement
of SP Lemma `bg:common-body-graph` (Part II-a) and for `ε = 0` the flat uniqueness clause of
`ProfileGraphFlat`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ## The standing regime (SP 2028-2031) -/

/-- `p = 11/4` of the background (SP 2032). -/
def bgp : ℝ := 11 / 4

/-- The auxiliary exponent `r = 23/8` of `bg:lp-free-comparison` (SP 1941, 1992). -/
def bgr : ℝ := 23 / 8

/-- SP 2031-2037: `c = ν⁻²`, `R = ε⁻¹`, `ε = e^{-d/ν}`, `P = 2εc`, `0 < d₋ ≤ d ≤ d₊`.
(`P = 2εc` is `Params.period`.)  The train `p.train` is *the* train of Part I: the
Gallay-Slijepcevic solution in `BUC` (SP 270-288: "a unique global mild solution in `BUC`"; SP 2040:
"Let `v_c` be the train of Proposition `sct:train`"), i.e. it lies in the class `PartI.IsBUCTrain` (all spatial derivatives
bounded on every `[0, S] × ℝ²`, `Short/PartI/TrainClass.lean`) in which Part I proves its estimates
(field `train_buc`; `Params.trainData` itself is an arbitrary `B0140.TrainSol`). -/
structure BgRegime (p : Params) (d dm dp : ℝ) : Prop where
  dm_pos : 0 < dm
  dm_le : dm ≤ d
  le_dp : d ≤ dp
  eps_eq : p.ε = Real.exp (-d / p.ν)
  c_eq : p.c = (p.ν ^ 2)⁻¹
  /-- The actual train is the BUC train of Part I (SP 270-288). -/
  train_buc : UnforcedLeray.Short.PartI.IsBUCTrain p.train
  /-- The stream `ψ` of the train is jointly smooth in `(s, q, η)` for `s > 0` (SP 397: the train and
  its decaying stream are smooth; SP 2049). -/
  train_stream_smooth : ContDiffOn ℝ ∞
    (fun x : ℝ × UnforcedLeray.Cyl.Plane => p.train.ψ x.1 x.2) (Ioi 0 ×ˢ univ)

/-! ## Weak first-order calculus in the chart `(s, (q, η))` -/

/-- The chart space `(s, (q, η))`. -/
abbrev Coord : Type := ℝ × (ℝ × ℝ)

/-- Complex meridional vectors `(b_r, b_z)`. -/
abbrev CMerid : Type := EuclideanSpace ℂ (Fin 2)

/-- A complex meridional profile. -/
abbrev CProf : Type := Coord → CMerid

/-- A test function in the open set `s > 0`: smooth with compact support there. -/
structure IsCoordTest (φ : Coord → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  compact : HasCompactSupport φ
  supp : tsupport φ ⊆ Ioi (0 : ℝ) ×ˢ univ

/-- The coordinate directions `∂_s, ∂_q, ∂_η`. -/
def cdir : Fin 3 → Coord := ![(1, (0, 0)), (0, (1, 0)), (0, (0, 1))]

/-- The partial derivative `∂_j φ` (`j = 0, 1, 2` for `s, q, η`). -/
def cpd (j : Fin 3) (φ : Coord → ℝ) (x : Coord) : ℝ := fderiv ℝ φ x (cdir j)

/-- The Lebesgue transpose of `v·∇ + d` on a test: `-div(vφ) + dφ`. -/
def coordTranspose (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) (φ : Coord → ℝ) (x : Coord) : ℝ :=
  -(∑ j : Fin 3, cpd j (fun y => v y j * φ y) x) + d x * φ x

/-- `g = v·∇u + d u` in distributions on `s > 0`, with convergent pairings. -/
def HasWeakFO (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) (u g : Coord → ℂ) : Prop :=
  (∀ φ, IsCoordTest φ →
    Integrable (fun x => u x * (coordTranspose v d φ x : ℂ)) ∧
      Integrable (fun x => g x * (φ x : ℂ))) ∧
  ∀ φ, IsCoordTest φ →
    ∫ x, g x * (φ x : ℂ) = ∫ x, u x * (coordTranspose v d φ x : ℂ)

/-- Componentwise `HasWeakFO` for profiles. -/
def HasWeakVec (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) (b g : CProf) : Prop :=
  ∀ i : Fin 2, HasWeakFO v d (fun x => b x i) (fun x => g x i)

/-- `S = s∂_s` (SP 1651). -/
def vS : Coord → Fin 3 → ℝ := fun x => ![x.1, 0, 0]

/-- `∂_q`. -/
def vQ0 : Coord → Fin 3 → ℝ := fun _ => ![0, 1, 0]

/-- `∂_η`. -/
def vEta : Coord → Fin 3 → ℝ := fun _ => ![0, 0, 1]

/-- `Q_ε = ∂_q - ε(K+1)`, `K = 2S + η∂_η` (SP 1651-1653): first-order part. -/
def vQ (ε : ℝ) : Coord → Fin 3 → ℝ := fun x => ![-2 * ε * x.1, 1, -ε * x.2.2]

/-- Zero-order part `-ε` of `Q_ε`. -/
def dQ (ε : ℝ) : Coord → ℝ := fun _ => -ε

/-- The zero function, for `HasWeakVec` without zero-order term. -/
def dZero : Coord → ℝ := fun _ => 0

/-! ## The spaces `H_r` -/

/-- Shift `q ↦ q + c`. -/
def qShift (c : ℝ) (x : Coord) : Coord := (x.1, (x.2.1 + c, x.2.2))

/-- `c`-periodicity in `q`, almost everywhere on the half space `s > 0` where `H_r` lives
(SP 1900-1903); no condition for `s ≤ 0`. -/
def QPeriodic (c : ℝ) (b : CProf) : Prop :=
  ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), b (qShift c x) = b x

/-- The measure `s^{r/2-5/2} ds dq/c dη` of `H_r` (SP 1900-1903; cell normalized by `dq/c`). -/
def hMeas (c r : ℝ) : Measure Coord := Axi.ageμ c (r / 2 - 5 / 2)

/-- `‖b‖_{H_r}`. -/
def hNorm (c r : ℝ) (b : CProf) : ℝ≥0∞ := eLpNorm b (ENNReal.ofReal r) (hMeas c r)

/-- `b ∈ H_r`: `c`-periodic, measurable, finite norm. -/
structure InHr (c r : ℝ) (b : CProf) : Prop where
  periodic : QPeriodic c b
  meas : AEStronglyMeasurable b (hMeas c r)
  finite : hNorm c r b < ⊤

/-- `√s b`. -/
def sqrtS (b : CProf) : CProf := fun x => (Real.sqrt x.1 : ℂ) • b x

/-! ## The physical free response `T_ε` (SP 1634-1700, 1339-1420) -/

/-- Real meridional part. -/
def reM (v : CMerid) : Axi.Merid := WithLp.toLp 2 fun i => (v i).re

/-- Imaginary meridional part. -/
def imM (v : CMerid) : Axi.Merid := WithLp.toLp 2 fun i => (v i).im

/-- The complex ring lift `N_v b = √s (b_r e_r + b_z e_z)` at the chart point (SP 1903, `Mb = √s b`
physical lift; `Axi.Nv` applied to real and imaginary parts). -/
def NvC (R : ℝ) (b : CProf) (x : ℝ × Space) : CVec3 :=
  B0412.realC (Axi.Nv R (fun z => reM (b z)) x.1 x.2) +
    Complex.I • B0412.realC (Axi.Nv R (fun z => imM (b z)) x.1 x.2)

/-- The phase-normalized `L^r` norm of a field on `ℝ × ℝ³` over one period
(`‖f‖_{Y_r}`, SP 1341-1344). -/
def phaseLpNorm (P r : ℝ) (f : ℝ × Space → CVec3) : ℝ≥0∞ :=
  (ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖f (t, y)‖ₑ ^ r) ^ (1 / r)

/-- `f ∈ Y_r` (period `P`): periodic, measurable, finite norm. -/
structure IsInYr (P r : ℝ) (f : ℝ × Space → CVec3) : Prop where
  periodic : ∀ᵐ x : ℝ × Space, f (x.1 + P, x.2) = f x
  meas : AEStronglyMeasurable f volume
  finite : phaseLpNorm P r f < ⊤

/-- `Lw = g` in distributions on `(ℝ/Pℤ) × ℝ³` for fields given pointwise: `⟪Lᵗ Φ, w⟫ = ⟪Φ, g⟫`
for every phase test. -/
def HasPtwOp (P : ℝ) (Lt : (ℝ × Space → CVec3) → ℝ × Space → CVec3)
    (w g : ℝ × Space → CVec3) : Prop :=
  ∀ Φ, IsPhaseTest P Φ → pairF P (Lt Φ) w = pairF P Φ g

/-- `w` solves `(μ + L) w = 𝔓 f` with `w ∈ D_{r,σ}` (SP 1339-1364, `bg:common-body-graph` at 1356):
`w, νΔw, 𝒯w ∈ Y_r`, `div w = 0`, and `⟪(μ + L)ᵗΦ, w⟫ = ⟪Φ, f⟫` for every solenoidal phase test
(on which the Leray projection is invisible), `L = 𝒯 - νΔ - 1/2`. -/
structure IsFreeResponse (ν : ℝ) (μ : ℂ) (r P : ℝ) (f w : ℝ × Space → CVec3) : Prop where
  mem_w : IsInYr P r w
  lapl : ∃ a, IsInYr P r a ∧ HasPtwOp P (nuLapT ν) w a
  drift : ∃ b, IsInYr P r b ∧ HasPtwOp P driftT w b
  solenoidal : ∀ φ : ℝ × Space → ℂ, IsPhaseTest P φ → pairF P (gradT φ) w = 0
  equation : ∀ Φ, IsSolTest P Φ →
    pairF P (fun x => L0T ν Φ x + μ • Φ x) w = pairF P Φ f

/-- `b = T_ε F` (SP 1665-1672): the physical response of the lifted source, `R = ε⁻¹`,
`P = 2εc`. -/
def IsResponse (ν c ε : ℝ) (μ : ℂ) (r : ℝ) (F b : CProf) : Prop :=
  IsFreeResponse ν μ r (2 * ε * c) (NvC ε⁻¹ F) (NvC ε⁻¹ b)

/-! ## The flat response `T_0` (SP 1684-1686, 1923-1927) -/

/-- Planar solenoidal tests `Ψ = (Ψ_r, Ψ_z)` in `s > 0`: `∂_qΨ_r + ∂_ηΨ_z = 0`. -/
structure IsPlanarSolTest (Ψ : Coord → Fin 2 → ℝ) : Prop where
  smooth : ∀ i, IsCoordTest (fun x => Ψ x i)
  div_free : ∀ x, cpd 1 (fun y => Ψ y 0) x + cpd 2 (fun y => Ψ y 1) x = 0

/-- Transpose of `μ - A_0 = μ + S - νsΔ_{q,η}` (Lebesgue pairing):
`(μ - 1)Ψ - SΨ - νsΔΨ`. -/
def flatTranspose (ν : ℝ) (μ : ℂ) (Ψ : Coord → Fin 2 → ℝ) (x : Coord) (i : Fin 2) : ℂ :=
  (μ - 1) * (Ψ x i : ℂ) - ((x.1 * cpd 0 (fun y => Ψ y i) x : ℝ) : ℂ) -
    ((ν * x.1 * (cpd 1 (fun y => cpd 1 (fun z => Ψ z i) y) x +
      cpd 2 (fun y => cpd 2 (fun z => Ψ z i) y) x) : ℝ) : ℂ)

/-- The pairing `b·Ψ`. -/
def cdot (b : CProf) (Ψ : Coord → Fin 2 → ℝ) (x : Coord) : ℂ := ∑ i : Fin 2, b x i * (Ψ x i : ℂ)

/-- `b = T_0 F`: `b` is solenoidal in `(q, η)` and `(μ + S - νsΔ_{q,η}) b = P_0 F`, tested against
planar solenoidal tests (`P_0` invisible on them). -/
structure IsFlatResponse (ν : ℝ) (μ : ℂ) (F b : CProf) : Prop where
  solenoidal : ∀ φ, IsCoordTest φ →
    Integrable (fun x => b x 0 * (cpd 1 φ x : ℂ) + b x 1 * (cpd 2 φ x : ℂ)) ∧
      ∫ x, (b x 0 * (cpd 1 φ x : ℂ) + b x 1 * (cpd 2 φ x : ℂ)) = 0
  equation : ∀ Ψ, IsPlanarSolTest Ψ →
    Integrable (fun x => ∑ i : Fin 2, b x i * flatTranspose ν μ Ψ x i) ∧
      Integrable (cdot F Ψ) ∧
      ∫ x, ∑ i : Fin 2, b x i * flatTranspose ν μ Ψ x i = ∫ x, cdot F Ψ x

/-- The graph class of the flat estimate: `b, Sb, √s Q_0 b, √s ∂_η b ∈ H_r`. -/
structure InFlatClass (c r : ℝ) (b : CProf) : Prop where
  inHr : InHr c r b
  deriv : ∃ Sb Qb Eb : CProf, HasWeakVec vS dZero b Sb ∧ HasWeakVec vQ0 dZero b Qb ∧
    HasWeakVec vEta dZero b Eb ∧ InHr c r Sb ∧ InHr c r (sqrtS Qb) ∧ InHr c r (sqrtS Eb)

/-- The graph bound `‖b‖ + ‖Sb‖ + √ν‖√s(Q_ε b, ∂_η b)‖ ≤ C‖F‖` of `bg:profile-graph`
(SP 1912-1918); `ε = 0` is the flat case `Q_0 = ∂_q`. -/
def GraphBound (ν c r ε C : ℝ) (F b : CProf) : Prop :=
  ∃ Sb Qb Eb : CProf, HasWeakVec vS dZero b Sb ∧ HasWeakVec (vQ ε) (dQ ε) b Qb ∧
    HasWeakVec vEta dZero b Eb ∧
    hNorm c r b + hNorm c r Sb +
        ENNReal.ofReal (Real.sqrt ν) * (hNorm c r (sqrtS Qb) + hNorm c r (sqrtS Eb))
      ≤ ENNReal.ofReal C * hNorm c r F

/-! ## First-order operators supported in the observation box (SP 1940-1952) -/

/-- The observation box `σ ≤ s ≤ H₁`, `|η| ≤ L₁`. -/
def obsBox (σ H₁ L₁ : ℝ) : Set Coord := Icc σ H₁ ×ˢ univ ×ˢ Icc (-L₁) L₁

/-- A first-order operator `B b = A_q ∂_q b + A_η ∂_η b + A_0 b` in `(q, η)` with smooth matrix
coefficients supported in the observation box, with all coefficient derivatives up to order 8
(the order used for the cutoffs in `near:compact-free-comparison`) bounded by `Γ`. -/
structure ObsOp (σ H₁ L₁ Γ : ℝ) where
  Aq : Coord → (CMerid →L[ℂ] CMerid)
  Aeta : Coord → (CMerid →L[ℂ] CMerid)
  A0 : Coord → (CMerid →L[ℂ] CMerid)
  smooth : ContDiff ℝ ∞ Aq ∧ ContDiff ℝ ∞ Aeta ∧ ContDiff ℝ ∞ A0
  supp : ∀ x, x ∉ obsBox σ H₁ L₁ → Aq x = 0 ∧ Aeta x = 0 ∧ A0 x = 0
  bounded : ∀ k ≤ 8, ∀ x, ‖iteratedFDeriv ℝ k Aq x‖ ≤ Γ ∧ ‖iteratedFDeriv ℝ k Aeta x‖ ≤ Γ ∧
    ‖iteratedFDeriv ℝ k A0 x‖ ≤ Γ

/-- `B` applied to `d` with weak `q`- and `η`-derivatives `gq, gη`. -/
def ObsOp.apply {σ H₁ L₁ Γ : ℝ} (B : ObsOp σ H₁ L₁ Γ) (d gq gη : CProf) : CProf :=
  fun x => B.Aq x (gq x) + B.Aeta x (gη x) + B.A0 x (d x)

/-- The rate statement of `bg:lp-comparison-rate` (and its Hilbert version): there are a fixed
integer `k` and a constant `C` such that for every `Γ ≥ 1` dominating `ν, ν⁻¹, c, c⁻¹, σ⁻¹, H₁, L₁`,
`|μ|`, the reciprocal gap `(Re μ + gap)⁻¹` and the coefficient seminorms of `B`, and all
`0 < ε ≤ 1` with `P = 2εc ≤ 1`, every pair of responses `b_ε = T_εF`, `b_0 = T_0F` of
`F ∈ H_r` satisfies `‖B(b_ε - b_0)‖_{H_r} ≤ CΓ^kε^θ‖F‖_{H_r}`; the derivatives in `B(b_ε - b_0)`
are weak and exist. `gap = γ_r = (3/r - 1)/2`. The cutoffs `χ, χ₁` of the Hilbert proposition are
chosen from the box by a fixed recipe and their `C⁸` norms are polynomial in the box data,
hence absorbed in `Γ^k`. -/
def CompRate (r gap θ : ℝ) : Prop :=
  ∃ (k : ℕ) (C : ℝ), 0 < C ∧
    ∀ (Γ ν c σ H₁ L₁ : ℝ) (μ : ℂ), 1 ≤ Γ → ν ≤ Γ → ν⁻¹ ≤ Γ → c ≤ Γ → c⁻¹ ≤ Γ → σ⁻¹ ≤ Γ →
      H₁ ≤ Γ → L₁ ≤ Γ → ‖μ‖ ≤ Γ → Γ⁻¹ ≤ μ.re + gap → 0 < ν → 0 < c → 0 < σ →
    ∀ B : ObsOp σ H₁ L₁ Γ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → 2 * ε * c ≤ 1 →
    ∀ F bε b0 : CProf, InHr c r F → InHr c r bε → IsResponse ν c ε μ r F bε →
      IsFlatResponse ν μ F b0 → InFlatClass c r b0 →
      ∃ gq gη : CProf, HasWeakVec vQ0 dZero (bε - b0) gq ∧ HasWeakVec vEta dZero (bε - b0) gη ∧
        hNorm c r (B.apply (bε - b0) gq gη) ≤
          ENNReal.ofReal (C * Γ ^ k * ε ^ θ) * hNorm c r F

end UnforcedLeray.Short.IIb
