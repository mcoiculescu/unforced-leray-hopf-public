import UnforcedLeray.Statement
import UnforcedLeray.Short.PartI.TrainClass
import UnforcedLeray.Units.B0185
import UnforcedLeray.Units.B0187
import UnforcedLeray.Units.B0188
import UnforcedLeray.Units.B0190

/-!
# Part II-a, module `seed-train/ring-lift.tex`: statements

Source of record: `the November 2 reference manuscript`, lines 1196-1338
(Proposition `sct:lift`, "Exact lift, residual and trace", statement at 1204-1239, proof at
1241-1336). Everything here is stated about the concrete objects:

* the exact periodic planar train of Section `sct:section` (lines 241-555), as the predicate
  `IsExactPlanarTrain ν c ψ p`: `(ψ, p)` are the stream/pressure profiles of a
  `B0140.TrainSol ν c` (the object Part I constructs); `IsPlanarTrainProfile` records the
  self-contained properties of lines 258-282 (cylinder Navier-Stokes solution, bounded
  uniformly continuous velocity, bounded periodic pressure, decaying stream, Gaussian datum);
* the lift `u_r = (R/r) v_1`, `u_z = (R/r)(v_2 + ε H)`, `p_raw = (R/r)^2 p`, which is the
  existing library/draft lift `B0185.liftUr / liftUz / rawPressure / liftVelocity /
  liftPressure` (charts of `B0184`, `H = (1 - K) ψ` is `B0185.ageDefect`);
* the similarity field `U_R` (`B0190.simProfile 1 (liftVelocity R ψ)`), and the similarity
  residual `F_R = t^{3/2} * (physical Navier-Stokes residual of the lift)` (equal to
  `s^{3/2} r` of line 1263, see the docstring of `ringResidual`).

Constants `P` of the source are "polynomial in `c, ν⁻¹`": they are written
`C * (1 + c + ν⁻¹) ^ d` with `C, d` independent of `ν, R` and of the train, after fixing
`ρ > 1/2` (so `c = ν ^ (-ρ)`) and the finite collection of orders/exponents, and for `ν` small
(the standing smallness convention of lines 252-256).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187 UnforcedLeray.B0188
  UnforcedLeray.B0190

/-! ### The planar train as a predicate (Section `sct:section`, lines 258-282) -/

/-- The Gaussian initial stream `ψ(q, η, 0) = Σ_n -2 e^{-((q-nc)^2 + η^2)/4}`
(lines 264-268). -/
def trainDatum (c q η : ℝ) : ℝ :=
  ∑' n : ℤ, -2 * Real.exp (-(((q - (n : ℝ) * c) ^ 2 + η ^ 2) / 4))

/-- **The exact periodic planar train** `v = ∇^⊥ψ` with bounded pressure `p`
(lines 258-282): `ψ` is smooth for `s > 0`, `c`-periodic in `q`; `v = (-ψ_η, ψ_q)` is bounded
and uniformly continuous in `(q, η)` for each `s > 0`; `(v, p)` solves the cylinder
Navier-Stokes equations `v_s + v·∇v - νΔv + ∇p = 0` (radial component along `q`, axial along
`η`, `B0188.planarRadialResidual / planarAxialResidual`); `p` is bounded; `ψ(s)` decays as
`|η| → ∞`; and `ψ`, `v` attain the Gaussian datum as `s → 0+`. By the cited Gallay-Slijepcevic
uniqueness theorem this determines the train. -/
structure IsPlanarTrainProfile (ν c : ℝ) (ψ p : ProfilePoint → ℝ) : Prop where
  nu_pos : 0 < ν
  c_pos : 0 < c
  psi_smooth : ContDiffOn ℝ ∞ ψ {x : ProfilePoint | 0 < x.2.2}
  p_smooth : ContDiffOn ℝ ∞ p {x : ProfilePoint | 0 < x.2.2}
  psi_periodic : QPeriodicOn c ψ
  p_periodic : QPeriodicOn c p
  radial_eq : ∀ x : ProfilePoint, 0 < x.2.2 → planarRadialResidual ν ψ p x = 0
  axial_eq : ∀ x : ProfilePoint, 0 < x.2.2 → planarAxialResidual ν ψ p x = 0
  velocity_bdd : ∃ M : ℝ, ∀ x : ProfilePoint, 0 < x.2.2 →
    |streamV1 ψ x| ≤ M ∧ |streamV2 ψ x| ≤ M
  velocity_uc : ∀ s : ℝ, 0 < s → UniformContinuous fun z : ℝ × ℝ =>
    (streamV1 ψ (z.1, z.2, s), streamV2 ψ (z.1, z.2, s))
  pressure_bdd : ∃ M : ℝ, ∀ x : ProfilePoint, 0 < x.2.2 → |p x| ≤ M
  stream_decay : ∀ s : ℝ, 0 < s →
    Tendsto (fun z : ℝ × ℝ => ψ (z.1, z.2, s)) (comap (fun z : ℝ × ℝ => |z.2|) atTop) (𝓝 0)
  stream_init : ∀ q η : ℝ,
    Tendsto (fun s => ψ (q, η, s)) (𝓝[>] 0) (𝓝 (trainDatum c q η))
  v1_init : ∀ q η : ℝ, Tendsto (fun s => streamV1 ψ (q, η, s)) (𝓝[>] 0)
    (𝓝 (-(deriv (fun η' => trainDatum c q η') η)))
  v2_init : ∀ q η : ℝ, Tendsto (fun s => streamV2 ψ (q, η, s)) (𝓝[>] 0)
    (𝓝 (deriv (fun q' => trainDatum c q' η) q))

/-- **The exact periodic planar train** as consumed by this module: `(ψ, p)` are the stream and
pressure profiles (in the chart order `(q, η, s)`, `B0190.trainProfile`) of a train solution
`T : B0140.TrainSol ν c` of the drafts/Part I (the global smooth finite-energy cylinder
Navier-Stokes solution with the Gaussian initial stream, lines 258-282). The properties listed
in `IsPlanarTrainProfile` are fields of `T.isTrain` (smooth, periodic, solenoidal, momentum
equation, initial datum, finite energy, decaying pressure and stream). The train is in the
Gallay-Slijepcevic (BUC) class `IsBUCTrain` (all spatial derivatives bounded on `[0, S]`), the class
in which Part I proves its estimates. -/
def IsExactPlanarTrain (ν c : ℝ) (ψ p : ProfilePoint → ℝ) : Prop :=
  ∃ T : UnforcedLeray.B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain T ∧
    ψ = trainProfile T.ψ ∧ p = trainProfile T.p

/-! ### Similarity residual and `C_per W^{1,p}` -/

/-- Physical Navier-Stokes residual `∂_t u + u·∇u - νΔu + ∇p` of the lift, as an `ℝ³`-vector
(radial part along `e_r`, axial along `e_3`; `B0187.cylRadialResidual / cylAxialResidual`),
at physical time `t` and point `x`. Its Lean value on the axis is a junk value of a null set. -/
def physResidualField (R ν : ℝ) (ψ p : ProfilePoint → ℝ) (t : ℝ) (x : Space) : Space :=
  cylRadialResidual ν (liftUr R ψ) (liftUz R ψ) (rawPressure R p) (Axi.ϱ x) (x 2) t • Axi.eR x +
    cylAxialResidual ν (liftUr R ψ) (liftUz R ψ) (rawPressure R p) (Axi.ϱ x) (x 2) t • Axi.e3

/-- The similarity residual `F_R(τ, y) = t^{3/2} (physical residual)(t, √t y)`, `t = e^τ`,
`y = x/√t`. In the chart this is `F_R = s^{3/2} r` (line 1263): the physical residual equals
`(R/r)^3 r` and `s^{3/2} = (R/r)^3 t^{3/2}`. -/
def ringResidual (R ν : ℝ) (ψ p : ProfilePoint → ℝ) (τ : ℝ) (y : Space) : Space :=
  Real.exp (τ / 2) ^ 3 • physResidualField R ν ψ p (Real.exp τ) (Real.exp (τ / 2) • y)

/-- `F ∈ C W^{1,p}(ℝ³)` with `sup_τ ‖F(τ)‖_{W^{1,p}} ≤ B`: for each `τ`, `F(τ)` and its weak
first derivatives `G τ i` lie in `L^p(ℝ³; ℝ³)`, with `‖F τ‖_p + Σ_i ‖G τ i‖_p ≤ B`, and
`τ ↦ (F τ, G τ)` is continuous in `L^p`. (Periodicity of `F` is stated separately.) -/
def IsCperW1pBdd (p : ℝ) (B : ℝ) (F : ℝ → SpatialField) : Prop :=
  ∃ G : ℝ → Fin 3 → SpatialField,
    (∀ τ, MemLp (F τ) (ENNReal.ofReal p) volume) ∧
    (∀ τ i, MemLp (G τ i) (ENNReal.ofReal p) volume ∧ HasWeakSpatialDerivative i (F τ) (G τ i)) ∧
    (∀ τ, (eLpNorm (F τ) (ENNReal.ofReal p) volume).toReal +
        ∑ i, (eLpNorm (G τ i) (ENNReal.ofReal p) volume).toReal ≤ B) ∧
    ∀ τ₀, Tendsto (fun τ => (eLpNorm (F τ - F τ₀) (ENNReal.ofReal p) volume).toReal +
        ∑ i, (eLpNorm (G τ i - G τ₀ i) (ENNReal.ofReal p) volume).toReal) (𝓝 τ₀) (𝓝 0)

/-- The polynomial constants of the source: `C (1 + c + ν⁻¹)^d`. -/
def polyConst (C : ℝ) (d : ℕ) (ν c : ℝ) : ℝ := C * (1 + c + ν⁻¹) ^ d

/-! ### The residual coefficient table (lines 1259-1276) -/

/-- Weighted late bound `⟨η/√s⟩^{2m} |X| ≤ B s^{-a}` for `s ≥ 1`
(`⟨u⟩ = (1+u²)^{1/2}`; the `L^∞_η L^∞_q` bound with normalised weight, line 1260). -/
def WtdBound (m : ℕ) (X : ProfilePoint → ℝ) (a B : ℝ) : Prop :=
  ∀ x : ProfilePoint, 1 ≤ x.2.2 → (1 + x.2.1 ^ 2 / x.2.2) ^ m * |X x| ≤ B * x.2.2 ^ (-a)

/-- Weighted exponentially small late bound `⟨η/√s⟩^{2m} |X| ≤ B e^{-κ ν s/c²}`, `s ≥ 1`. -/
def ExpBound (κ ν c : ℝ) (m : ℕ) (X : ProfilePoint → ℝ) (B : ℝ) : Prop :=
  ∀ x : ProfilePoint, 1 ≤ x.2.2 →
    (1 + x.2.1 ^ 2 / x.2.2) ^ m * |X x| ≤ B * Real.exp (-(κ * ν * x.2.2 / c ^ 2))

/-- **The complete late residual table** (lines 1259-1276), for the coefficients `A₁, B₁, B₂,
B₃, A₂` of `B0188` (tex 2890-2914) of the exact train, `s ≥ 1`:
* `A₁, B₁`: size `s^{-2}` (an `η` derivative gains `s^{-1/2}`), `(K+3)` also `s^{-2}`;
* `B₂, B₃`: size `s^{-3/2}` (`η` derivative `s^{-2}`), `(K+3)` size `s^{-5/2}`;
* `A₂`: exponentially small `e^{-κ ν s / c²}`, also after `∂_η` and `(K+3)`;
* every `∂_q` derivative is exponentially small.
For each fixed weight `m`. -/
def RingLateTable : Prop :=
  ∀ (ρ : ℝ) (m : ℕ), 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∃ (C : ℝ) (d : ℕ) (κ : ℝ), 0 < κ ∧
    ∀ ν ∈ Ioo 0 ν₀, ∀ ψ p : ProfilePoint → ℝ, IsExactPlanarTrain ν (ν ^ (-ρ)) ψ p →
      let c := ν ^ (-ρ)
      let B := polyConst C d ν c
      (WtdBound m (coeffA₁ ν ψ p) 2 B ∧ WtdBound m (partialEta (coeffA₁ ν ψ p)) (5 / 2) B ∧
        WtdBound m (ageShift 3 (coeffA₁ ν ψ p)) 2 B ∧
        ExpBound κ ν c m (partialQ (coeffA₁ ν ψ p)) B) ∧
      (WtdBound m (coeffB₁ ν ψ) 2 B ∧ WtdBound m (partialEta (coeffB₁ ν ψ)) (5 / 2) B ∧
        WtdBound m (ageShift 3 (coeffB₁ ν ψ)) 2 B ∧
        ExpBound κ ν c m (partialQ (coeffB₁ ν ψ)) B) ∧
      (WtdBound m (coeffB₂ ν ψ) (3 / 2) B ∧ WtdBound m (partialEta (coeffB₂ ν ψ)) 2 B ∧
        WtdBound m (ageShift 3 (coeffB₂ ν ψ)) (5 / 2) B ∧
        ExpBound κ ν c m (partialQ (coeffB₂ ν ψ)) B) ∧
      (WtdBound m (coeffB₃ ν ψ) (3 / 2) B ∧ WtdBound m (partialEta (coeffB₃ ν ψ)) 2 B ∧
        WtdBound m (ageShift 3 (coeffB₃ ν ψ)) (5 / 2) B ∧
        ExpBound κ ν c m (partialQ (coeffB₃ ν ψ)) B) ∧
      (ExpBound κ ν c m (coeffA₂ ν ψ) B ∧ ExpBound κ ν c m (partialEta (coeffA₂ ν ψ)) B ∧
        ExpBound κ ν c m (ageShift 3 (coeffA₂ ν ψ)) B ∧
        ExpBound κ ν c m (partialQ (coeffA₂ ν ψ)) B)

/-- Bounded early-age coefficients (lines 1294-1297, "at zero age the integrands are bounded"):
for `0 < s ≤ 1` each of `X, ∂_η X, ∂_q X, (K+3) X` (`X = A₁, A₂, B₁, B₂, B₃`) satisfies
`⟨η⟩^{2m} |·| ≤ B`. -/
def RingEarlyBound : Prop :=
  ∀ (ρ : ℝ) (m : ℕ), 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∃ (C : ℝ) (d : ℕ),
    ∀ ν ∈ Ioo 0 ν₀, ∀ ψ p : ProfilePoint → ℝ, IsExactPlanarTrain ν (ν ^ (-ρ)) ψ p →
      ∀ x : ProfilePoint, 0 < x.2.2 → x.2.2 ≤ 1 → ∀ X ∈ ({coeffA₁ ν ψ p, coeffA₂ ν ψ, coeffB₁ ν ψ,
          coeffB₂ ν ψ, coeffB₃ ν ψ} : Set (ProfilePoint → ℝ)),
        (1 + x.2.1 ^ 2) ^ m * |X x| ≤ polyConst C d ν (ν ^ (-ρ)) ∧
        (1 + x.2.1 ^ 2) ^ m * |partialEta X x| ≤ polyConst C d ν (ν ^ (-ρ)) ∧
        (1 + x.2.1 ^ 2) ^ m * |partialQ X x| ≤ polyConst C d ν (ν ^ (-ρ)) ∧
        (1 + x.2.1 ^ 2) ^ m * |ageShift 3 X x| ≤ polyConst C d ν (ν ^ (-ρ))

/-! ### The conclusions of Proposition `sct:lift` (lines 1204-1239) -/

/-- **Exact solenoidality of the lift** (lines 1211-1214, 1243-1246): the field with
`u_r = (R/r) v_1`, `u_z = (R/r)(v_2 + εH)` has vanishing cylindrical divergence off the axis,
for every stream that is `C²` at the chart point. -/
def RingSolenoidal : Prop :=
  ∀ (R : ℝ), 2 ≤ R → ∀ (ψ : ProfilePoint → ℝ) (r z t : ℝ), r ≠ 0 →
    ContDiffAt ℝ 2 ψ (profileChart R r z t) →
      cylDivergence (liftUr R ψ) (liftUz R ψ) r z t = 0

/-- **Discrete self-similarity** (lines 1215-1217): for `λ = e^{c/R}`,
`u(λx, λ²t) = λ^{-1} u(x,t)`, `p_raw(λx, λ²t) = λ^{-2} p_raw(x,t)`, and the similarity
field `U_R` and pressure have period `2c/R` (`= 2εc`). -/
def RingDSS : Prop :=
  ∀ (R c : ℝ) (ψ p : ProfilePoint → ℝ), 2 ≤ R → QPeriodicOn c ψ → QPeriodicOn c p →
    (∀ t : ℝ, 0 < t → ∀ y : Space,
      liftVelocity R ψ (Real.exp (c / R) ^ 2 * t) (Real.exp (c / R) • y) =
        (Real.exp (c / R))⁻¹ • liftVelocity R ψ t y) ∧
    (∀ t : ℝ, 0 < t → ∀ y : Space,
      liftPressure R p (Real.exp (c / R) ^ 2 * t) (Real.exp (c / R) • y) =
        (Real.exp (c / R) ^ 2)⁻¹ * liftPressure R p t y) ∧
    (∀ τ : ℝ, simProfile 1 (liftVelocity R ψ) (τ + 2 * c / R) =
        simProfile 1 (liftVelocity R ψ) τ) ∧
    (∀ τ : ℝ, simProfile 2 (liftPressure R p) (τ + 2 * c / R) =
        simProfile 2 (liftPressure R p) τ)

/-- **Smoothness through the axis for positive time** (line 1214, proof lines 1305-1322): the
lifted velocity and raw pressure, as Cartesian functions of `(t, x) ∈ (0,∞) × ℝ³`, agree off
the axis with functions that are `C^∞` on `{t > 0}` (including the axis). -/
def RingAxisSmooth : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioo 0 ν₀, ∀ ψ p : ProfilePoint → ℝ,
    IsExactPlanarTrain ν (ν ^ (-ρ)) ψ p → ∀ R : ℝ, 2 ≤ R →
      ∃ (u : ℝ × Space → Space) (π : ℝ × Space → ℝ),
        ContDiffOn ℝ ∞ u {z : ℝ × Space | 0 < z.1} ∧ ContDiffOn ℝ ∞ π {z : ℝ × Space | 0 < z.1} ∧
        ∀ t : ℝ, 0 < t → ∀ x : Space, x ∉ Axi.axis →
          u (t, x) = liftVelocity R ψ t x ∧ π (t, x) = liftPressure R p t x

/-- **Globally bounded fixed spatial derivatives of `U_R`** (lines 1217-1219, 1322-1325):
for every `k`, `‖D^j U_R(·, τ)‖_∞ ≤ P_k` for `j ≤ k`, uniformly in `R ≥ 2` and `τ`; `U_R(τ)` is
smooth on all of `ℝ³` (a smooth extension across the axis exists). -/
def RingBoundedDerivs : Prop :=
  ∀ (ρ : ℝ) (k : ℕ), 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∃ (C : ℝ) (d : ℕ),
    ∀ ν ∈ Ioo 0 ν₀, ∀ ψ p : ProfilePoint → ℝ, IsExactPlanarTrain ν (ν ^ (-ρ)) ψ p →
      ∀ R : ℝ, 2 ≤ R → ∃ U : ℝ → Space → Space, (∀ τ, ContDiff ℝ ∞ (U τ)) ∧
        (∀ τ (y : Space), Axi.ϱ y ≠ 0 → U τ y = simProfile 1 (liftVelocity R ψ) τ y) ∧
        ∀ j ≤ k, ∀ (τ : ℝ) (y : Space),
          ‖iteratedFDeriv ℝ j (U τ) y‖ ≤ polyConst C d ν (ν ^ (-ρ))

/-- **The residual bound** (lines 1219-1225, eq. `sct:residual-bound`): for `2 ≤ p < ∞`,
`‖F_R‖_{C_per W^{1,p}(ℝ³)} ≤ P_p ε^{1-2/p}`, `ε = 1/R`, with `F_R` periodic of period `2c/R`
(at `p = 11/4` this is `P ε^{3/11}`). -/
def RingResidualBound : Prop :=
  ∀ (ρ p : ℝ), 1 / 2 < ρ → 2 ≤ p → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∃ (C : ℝ) (d : ℕ),
    ∀ ν ∈ Ioo 0 ν₀, ∀ ψ pr : ProfilePoint → ℝ, IsExactPlanarTrain ν (ν ^ (-ρ)) ψ pr →
      ∀ R : ℝ, 2 ≤ R →
        (∀ τ, ringResidual R ν ψ pr (τ + 2 * ν ^ (-ρ) / R) = ringResidual R ν ψ pr τ) ∧
        IsCperW1pBdd p (polyConst C d ν (ν ^ (-ρ)) * (R⁻¹) ^ (1 - 2 / p)) (ringResidual R ν ψ pr)

/-- The `t = 0` stream formula with the Gaussian inlet (lines 1330-1335): `𝒫(r, z) = r ψ(q, η, 0)`,
`q = R log (r/R)`, `η = R z / r`. -/
def inletStream (c R r z : ℝ) : ℝ := r * trainDatum c (R * Real.log (r / R)) (R * z / r)

/-- The raw inlet `a_raw = u(·, 0)`: `u_r = -r⁻¹ ∂_z 𝒫`, `u_z = r⁻¹ ∂_r 𝒫` (line 1210 stream
form), as a field on `ℝ³` (value `0` on the axis, a null set). -/
def inletRaw (c R : ℝ) (x : Space) : Space :=
  (-(1 / Axi.ϱ x) * deriv (fun z => inletStream c R (Axi.ϱ x) z) (x 2)) • Axi.eR x +
    ((1 / Axi.ϱ x) * deriv (fun r => inletStream c R r (x 2)) (Axi.ϱ x)) • Axi.e3

/-- **The raw inlet** (lines 1226-1229, 1328-1336, eq. `sct:raw-trace`): `a_raw` is distributionally
solenoidal, has the same discrete scaling, is nonzero, and is smooth away from `0` (also at
nonzero axis points) with `|D^j a_raw(x)| ≤ C_j |x|^{-1-j}`. -/
def RingInlet : Prop :=
  ∀ c R : ℝ, 0 < c → 2 ≤ R →
    IsSolenoidal (inletRaw c R) ∧
    (∀ x : Space, Axi.ϱ x ≠ 0 →
      inletRaw c R (Real.exp (c / R) • x) = (Real.exp (c / R))⁻¹ • inletRaw c R x) ∧
    (∃ x : Space, inletRaw c R x ≠ 0) ∧
    ∃ a : Space → Space, ContDiffOn ℝ ∞ a {x : Space | x ≠ 0} ∧
      (∀ x : Space, x ∉ Axi.axis → a x = inletRaw c R x) ∧
      ∀ j : ℕ, ∃ C : ℝ, ∀ x : Space, x ≠ 0 → ‖iteratedFDeriv ℝ j a x‖ ≤ C * ‖x‖ ^ (-(1 + (j : ℝ)))

/-- **The step "late table + bounded early coefficients ⟹ residual bound"** (lines 1277-1297):
change to similarity variables `ϱ = R/√s`, `z_y = η/√s`, `q = Rτ/2 - (R/2) log s`,
`dy = π R² s^{-5/2} ds dη`; `∂_{z_y} F_R = s² ∂_η r`, `∂_ϱ F_R = s²[∂_q - ε(K+3)] r`; late
integrands `s^{-p/2-2}, s^{-2}`; zero-age integrands `s^{3p/2-5/2}, s^{2p-5/2}`; Jacobian costs
`R^{2/p}`; continuity by dominated convergence. -/
def RingResidualFromTable : Prop :=
  RingLateTable → RingEarlyBound → RingResidualBound

/-- **Proposition `sct:lift`** (lines 1204-1239): all conclusions, for the concrete train. -/
def RingLiftProposition : Prop :=
  RingSolenoidal ∧ RingDSS ∧ RingAxisSmooth ∧ RingBoundedDerivs ∧ RingResidualBound ∧ RingInlet

end UnforcedLeray.Short.PartIIa
