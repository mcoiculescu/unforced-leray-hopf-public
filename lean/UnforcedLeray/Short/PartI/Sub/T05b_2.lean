import UnforcedLeray.Short.PartI.Sub.T05
import UnforcedLeray.Short.PartI.Sub.T02_3

/-!
# Part I, task `PartI:T05b/2`: `TrainCutoffEnergyIneq` (conditional decomposition)

Source of record: `the November 2 reference manuscript`, lines 276-288 ("It gives a
unique global mild solution in BUC ... Approximation and transverse cutoffs then give the velocity
and vorticity energy identities ... Uniqueness gives `v(-q,-η,s) = -v(q,η,s)`") and the classical
energy method for the difference of two solutions.

The target is `TrainCutoffEnergyIneq` (`Short/PartI/Sub/T05.lean`, line 170): two trains bounded by
`M` on `[0, S]` have a cutoff energy `F_R(s) = ∫_cell φ_R |v - v'|²` that is continuous on `[0, S]`
and satisfies `F_R(s) ≤ C ∫₀ˢ F_R + C/√R`, `C` independent of `R ≥ 1`.

## Mathematics (with `w = v - v'`, `π = p - p'`, `φ = φ_R = etaCutoff R`, `D = ∫_cell φ |∇w|²`)

`w_s + (v·∇)w + (w·∇)v' - νΔw + ∇π = 0`, `div w = 0`, `F_R(0) = 0`.  Differentiating under the
integral and using the equation,
`F_R'(s) = ∫_cell φ · 2⟨w, w_s⟩ = T_visc + T_trans + T_stretch + T_pres` with

* `T_visc = 2ν ∫ φ ⟨w, Δw⟩ = -2νD - 2ν ∫ φ' ⟨w, ∂_η w⟩`   (integration by parts, `φ = φ(η)`),
* `T_trans = -2 ∫ φ ⟨w, (v·∇)w⟩ = ∫ |w|² v_η φ'`   (`div v = 0`),
* `T_stretch = -2 ∫ φ ⟨w, (w·∇)v'⟩ = 2 ∫ φ' w_η ⟨w, v'⟩ + 2 ∫ φ ⟨(w·∇)w, v'⟩`   (`div w = 0`; only
  `‖v'‖_∞ ≤ M` is used, never `∇v'`),
* `T_pres = -2 ∫ φ ⟨w, ∇π⟩ = 2 ∫ φ' π w_η`   (`div w = 0`).

With `|φ'| ≤ (C₀/R) √φ` (`EtaCutoffFacts`), `‖v‖_∞, ‖p‖_∞ ≤ M`, `∫_cell |w|² ≤ 4M`:
`T_visc ≤ -(3/2)νD + K/R²`, `|T_trans| ≤ 4C₀M²/R`, `T_stretch ≤ (ν/2)D + (2M²/ν)F_R + 8C₀M²/R`,
`|T_pres| ≤ 4C₀M √(8cM)/√R` (Cauchy-Schwarz on the strip `R ≤ |η| ≤ 2R` of measure `2Rc`).
Hence `F_R' ≤ C F_R + C/√R` (the dissipation cancels: `-(3/2)ν + ν/2 < 0`), and `F_R(0) = 0` gives
the integrated form.

## What is proved here

`trainCutoffEnergyIneq_of` derives `TrainCutoffEnergyIneq` from eleven leaf statements:
`CutoffEnergyContinuous`, `CutoffEnergyHasDeriv`, `CutoffIntegrandDecomp` (the equation for `w`,
splitting `F_R'` into the four terms), and an identity/estimate pair for each term
(`ViscousIdentity`/`ViscousEstimate`, `TransportIdentity`/`TransportEstimate`,
`StretchIdentity`/`StretchEstimate`, `PressureIdentity`/`PressureEstimate`).  The assembly adds the
four estimates, discards `-νD ≤ 0`, and integrates the differential inequality
(`antitoneOn_of_deriv_nonpos` for `F - C∫F - (C/√R)s`).  The final constant is `C₁(S + 1)` because the
integrated inequality has the term `(C₁/√R) s ≤ (C₁(S+1))/√R`.

Four toolkit statements are shared by the leaves: `CellIntegrableOfSupport`, `CellDerivZero` (cell
integration by parts for cutoff-supported periodic `C¹` functions), `TrainSliceSmooth` and
`DiffEnergyBound`.

The unconditional target is task `PartI:T05b/2` (`Short/PartI/Tasks/TrainCutoffEnergyProof.lean`).
`EtaCutoffFacts` (`Sub/T02_3.lean`, line 125) is proved by task `PartI:T02/3/9`; the leaves take it
as a hypothesis.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-! ### Notation for the difference of two trains -/

/-- The velocity difference `w(s) = v(s) - v'(s)` at age `s`, as a field on the plane. -/
def diffV {ν c : ℝ} (tr tr' : B0140.TrainSol ν c) (s : ℝ) : Plane → Vec :=
  fun z => tr.v s z - tr'.v s z

/-- The pressure difference `π(s) = p(s) - p'(s)`. -/
def diffP {ν c : ℝ} (tr tr' : B0140.TrainSol ν c) (s : ℝ) : Plane → ℝ :=
  fun z => tr.p s z - tr'.p s z

/-- The transport `(a·∇) b = (a₁ ∂_q + a₂ ∂_η) b` of a vector field `b` by `a` (components `0 = q`,
`1 = η`); `Train.advection u = bilinAdv u u`. -/
def bilinAdv (a b : Plane → Vec) (z : Plane) : Vec :=
  Train.toVec (a z 0 * Cyl.partialQ (fun w => b w 0) z + a z 1 * Cyl.partialEta (fun w => b w 0) z,
    a z 0 * Cyl.partialQ (fun w => b w 1) z + a z 1 * Cyl.partialEta (fun w => b w 1) z)

/-- `|∇u|² = Σ_{i,k} (∂_k u_i)²`. -/
def gradNormSq (u : Plane → Vec) (z : Plane) : ℝ :=
  Cyl.partialQ (fun w => u w 0) z ^ 2 + Cyl.partialEta (fun w => u w 0) z ^ 2 +
    Cyl.partialQ (fun w => u w 1) z ^ 2 + Cyl.partialEta (fun w => u w 1) z ^ 2

/-- The cutoff dissipation `D(s) = ∫_cell φ_R |∇w|²`. -/
def cutoffDissipation {ν c : ℝ} (tr tr' : B0140.TrainSol ν c) (R s : ℝ) : ℝ :=
  ∫ z in Cyl.cell c, etaCutoff R z.2 * gradNormSq (diffV tr tr' s) z

/-- The viscous term `T_visc = 2ν ∫_cell φ_R ⟨w, Δw⟩`. -/
def cutoffViscous {ν c : ℝ} (tr tr' : B0140.TrainSol ν c) (R s : ℝ) : ℝ :=
  2 * ν * ∫ z in Cyl.cell c,
    etaCutoff R z.2 * inner ℝ (diffV tr tr' s z) (Train.vecLaplacian (diffV tr tr' s) z)

/-- The transport term `T_trans = -2 ∫_cell φ_R ⟨w, (v·∇)w⟩`. -/
def cutoffTransport {ν c : ℝ} (tr tr' : B0140.TrainSol ν c) (R s : ℝ) : ℝ :=
  -2 * ∫ z in Cyl.cell c,
    etaCutoff R z.2 * inner ℝ (diffV tr tr' s z) (bilinAdv (tr.v s) (diffV tr tr' s) z)

/-- The stretching term `T_stretch = -2 ∫_cell φ_R ⟨w, (w·∇)v'⟩`. -/
def cutoffStretch {ν c : ℝ} (tr tr' : B0140.TrainSol ν c) (R s : ℝ) : ℝ :=
  -2 * ∫ z in Cyl.cell c,
    etaCutoff R z.2 * inner ℝ (diffV tr tr' s z) (bilinAdv (diffV tr tr' s) (tr'.v s) z)

/-- The pressure term `T_pres = -2 ∫_cell φ_R ⟨w, ∇π⟩`. -/
def cutoffPressure {ν c : ℝ} (tr tr' : B0140.TrainSol ν c) (R s : ℝ) : ℝ :=
  -2 * ∫ z in Cyl.cell c,
    etaCutoff R z.2 * inner ℝ (diffV tr tr' s z) (Train.gradS (diffP tr tr' s) z)

/-- The cutoff is nonnegative. -/
theorem etaCutoff_nonneg (R η : ℝ) : 0 ≤ etaCutoff R η := by
  unfold etaCutoff
  positivity

/-- `gradNormSq` is nonnegative. -/
theorem gradNormSq_nonneg (u : Plane → Vec) (z : Plane) : 0 ≤ gradNormSq u z := by
  unfold gradNormSq
  positivity

theorem cutoffDissipation_nonneg {ν c : ℝ} (tr tr' : B0140.TrainSol ν c) (R s : ℝ) :
    0 ≤ cutoffDissipation tr tr' R s :=
  integral_nonneg (fun z => mul_nonneg (etaCutoff_nonneg R z.2) (gradNormSq_nonneg _ z))

theorem cutoffEnergy_nonneg {ν c : ℝ} (tr tr' : B0140.TrainSol ν c) (R s : ℝ) :
    0 ≤ cutoffEnergy tr tr' R s :=
  integral_nonneg (fun z => mul_nonneg (etaCutoff_nonneg R z.2) (sq_nonneg _))

/-- Equal initial data give `F_R(0) = 0`. -/
theorem cutoffEnergy_zero {ν c : ℝ} (tr tr' : B0140.TrainSol ν c) (R : ℝ) :
    cutoffEnergy tr tr' R 0 = 0 := by
  simp [cutoffEnergy, tr.isTrain.initial, tr'.isTrain.initial]

/-! ### Toolkit leaves -/

/-- **Toolkit `CellIntegrableOfSupport`**: a continuous function that vanishes for `|η| ≥ 2R` is
integrable on the cell (it is supported in the compact `[-c/2, c/2] × [-2R, 2R]`). -/
def CellIntegrableOfSupport : Prop :=
  ∀ (c R : ℝ), 0 < c → 0 < R → ∀ g : Plane → ℝ, Continuous g →
    (∀ z : Plane, 2 * R ≤ |z.2| → g z = 0) → IntegrableOn g (Cyl.cell c)

/-- **Toolkit `CellDerivZero`** (cell integration by parts): for a `C¹` function `G` that is
`c`-periodic in `q` and vanishes for `|η| ≥ 2R`, `∫_cell ∂_q G = 0 = ∫_cell ∂_η G`
(`Cyl.integral_cell_deriv_q_of_periodic`, `Cyl.integral_cell_deriv_eta` in `Lib/Cylinder/IBP.lean`). -/
def CellDerivZero : Prop :=
  ∀ (c R : ℝ), 0 < c → 0 < R → ∀ G : Plane → ℝ, ContDiff ℝ 1 G → Cyl.IsPeriodic c G →
    (∀ z : Plane, 2 * R ≤ |z.2| → G z = 0) →
      ∫ z in Cyl.cell c, Cyl.partialQ G z = 0 ∧ ∫ z in Cyl.cell c, Cyl.partialEta G z = 0

/-- **Toolkit `TrainSliceSmooth`**: for `s ≥ 0` the slices `v(s)` and `p(s)` of a train are
`C^∞` on the plane (composition of `smooth_v`, `smooth_p` on `Ici 0 ×ˢ univ` with `z ↦ (s, z)`). -/
def TrainSliceSmooth : Prop :=
  ∀ (ν c : ℝ) (tr : B0140.TrainSol ν c) (s : ℝ), 0 ≤ s →
    ContDiff ℝ ∞ (tr.v s) ∧ ContDiff ℝ ∞ (tr.p s)

/-- **Toolkit `DiffEnergyBound`**: for trains bounded by `M` on `[0, S]`, the difference has finite
cell energy `≤ 4M` at every `s ∈ [0, S]` (`|a - b|² ≤ 2|a|² + 2|b|²`). -/
def DiffEnergyBound : Prop :=
  ∀ (ν c : ℝ), 0 < c → ∀ tr tr' : B0140.TrainSol ν c, ∀ S M : ℝ,
    TrainBoundedBy tr S M → TrainBoundedBy tr' S M → ∀ s ∈ Icc (0 : ℝ) S,
      IntegrableOn (fun z => ‖diffV tr tr' s z‖ ^ 2) (Cyl.cell c) ∧
        ∫ z in Cyl.cell c, ‖diffV tr tr' s z‖ ^ 2 ≤ 4 * M

/-! ### The cutoff energy: continuity, derivative, splitting -/

/-- **Leaf `CutoffEnergyContinuous`**: `F_R` is continuous on `[0, S]` (the integrand is continuous
in `(s, z)` on `[0, S] × ℝ²` and supported in the compact set `[-c/2, c/2] × [-2R, 2R]`). -/
def CutoffEnergyContinuous : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr tr' : B0140.TrainSol ν c, ∀ R : ℝ, 1 ≤ R → ∀ S : ℝ,
    ContinuousOn (cutoffEnergy tr tr' R) (Icc 0 S)

/-- **Leaf `CutoffEnergyHasDeriv`** (differentiation under the integral sign): for `s > 0`,
`F_R'(s) = ∫_cell φ_R · 2⟨w, ∂_s w⟩`. -/
def CutoffEnergyHasDeriv : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr tr' : B0140.TrainSol ν c, ∀ R : ℝ, 1 ≤ R → ∀ s : ℝ, 0 < s →
    HasDerivAt (cutoffEnergy tr tr' R)
      (∫ z in Cyl.cell c, etaCutoff R z.2 *
        (2 * inner ℝ (diffV tr tr' s z) (deriv (fun t => diffV tr tr' t z) s))) s

/-- **Leaf `CutoffIntegrandDecomp`** (the equation for `w`): for `s > 0`, by the momentum equations of
both trains, `∂_s w = -(v·∇)w - (w·∇)v' + νΔw - ∇π`, so the integral `∫_cell φ_R · 2⟨w, ∂_s w⟩`
is the sum of the four terms (all integrands are continuous with support in `|η| ≤ 2R`). -/
def CutoffIntegrandDecomp : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr tr' : B0140.TrainSol ν c, ∀ R : ℝ, 1 ≤ R → ∀ s : ℝ, 0 < s →
    (∫ z in Cyl.cell c, etaCutoff R z.2 *
        (2 * inner ℝ (diffV tr tr' s z) (deriv (fun t => diffV tr tr' t z) s))) =
      cutoffViscous tr tr' R s + cutoffTransport tr tr' R s + cutoffStretch tr tr' R s +
        cutoffPressure tr tr' R s

/-! ### Identity / estimate pairs for the four terms -/

/-- Right side of the viscous identity: `-2νD - 2ν ∫ φ' ⟨w, ∂_η w⟩`. -/
def viscousRhs {ν c : ℝ} (tr tr' : B0140.TrainSol ν c) (R s : ℝ) : ℝ :=
  -2 * ν * cutoffDissipation tr tr' R s - 2 * ν * ∫ z in Cyl.cell c,
    deriv (etaCutoff R) z.2 * inner ℝ (diffV tr tr' s z) (Cyl.partialEta (diffV tr tr' s) z)

/-- Right side of the transport identity: `∫ |w|² v_η φ'`. -/
def transportRhs {ν c : ℝ} (tr tr' : B0140.TrainSol ν c) (R s : ℝ) : ℝ :=
  ∫ z in Cyl.cell c, ‖diffV tr tr' s z‖ ^ 2 * tr.v s z 1 * deriv (etaCutoff R) z.2

/-- Right side of the stretching identity: `2 ∫ φ' w_η ⟨w, v'⟩ + 2 ∫ φ ⟨(w·∇)w, v'⟩`. -/
def stretchRhs {ν c : ℝ} (tr tr' : B0140.TrainSol ν c) (R s : ℝ) : ℝ :=
  2 * (∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * diffV tr tr' s z 1 *
      inner ℝ (diffV tr tr' s z) (tr'.v s z)) +
    2 * ∫ z in Cyl.cell c, etaCutoff R z.2 *
      inner ℝ (bilinAdv (diffV tr tr' s) (diffV tr tr' s) z) (tr'.v s z)

/-- Right side of the pressure identity: `2 ∫ φ' π w_η`. -/
def pressureRhs {ν c : ℝ} (tr tr' : B0140.TrainSol ν c) (R s : ℝ) : ℝ :=
  2 * ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * diffP tr tr' s z * diffV tr tr' s z 1

/-- **Leaf `ViscousIdentity`**: `T_visc = -2νD - 2ν ∫ φ' ⟨w, ∂_η w⟩` (cell integration by parts of
`φ w_i (∂_q² + ∂_η²) w_i` for each component; `φ` depends on `η` only). -/
def ViscousIdentity : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr tr' : B0140.TrainSol ν c, ∀ R : ℝ, 1 ≤ R → ∀ s : ℝ, 0 ≤ s →
    cutoffViscous tr tr' R s = viscousRhs tr tr' R s

/-- **Leaf `ViscousEstimate`**: with `|φ'| ≤ (C₀/R)√φ`, Young's inequality
`2ν|φ'||w||∂_η w| ≤ (ν/2) φ|∂_η w|² + 2ν(C₀/R)²|w|²` and `∫_cell |w|² ≤ 4M`:
`viscousRhs ≤ -(3/2)νD + K/√R` (in fact `K/R²`). -/
def ViscousEstimate : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr tr' : B0140.TrainSol ν c, ∀ S M : ℝ, 0 ≤ S →
    TrainBoundedBy tr S M → TrainBoundedBy tr' S M →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Icc (0 : ℝ) S,
      viscousRhs tr tr' R s ≤ -(3 / 2) * ν * cutoffDissipation tr tr' R s + K / Real.sqrt R

/-- **Leaf `TransportIdentity`**: `T_trans = ∫ |w|² v_η φ'` (`-2⟨w, (v·∇)w⟩ = -v·∇|w|²`, then
`∫ |w|² ∂_j(φ v_j) = ∫ |w|² φ' v_η` since `div v = 0`). -/
def TransportIdentity : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr tr' : B0140.TrainSol ν c, ∀ R : ℝ, 1 ≤ R → ∀ s : ℝ, 0 ≤ s →
    cutoffTransport tr tr' R s = transportRhs tr tr' R s

/-- **Leaf `TransportEstimate`**: `|v_η| ≤ M`, `|φ'| ≤ C₀/R`, `∫_cell |w|² ≤ 4M` give
`transportRhs ≤ K/√R` (in fact `4C₀M²/R`). -/
def TransportEstimate : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr tr' : B0140.TrainSol ν c, ∀ S M : ℝ, 0 ≤ S →
    TrainBoundedBy tr S M → TrainBoundedBy tr' S M →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Icc (0 : ℝ) S,
      transportRhs tr tr' R s ≤ K / Real.sqrt R

/-- **Leaf `StretchIdentity`**: `T_stretch = 2 ∫ φ' w_η ⟨w, v'⟩ + 2 ∫ φ ⟨(w·∇)w, v'⟩` (integrate
`φ w_i w_j ∂_j v'_i` by parts in `j`; the term `φ w_i (∂_j w_j) v'_i` vanishes since `div w = 0`;
no derivative of `v'` remains). -/
def StretchIdentity : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr tr' : B0140.TrainSol ν c, ∀ R : ℝ, 1 ≤ R → ∀ s : ℝ, 0 ≤ s →
    cutoffStretch tr tr' R s = stretchRhs tr tr' R s

/-- **Leaf `StretchEstimate`**: `|(w·∇)w|² ≤ |w|² |∇w|²`, `|v'| ≤ M`, Young
`2M√φ|w| √φ|∇w| ≤ (ν/2) φ|∇w|² + (2M²/ν) φ|w|²`, and `|φ'| ≤ C₀/R`, `∫|w|² ≤ 4M`:
`stretchRhs ≤ (ν/2) D + K F_R + K/√R`. -/
def StretchEstimate : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr tr' : B0140.TrainSol ν c, ∀ S M : ℝ, 0 ≤ S →
    TrainBoundedBy tr S M → TrainBoundedBy tr' S M →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Icc (0 : ℝ) S,
      stretchRhs tr tr' R s ≤
        (ν / 2) * cutoffDissipation tr tr' R s + K * cutoffEnergy tr tr' R s + K / Real.sqrt R

/-- **Leaf `PressureIdentity`**: `T_pres = 2 ∫ φ' π w_η` (`-2φ ⟨w, ∇π⟩ = -2 div(φ π w) + 2π ⟨w, ∇φ⟩`
since `div w = 0`; cell integration by parts in `q` and `η`). -/
def PressureIdentity : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr tr' : B0140.TrainSol ν c, ∀ R : ℝ, 1 ≤ R → ∀ s : ℝ, 0 ≤ s →
    cutoffPressure tr tr' R s = pressureRhs tr tr' R s

/-- **Leaf `PressureEstimate`**: `|π| ≤ 2M`, `|φ'| ≤ (C₀/R) 1_{R ≤ |η| ≤ 2R}`, Cauchy-Schwarz on the
strip `{R ≤ |η| ≤ 2R} ∩ cell` of measure `2Rc` and `∫_cell |w|² ≤ 4M`:
`pressureRhs ≤ K/√R` with `K = 4C₀M √(8cM)`. -/
def PressureEstimate : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr tr' : B0140.TrainSol ν c, ∀ S M : ℝ, 0 ≤ S →
    TrainBoundedBy tr S M → TrainBoundedBy tr' S M →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Icc (0 : ℝ) S,
      pressureRhs tr tr' R s ≤ K / Real.sqrt R

/-! ### The conditional theorem -/

/-- **`PartI:T05b/2`, conditional form**: `TrainCutoffEnergyIneq` from the eleven leaves. -/
theorem trainCutoffEnergyIneq_of (hC : CutoffEnergyContinuous) (hD : CutoffEnergyHasDeriv)
    (hE : CutoffIntegrandDecomp) (hVi : ViscousIdentity) (hVe : ViscousEstimate)
    (hTi : TransportIdentity) (hTe : TransportEstimate) (hSi : StretchIdentity)
    (hSe : StretchEstimate) (hPi : PressureIdentity) (hPe : PressureEstimate) :
    TrainCutoffEnergyIneq := by
  intro ν c hν hc tr tr' S M hS0 hb hb'
  obtain ⟨KV, hKV, HV⟩ := hVe ν c hν hc tr tr' S M hS0 hb hb'
  obtain ⟨KT, hKT, HT⟩ := hTe ν c hν hc tr tr' S M hS0 hb hb'
  obtain ⟨KS, hKS, HS⟩ := hSe ν c hν hc tr tr' S M hS0 hb hb'
  obtain ⟨KP, hKP, HP⟩ := hPe ν c hν hc tr tr' S M hS0 hb hb'
  set C₁ : ℝ := KV + KT + KS + KP with hC₁
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; linarith
  refine ⟨C₁ * (S + 1), mul_nonneg hC₁0 (by linarith), ?_⟩
  intro R hR
  have hRpos : 0 < R := by linarith
  have hsq : 0 < Real.sqrt R := Real.sqrt_pos.2 hRpos
  have hcont : ContinuousOn (cutoffEnergy tr tr' R) (Icc 0 S) := hC ν c hν hc tr tr' R hR S
  refine ⟨hcont, ?_⟩
  intro s hs
  -- the pointwise differential inequality
  have hbound : ∀ r ∈ Ioc (0 : ℝ) S,
      (∫ z in Cyl.cell c, etaCutoff R z.2 *
          (2 * inner ℝ (diffV tr tr' r z) (deriv (fun t => diffV tr tr' t z) r))) ≤
        C₁ * cutoffEnergy tr tr' R r + C₁ / Real.sqrt R := by
    intro r hr
    have hr' : r ∈ Icc (0 : ℝ) S := ⟨hr.1.le, hr.2⟩
    rw [hE ν c hν hc tr tr' R hR r hr.1, hVi ν c hν hc tr tr' R hR r hr.1.le,
      hTi ν c hν hc tr tr' R hR r hr.1.le, hSi ν c hν hc tr tr' R hR r hr.1.le,
      hPi ν c hν hc tr tr' R hR r hr.1.le]
    have h1 := HV R hR r hr'
    have h2 := HT R hR r hr'
    have h3 := HS R hR r hr'
    have h4 := HP R hR r hr'
    have hD0 := cutoffDissipation_nonneg tr tr' R r
    have hF0 := cutoffEnergy_nonneg tr tr' R r
    have hνD : 0 ≤ ν * cutoffDissipation tr tr' R r := mul_nonneg hν.le hD0
    have hKF : KS * cutoffEnergy tr tr' R r ≤ C₁ * cutoffEnergy tr tr' R r :=
      mul_le_mul_of_nonneg_right (by rw [hC₁]; linarith) hF0
    have hsum : KV / Real.sqrt R + KT / Real.sqrt R + KS / Real.sqrt R + KP / Real.sqrt R =
        C₁ / Real.sqrt R := by rw [hC₁]; ring
    linarith
  -- integrate
  set Fn : ℝ → ℝ := cutoffEnergy tr tr' R with hFn
  have hFint : IntervalIntegrable Fn volume 0 S := hcont.intervalIntegrable_of_Icc hS0
  have hprim : ContinuousOn (fun r => ∫ x in (0 : ℝ)..r, Fn x) (Icc 0 S) := by
    have h := intervalIntegral.continuousOn_primitive_interval' hFint
      (show (0 : ℝ) ∈ Set.uIcc 0 S from Set.left_mem_uIcc)
    rwa [Set.uIcc_of_le hS0] at h
  set H : ℝ → ℝ := fun r =>
    Fn r - (C₁ * (∫ x in (0 : ℝ)..r, Fn x) + C₁ / Real.sqrt R * r) with hH
  have hHcont : ContinuousOn H (Icc 0 S) :=
    hcont.sub ((continuousOn_const.mul hprim).add (continuousOn_const.mul continuousOn_id))
  have hHder : ∀ r ∈ Ioo (0 : ℝ) S, HasDerivAt H
      ((∫ z in Cyl.cell c, etaCutoff R z.2 *
          (2 * inner ℝ (diffV tr tr' r z) (deriv (fun t => diffV tr tr' t z) r))) -
        (C₁ * Fn r + C₁ / Real.sqrt R)) r := by
    intro r hr
    have hI := hD ν c hν hc tr tr' R hR r hr.1
    have hcr : ContinuousAt Fn r := hcont.continuousAt (Icc_mem_nhds hr.1 hr.2)
    have hmeas : StronglyMeasurableAtFilter Fn (𝓝 r) volume :=
      (hcont.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo r hr
    have hFr : IntervalIntegrable Fn volume 0 r :=
      hFint.mono_set (by
        rw [Set.uIcc_of_le hS0, Set.uIcc_of_le hr.1.le]
        exact Icc_subset_Icc_right hr.2.le)
    have hP : HasDerivAt (fun u => ∫ x in (0 : ℝ)..u, Fn x) (Fn r) r :=
      intervalIntegral.integral_hasDerivAt_right hFr hmeas hcr
    have hG : HasDerivAt (fun u => C₁ * (∫ x in (0 : ℝ)..u, Fn x) + C₁ / Real.sqrt R * u)
        (C₁ * Fn r + C₁ / Real.sqrt R) r := by
      have h := (hP.const_mul C₁).add ((hasDerivAt_id' r).const_mul (C₁ / Real.sqrt R))
      rwa [mul_one] at h
    exact hI.sub hG
  have hanti : AntitoneOn H (Icc 0 S) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 S) hHcont
    · intro r hr
      rw [interior_Icc] at hr
      exact (hHder r hr).differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      rw [(hHder r hr).deriv]
      have := hbound r ⟨hr.1, hr.2.le⟩
      linarith
  have hH0 : H 0 = 0 := by
    simp [hH, hFn, cutoffEnergy_zero]
  have hle : H s ≤ H 0 := hanti ⟨le_rfl, hS0⟩ hs hs.1
  have hint0 : 0 ≤ ∫ x in (0 : ℝ)..s, Fn x :=
    intervalIntegral.integral_nonneg hs.1 (fun x _ => cutoffEnergy_nonneg tr tr' R x)
  have h1 : Fn s ≤ C₁ * (∫ x in (0 : ℝ)..s, Fn x) + C₁ / Real.sqrt R * s := by
    have : H s ≤ 0 := hH0 ▸ hle
    simp only [hH] at this
    linarith
  have h2 : C₁ * (∫ x in (0 : ℝ)..s, Fn x) ≤ C₁ * (S + 1) * (∫ x in (0 : ℝ)..s, Fn x) := by
    apply mul_le_mul_of_nonneg_right _ hint0
    nlinarith [hS0]
  have h3 : C₁ / Real.sqrt R * s ≤ C₁ * (S + 1) / Real.sqrt R := by
    have : C₁ * s ≤ C₁ * (S + 1) := mul_le_mul_of_nonneg_left (by linarith [hs.2]) hC₁0
    calc C₁ / Real.sqrt R * s = (C₁ * s) / Real.sqrt R := by ring
      _ ≤ C₁ * (S + 1) / Real.sqrt R := div_le_div_of_nonneg_right this hsq.le
  show Fn s ≤ C₁ * (S + 1) * (∫ r in (0 : ℝ)..s, Fn r) + C₁ * (S + 1) / Real.sqrt R
  linarith

end UnforcedLeray.Short.PartI
