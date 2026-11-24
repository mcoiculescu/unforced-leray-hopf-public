import UnforcedLeray.Short.PartI.Sub.T05b_2

/-!
# Part I, task `PartI:T02/3/11`: `ClassicalCutoffEnergyIneq` (conditional decomposition)

Source of record: `the November 2 reference manuscript`, lines 276-288 ("Approximation
and transverse cutoffs then give the velocity and vorticity energy identities ... Uniqueness gives
`v(-q,-eta,s) = -v(q,eta,s)`") and the classical energy method for the difference of two solutions.

The target is `ClassicalCutoffEnergyIneq` (`Short/PartI/Sub/T02_3.lean`, line 195): two classical
solutions `(v, p)`, `(v', p')` on `[0, T]` with bounded derivatives and the uniform bounds
`ClassicalBoundedBy c T M` have a cutoff energy `F_R(s) = ∫_cell φ_R |v - v'|²` that is continuous on
`[0, T]` and satisfies `F_R(s) ≤ C ∫₀ˢ F_R + C/√R`, `C` independent of `R ≥ 1`.

## Mathematics (with `w = v - v'`, `π = p - p'`, `φ = φ_R = etaCutoff R`, `D = ∫_cell φ |∇w|²`)

`w_s + (v·∇)w + (w·∇)v' - νΔw + ∇π = 0`, `div w = 0`, `F_R(0) = 0` (both data equal `trainDatum c`).
Differentiating under the integral and using the equation, for `s ∈ (0, T)`,
`F_R'(s) = ∫_cell φ · 2⟨w, w_s⟩ = T_visc + T_trans + T_stretch + T_pres` with

* `T_visc = 2ν ∫ φ ⟨w, Δw⟩ = -2νD - 2ν ∫ φ' ⟨w, ∂_η w⟩`   (integration by parts, `φ = φ(η)`),
* `T_trans = -2 ∫ φ ⟨w, (v·∇)w⟩ = ∫ |w|² v_η φ'`   (`div v = 0`),
* `T_stretch = -2 ∫ φ ⟨w, (w·∇)v'⟩`, bounded directly by `2 K F_R` where `K = 4 sup |∇v'|`
  (`HasBoundedDerivsOn T v'`, order `1`; this is the one place where the classical class differs from
  the train class, where only `‖v'‖_∞ ≤ M` is available),
* `T_pres = -2 ∫ φ ⟨w, ∇π⟩ = 2 ∫ φ' π w_η`   (`div w = 0`).

With `|φ'| ≤ (C₀/R) √φ` (`EtaCutoffFacts`), `‖v‖_∞, ‖p‖_∞ ≤ M` and `∫_cell |w|² ≤ 4M`:
`T_visc ≤ -(3/2)νD + K/R²`, `|T_trans| ≤ 4C₀M²/R`, `|T_pres| ≤ 4C₀M √(8cM)/√R` (Cauchy-Schwarz on the
strip `R ≤ |η| ≤ 2R` of measure `2Rc`).  Hence `F_R' ≤ C F_R + C/√R` on `(0, T)`, and `F_R(0) = 0`
gives the integrated form (the dissipation `-(3/2)νD ≤ 0` is dropped).

## What is proved here

`classicalCutoffEnergyIneq_of` derives `ClassicalCutoffEnergyIneq` from ten leaf statements:
`CcEnergyContinuous`, `CcEnergyHasDeriv`, `CcIntegrandDecomp` (the equation for `w`, splitting `F_R'`
into the four terms), an identity/estimate pair for the viscous, transport and pressure terms, and a
direct estimate `CcStretchEstimate` for the stretching term.  The assembly adds the estimates, discards
`-(3/2)νD ≤ 0`, and integrates the differential inequality (`antitoneOn_of_deriv_nonpos` for
`F - C∫F - (C/√R)s`, as in `trainCutoffEnergyIneq_of`, `Sub/T05b_2.lean`).  The final constant is
`C₁(T + 1)`.

Four auxiliary statements are shared by the proofs of the leaves: `CcSliceSmooth`,
`CcDiffEnergyBound`, `CcStretchPointwise` and `CcDiffMomentum`.  The cell toolkit
`CellIntegrableOfSupport`, `CellDerivZero` (`Sub/T05b_2.lean`) is proved by `cellToolkit`
(`Tasks/TrainCutoffEnergyProof/CellToolkit.lean`), and `EtaCutoffFacts` by `etaCutoffFacts` (task
`PartI:T02/3/9`); the leaves take them as hypotheses.  The leaves are the classical-solution analogues
of the proved leaves of `Tasks/TrainCutoffEnergyProof/*.lean`.

The unconditional target is task `PartI:T02/3/11`
(`Short/PartI/Tasks/ClassicalOdd/ClassicalCutoffEnergyIneq.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-! ### Hypotheses and notation for the difference of two classical solutions -/

/-- The hypotheses of `ClassicalCutoffEnergyIneq`, bundled: two classical solutions of the same
system on `[0, T]` with bounded derivatives and the uniform bounds `ClassicalBoundedBy` by `M`. -/
structure CcPair (ν c T M : ℝ) (v v' : ℝ → Plane → Vec) (p p' : ℝ → Plane → ℝ) : Prop where
  nu_pos : 0 < ν
  c_ge : 1 ≤ c
  T_pos : 0 < T
  cl : IsClassicalOn ν c T v p
  cl' : IsClassicalOn ν c T v' p'
  bd : HasBoundedDerivsOn T v
  bd' : HasBoundedDerivsOn T v'
  bb : ClassicalBoundedBy c T M v p
  bb' : ClassicalBoundedBy c T M v' p'

/-- The velocity difference `w(s) = v(s) - v'(s)` at time `s`, as a field on the plane. -/
def ccDiffV (v v' : ℝ → Plane → Vec) (s : ℝ) : Plane → Vec :=
  fun z => v s z - v' s z

/-- The pressure difference `π(s) = p(s) - p'(s)`. -/
def ccDiffP (p p' : ℝ → Plane → ℝ) (s : ℝ) : Plane → ℝ :=
  fun z => p s z - p' s z

/-- The cutoff dissipation `D(s) = ∫_cell φ_R |∇w|²`. -/
def ccDissipation (c : ℝ) (v v' : ℝ → Plane → Vec) (R s : ℝ) : ℝ :=
  ∫ z in Cyl.cell c, etaCutoff R z.2 * gradNormSq (ccDiffV v v' s) z

/-- The time-derivative integral `∫_cell φ_R · 2⟨w, ∂_s w⟩` (the derivative of `F_R` on `(0, T)`). -/
def ccDt (c : ℝ) (v v' : ℝ → Plane → Vec) (R s : ℝ) : ℝ :=
  ∫ z in Cyl.cell c, etaCutoff R z.2 *
    (2 * inner ℝ (ccDiffV v v' s z) (deriv (fun t => ccDiffV v v' t z) s))

/-- The viscous term `T_visc = 2ν ∫_cell φ_R ⟨w, Δw⟩`. -/
def ccViscous (ν c : ℝ) (v v' : ℝ → Plane → Vec) (R s : ℝ) : ℝ :=
  2 * ν * ∫ z in Cyl.cell c,
    etaCutoff R z.2 * inner ℝ (ccDiffV v v' s z) (Train.vecLaplacian (ccDiffV v v' s) z)

/-- The transport term `T_trans = -2 ∫_cell φ_R ⟨w, (v·∇)w⟩`. -/
def ccTransport (c : ℝ) (v v' : ℝ → Plane → Vec) (R s : ℝ) : ℝ :=
  -2 * ∫ z in Cyl.cell c,
    etaCutoff R z.2 * inner ℝ (ccDiffV v v' s z) (bilinAdv (v s) (ccDiffV v v' s) z)

/-- The stretching term `T_stretch = -2 ∫_cell φ_R ⟨w, (w·∇)v'⟩`. -/
def ccStretch (c : ℝ) (v v' : ℝ → Plane → Vec) (R s : ℝ) : ℝ :=
  -2 * ∫ z in Cyl.cell c,
    etaCutoff R z.2 * inner ℝ (ccDiffV v v' s z) (bilinAdv (ccDiffV v v' s) (v' s) z)

/-- The pressure term `T_pres = -2 ∫_cell φ_R ⟨w, ∇π⟩`. -/
def ccPressure (c : ℝ) (v v' : ℝ → Plane → Vec) (p p' : ℝ → Plane → ℝ) (R s : ℝ) : ℝ :=
  -2 * ∫ z in Cyl.cell c,
    etaCutoff R z.2 * inner ℝ (ccDiffV v v' s z) (Train.gradS (ccDiffP p p' s) z)

/-- Right side of the viscous identity: `-2νD - 2ν ∫ φ' ⟨w, ∂_η w⟩`. -/
def ccViscousRhs (ν c : ℝ) (v v' : ℝ → Plane → Vec) (R s : ℝ) : ℝ :=
  -2 * ν * ccDissipation c v v' R s - 2 * ν * ∫ z in Cyl.cell c,
    deriv (etaCutoff R) z.2 * inner ℝ (ccDiffV v v' s z) (Cyl.partialEta (ccDiffV v v' s) z)

/-- Right side of the transport identity: `∫ |w|² v_η φ'`. -/
def ccTransportRhs (c : ℝ) (v v' : ℝ → Plane → Vec) (R s : ℝ) : ℝ :=
  ∫ z in Cyl.cell c, ‖ccDiffV v v' s z‖ ^ 2 * v s z 1 * deriv (etaCutoff R) z.2

/-- Right side of the pressure identity: `2 ∫ φ' π w_η`. -/
def ccPressureRhs (c : ℝ) (v v' : ℝ → Plane → Vec) (p p' : ℝ → Plane → ℝ) (R s : ℝ) : ℝ :=
  2 * ∫ z in Cyl.cell c,
    deriv (etaCutoff R) z.2 * ccDiffP p p' s z * ccDiffV v v' s z 1

theorem ccDissipation_nonneg (c : ℝ) (v v' : ℝ → Plane → Vec) (R s : ℝ) :
    0 ≤ ccDissipation c v v' R s :=
  integral_nonneg (fun z => mul_nonneg (etaCutoff_nonneg R z.2) (gradNormSq_nonneg _ z))

theorem classicalCutoffEnergy_nonneg (c : ℝ) (v v' : ℝ → Plane → Vec) (R s : ℝ) :
    0 ≤ classicalCutoffEnergy c v v' R s :=
  integral_nonneg (fun z => mul_nonneg (etaCutoff_nonneg R z.2) (sq_nonneg _))

/-- Equal initial data give `F_R(0) = 0`. -/
theorem classicalCutoffEnergy_zero {ν c T M : ℝ} {v v' : ℝ → Plane → Vec}
    {p p' : ℝ → Plane → ℝ} (h : CcPair ν c T M v v' p p') (R : ℝ) :
    classicalCutoffEnergy c v v' R 0 = 0 := by
  simp [classicalCutoffEnergy, h.cl.initial, h.cl'.initial]

/-! ### Auxiliary statements shared by the proofs of the leaves -/

/-- **Auxiliary `CcSliceSmooth`**: for `s ∈ [0, T]` the slices `v(s)` and `p(s)` of a classical
solution are `C^∞` on the plane (compose `smooth_v`, `smooth_p` on `Icc 0 T ×ˢ univ` with
`z ↦ (s, z)`; train analogue `trainSliceSmooth`, `Tasks/TrainCutoffEnergyProof/SliceSmooth.lean`). -/
def CcSliceSmooth : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), IsClassicalOn ν c T v p →
    ∀ s ∈ Icc (0 : ℝ) T, ContDiff ℝ ∞ (v s) ∧ ContDiff ℝ ∞ (p s)

/-- **Auxiliary `CcDiffEnergyBound`**: the difference of two solutions bounded by `M` has finite cell
energy `≤ 4M` at every `s ∈ [0, T]` (`|a - b|² ≤ 2|a|² + 2|b|²`, `finite_energy`,
`ClassicalBoundedBy`). -/
def CcDiffEnergyBound : Prop :=
  ∀ (ν c T M : ℝ) (v v' : ℝ → Plane → Vec) (p p' : ℝ → Plane → ℝ), CcPair ν c T M v v' p p' →
    ∀ s ∈ Icc (0 : ℝ) T, IntegrableOn (fun z => ‖ccDiffV v v' s z‖ ^ 2) (Cyl.cell c) ∧
      ∫ z in Cyl.cell c, ‖ccDiffV v v' s z‖ ^ 2 ≤ 4 * M

/-- **Auxiliary `CcStretchPointwise`**: the stretching field is pointwise bounded by the size of `w`:
there is `K ≥ 0` with `‖(w·∇)v'‖ ≤ K ‖w‖` on `[0, T] × ℝ²`.  (`HasBoundedDerivsOn T v'` at order `1`
bounds the four partials of `v'` by a constant `B`, via `Cyl.partialQ_eq_fderiv`,
`Cyl.partialEta_eq_fderiv` and `norm_iteratedFDeriv_one`; each component of `(w·∇)v'` is bounded by
`2 B ‖w‖`; take `K = 4B`.  Pattern: `cpS_partialQ_coord`, `cpS_coord_le` in
`Tasks/ClassicalOdd/CylinderPoissonBound/SourceBound.lean`.) -/
def CcStretchPointwise : Prop :=
  ∀ (ν c T M : ℝ) (v v' : ℝ → Plane → Vec) (p p' : ℝ → Plane → ℝ), CcPair ν c T M v v' p p' →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc (0 : ℝ) T, ∀ z : Plane,
      ‖bilinAdv (ccDiffV v v' s) (v' s) z‖ ≤ K * ‖ccDiffV v v' s z‖

/-- **Auxiliary `CcDiffMomentum`** (the equation for `w`): for `s ∈ (0, T)` and every `z`,
`∂_s w = -(v·∇)w - (w·∇)v' + νΔw - ∇π`.  (Subtract the two momentum equations
`Train.momentumResidual ν v p s z = 0`, `Train.momentumResidual ν v' p' s z = 0`; the slices are `C^∞`,
so `deriv`, `vecLaplacian`, `gradS` are linear on differences, and
`advection v - advection v' = bilinAdv v w + bilinAdv w v'` because `advection u = bilinAdv u u`.) -/
def CcDiffMomentum : Prop :=
  ∀ (ν c T M : ℝ) (v v' : ℝ → Plane → Vec) (p p' : ℝ → Plane → ℝ), CcPair ν c T M v v' p p' →
    ∀ s ∈ Ioo (0 : ℝ) T, ∀ z : Plane,
      deriv (fun t => ccDiffV v v' t z) s =
        -(bilinAdv (v s) (ccDiffV v v' s) z) - bilinAdv (ccDiffV v v' s) (v' s) z +
          ν • Train.vecLaplacian (ccDiffV v v' s) z - Train.gradS (ccDiffP p p' s) z

/-! ### The cutoff energy: continuity, derivative, splitting -/

/-- **Leaf `CcEnergyContinuous`**: `F_R` is continuous on `[0, T]` (the integrand is jointly continuous
in `(s, z)` on `[0, T] × ℝ²` and supported in the compact set `[-c/2, c/2] × [-2R, 2R]`). -/
def CcEnergyContinuous : Prop :=
  ∀ (ν c T M : ℝ) (v v' : ℝ → Plane → Vec) (p p' : ℝ → Plane → ℝ), CcPair ν c T M v v' p p' →
    ∀ R : ℝ, 1 ≤ R → ContinuousOn (classicalCutoffEnergy c v v' R) (Icc 0 T)

/-- **Leaf `CcEnergyHasDeriv`** (differentiation under the integral sign): for `s ∈ (0, T)`,
`F_R'(s) = ∫_cell φ_R · 2⟨w, ∂_s w⟩`. -/
def CcEnergyHasDeriv : Prop :=
  ∀ (ν c T M : ℝ) (v v' : ℝ → Plane → Vec) (p p' : ℝ → Plane → ℝ), CcPair ν c T M v v' p p' →
    ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Ioo (0 : ℝ) T,
      HasDerivAt (classicalCutoffEnergy c v v' R) (ccDt c v v' R s) s

/-- **Leaf `CcIntegrandDecomp`**: for `s ∈ (0, T)`, by `CcDiffMomentum`, the integral
`∫_cell φ_R · 2⟨w, ∂_s w⟩` is the sum of the four terms (all integrands are continuous with support in
`|η| ≤ 2R`, hence integrable on the cell). -/
def CcIntegrandDecomp : Prop :=
  ∀ (ν c T M : ℝ) (v v' : ℝ → Plane → Vec) (p p' : ℝ → Plane → ℝ), CcPair ν c T M v v' p p' →
    ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Ioo (0 : ℝ) T,
      ccDt c v v' R s =
        ccViscous ν c v v' R s + ccTransport c v v' R s + ccStretch c v v' R s +
          ccPressure c v v' p p' R s

/-! ### Identity / estimate pairs -/

/-- **Leaf `CcViscousIdentity`**: `T_visc = -2νD - 2ν ∫ φ' ⟨w, ∂_η w⟩` (cell integration by parts of
`φ w_i (∂_q² + ∂_η²) w_i` for each component; `φ` depends on `η` only). -/
def CcViscousIdentity : Prop :=
  ∀ (ν c T M : ℝ) (v v' : ℝ → Plane → Vec) (p p' : ℝ → Plane → ℝ), CcPair ν c T M v v' p p' →
    ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Icc (0 : ℝ) T,
      ccViscous ν c v v' R s = ccViscousRhs ν c v v' R s

/-- **Leaf `CcViscousEstimate`**: with `|φ'| ≤ (C₀/R)√φ`, Young's inequality
`2ν|φ'||w||∂_η w| ≤ (ν/2) φ|∂_η w|² + 2ν(C₀/R)²|w|²` and `∫_cell |w|² ≤ 4M`:
`ccViscousRhs ≤ -(3/2)νD + K/√R` (in fact `K/R²`). -/
def CcViscousEstimate : Prop :=
  ∀ (ν c T M : ℝ) (v v' : ℝ → Plane → Vec) (p p' : ℝ → Plane → ℝ), CcPair ν c T M v v' p p' →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Icc (0 : ℝ) T,
      ccViscousRhs ν c v v' R s ≤ -(3 / 2) * ν * ccDissipation c v v' R s + K / Real.sqrt R

/-- **Leaf `CcTransportIdentity`**: `T_trans = ∫ |w|² v_η φ'` (`-2⟨w, (v·∇)w⟩ = -v·∇|w|²`, then
`∫ |w|² ∂_j(φ v_j) = ∫ |w|² φ' v_η` since `div v = 0`). -/
def CcTransportIdentity : Prop :=
  ∀ (ν c T M : ℝ) (v v' : ℝ → Plane → Vec) (p p' : ℝ → Plane → ℝ), CcPair ν c T M v v' p p' →
    ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Icc (0 : ℝ) T,
      ccTransport c v v' R s = ccTransportRhs c v v' R s

/-- **Leaf `CcTransportEstimate`**: `|v_η| ≤ M`, `|φ'| ≤ C₀/R`, `∫_cell |w|² ≤ 4M` give
`ccTransportRhs ≤ K/√R` (in fact `4C₀M²/R`). -/
def CcTransportEstimate : Prop :=
  ∀ (ν c T M : ℝ) (v v' : ℝ → Plane → Vec) (p p' : ℝ → Plane → ℝ), CcPair ν c T M v v' p p' →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Icc (0 : ℝ) T,
      ccTransportRhs c v v' R s ≤ K / Real.sqrt R

/-- **Leaf `CcStretchEstimate`**: from `CcStretchPointwise`, `|⟨w, (w·∇)v'⟩| ≤ K |w|²`, so
`T_stretch = -2∫ φ ⟨w, (w·∇)v'⟩ ≤ 2K F_R` (integrands continuous with support in `|η| ≤ 2R`). -/
def CcStretchEstimate : Prop :=
  ∀ (ν c T M : ℝ) (v v' : ℝ → Plane → Vec) (p p' : ℝ → Plane → ℝ), CcPair ν c T M v v' p p' →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Icc (0 : ℝ) T,
      ccStretch c v v' R s ≤ K * classicalCutoffEnergy c v v' R s

/-- **Leaf `CcPressureIdentity`**: `T_pres = 2 ∫ φ' π w_η` (`-2φ ⟨w, ∇π⟩ = -2 div(φ π w) + 2π ⟨w, ∇φ⟩`
since `div w = 0`; cell integration by parts in `q` and `η`). -/
def CcPressureIdentity : Prop :=
  ∀ (ν c T M : ℝ) (v v' : ℝ → Plane → Vec) (p p' : ℝ → Plane → ℝ), CcPair ν c T M v v' p p' →
    ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Icc (0 : ℝ) T,
      ccPressure c v v' p p' R s = ccPressureRhs c v v' p p' R s

/-- **Leaf `CcPressureEstimate`**: `|π| ≤ 2M`, `|φ'| ≤ (C₀/R) 1_{R ≤ |η| ≤ 2R}`, Cauchy-Schwarz on the
strip `{R ≤ |η| ≤ 2R} ∩ cell` of measure `2Rc` and `∫_cell |w|² ≤ 4M`:
`ccPressureRhs ≤ K/√R` with `K = 4C₀M √(8cM)`. -/
def CcPressureEstimate : Prop :=
  ∀ (ν c T M : ℝ) (v v' : ℝ → Plane → Vec) (p p' : ℝ → Plane → ℝ), CcPair ν c T M v v' p p' →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Icc (0 : ℝ) T,
      ccPressureRhs c v v' p p' R s ≤ K / Real.sqrt R

/-! ### The conditional theorem -/

/-- **`PartI:T02/3/11`, conditional form**: `ClassicalCutoffEnergyIneq` from the ten leaves. -/
theorem classicalCutoffEnergyIneq_of (hC : CcEnergyContinuous) (hD : CcEnergyHasDeriv)
    (hE : CcIntegrandDecomp) (hVi : CcViscousIdentity) (hVe : CcViscousEstimate)
    (hTi : CcTransportIdentity) (hTe : CcTransportEstimate) (hSe : CcStretchEstimate)
    (hPi : CcPressureIdentity) (hPe : CcPressureEstimate) :
    ClassicalCutoffEnergyIneq := by
  intro ν c T M v v' p p' hν hc hT cl cl' bd bd' bb bb'
  have hP : CcPair ν c T M v v' p p' := ⟨hν, hc, hT, cl, cl', bd, bd', bb, bb'⟩
  obtain ⟨KV, hKV, HV⟩ := hVe ν c T M v v' p p' hP
  obtain ⟨KT, hKT, HT⟩ := hTe ν c T M v v' p p' hP
  obtain ⟨KS, hKS, HS⟩ := hSe ν c T M v v' p p' hP
  obtain ⟨KP, hKP, HP⟩ := hPe ν c T M v v' p p' hP
  set C₁ : ℝ := KV + KT + KS + KP with hC₁
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; linarith
  have hT0 : (0 : ℝ) ≤ T := hT.le
  refine ⟨C₁ * (T + 1), mul_nonneg hC₁0 (by linarith), ?_⟩
  intro R hR
  have hRpos : 0 < R := by linarith
  have hsq : 0 < Real.sqrt R := Real.sqrt_pos.2 hRpos
  have hcont : ContinuousOn (classicalCutoffEnergy c v v' R) (Icc 0 T) :=
    hC ν c T M v v' p p' hP R hR
  refine ⟨hcont, ?_⟩
  intro s hs
  -- the pointwise differential inequality
  have hbound : ∀ r ∈ Ioo (0 : ℝ) T,
      ccDt c v v' R r ≤ C₁ * classicalCutoffEnergy c v v' R r + C₁ / Real.sqrt R := by
    intro r hr
    have hr' : r ∈ Icc (0 : ℝ) T := Ioo_subset_Icc_self hr
    rw [hE ν c T M v v' p p' hP R hR r hr, hVi ν c T M v v' p p' hP R hR r hr',
      hTi ν c T M v v' p p' hP R hR r hr', hPi ν c T M v v' p p' hP R hR r hr']
    have h1 := HV R hR r hr'
    have h2 := HT R hR r hr'
    have h3 := HS R hR r hr'
    have h4 := HP R hR r hr'
    have hD0 := ccDissipation_nonneg c v v' R r
    have hF0 := classicalCutoffEnergy_nonneg c v v' R r
    have hνD : 0 ≤ ν * ccDissipation c v v' R r := mul_nonneg hν.le hD0
    have hKF : KS * classicalCutoffEnergy c v v' R r ≤ C₁ * classicalCutoffEnergy c v v' R r :=
      mul_le_mul_of_nonneg_right (by rw [hC₁]; linarith) hF0
    have hsum : KV / Real.sqrt R + KT / Real.sqrt R + KP / Real.sqrt R ≤ C₁ / Real.sqrt R := by
      have : KV + KT + KP ≤ C₁ := by rw [hC₁]; linarith
      calc KV / Real.sqrt R + KT / Real.sqrt R + KP / Real.sqrt R
          = (KV + KT + KP) / Real.sqrt R := by ring
        _ ≤ C₁ / Real.sqrt R := div_le_div_of_nonneg_right this hsq.le
    linarith
  -- integrate
  set Fn : ℝ → ℝ := classicalCutoffEnergy c v v' R with hFn
  have hFint : IntervalIntegrable Fn volume 0 T := hcont.intervalIntegrable_of_Icc hT0
  have hprim : ContinuousOn (fun r => ∫ x in (0 : ℝ)..r, Fn x) (Icc 0 T) := by
    have h := intervalIntegral.continuousOn_primitive_interval' hFint
      (show (0 : ℝ) ∈ Set.uIcc 0 T from Set.left_mem_uIcc)
    rwa [Set.uIcc_of_le hT0] at h
  set H : ℝ → ℝ := fun r =>
    Fn r - (C₁ * (∫ x in (0 : ℝ)..r, Fn x) + C₁ / Real.sqrt R * r) with hH
  have hHcont : ContinuousOn H (Icc 0 T) :=
    hcont.sub ((continuousOn_const.mul hprim).add (continuousOn_const.mul continuousOn_id))
  have hHder : ∀ r ∈ Ioo (0 : ℝ) T, HasDerivAt H
      (ccDt c v v' R r - (C₁ * Fn r + C₁ / Real.sqrt R)) r := by
    intro r hr
    have hI := hD ν c T M v v' p p' hP R hR r hr
    have hcr : ContinuousAt Fn r := hcont.continuousAt (Icc_mem_nhds hr.1 hr.2)
    have hmeas : StronglyMeasurableAtFilter Fn (𝓝 r) volume :=
      (hcont.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo r hr
    have hFr : IntervalIntegrable Fn volume 0 r :=
      hFint.mono_set (by
        rw [Set.uIcc_of_le hT0, Set.uIcc_of_le hr.1.le]
        exact Icc_subset_Icc_right hr.2.le)
    have hP' : HasDerivAt (fun u => ∫ x in (0 : ℝ)..u, Fn x) (Fn r) r :=
      intervalIntegral.integral_hasDerivAt_right hFr hmeas hcr
    have hG : HasDerivAt (fun u => C₁ * (∫ x in (0 : ℝ)..u, Fn x) + C₁ / Real.sqrt R * u)
        (C₁ * Fn r + C₁ / Real.sqrt R) r := by
      have h := (hP'.const_mul C₁).add ((hasDerivAt_id' r).const_mul (C₁ / Real.sqrt R))
      rwa [mul_one] at h
    exact hI.sub hG
  have hanti : AntitoneOn H (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hHcont
    · intro r hr
      rw [interior_Icc] at hr
      exact (hHder r hr).differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      rw [(hHder r hr).deriv]
      have := hbound r hr
      linarith
  have hH0 : H 0 = 0 := by
    simp [hH, hFn, classicalCutoffEnergy_zero hP]
  have hle : H s ≤ H 0 := hanti ⟨le_rfl, hT0⟩ hs hs.1
  have hint0 : 0 ≤ ∫ x in (0 : ℝ)..s, Fn x :=
    intervalIntegral.integral_nonneg hs.1 (fun x _ => classicalCutoffEnergy_nonneg c v v' R x)
  have h1 : Fn s ≤ C₁ * (∫ x in (0 : ℝ)..s, Fn x) + C₁ / Real.sqrt R * s := by
    have : H s ≤ 0 := hH0 ▸ hle
    simp only [hH] at this
    linarith
  have h2 : C₁ * (∫ x in (0 : ℝ)..s, Fn x) ≤ C₁ * (T + 1) * (∫ x in (0 : ℝ)..s, Fn x) := by
    apply mul_le_mul_of_nonneg_right _ hint0
    nlinarith [hT0]
  have h3 : C₁ / Real.sqrt R * s ≤ C₁ * (T + 1) / Real.sqrt R := by
    have : C₁ * s ≤ C₁ * (T + 1) := mul_le_mul_of_nonneg_left (by linarith [hs.2]) hC₁0
    calc C₁ / Real.sqrt R * s = (C₁ * s) / Real.sqrt R := by ring
      _ ≤ C₁ * (T + 1) / Real.sqrt R := div_le_div_of_nonneg_right this hsq.le
  show Fn s ≤ C₁ * (T + 1) * (∫ r in (0 : ℝ)..s, Fn r) + C₁ * (T + 1) / Real.sqrt R
  linarith

end UnforcedLeray.Short.PartI
