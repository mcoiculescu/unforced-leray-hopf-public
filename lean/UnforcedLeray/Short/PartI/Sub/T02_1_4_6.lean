import UnforcedLeray.Short.PartI.Sub.T02_1_4
import UnforcedLeray.Lib.TrainB.P0MildWeakSpatialPairing

/-!
# Part I, task `PartI:T02/1/4/6`: the Leray form of the mild equation (conditional)

Source of record: `the November 2 reference manuscript`, lines 261-288
(Gallay-Slijepcevic 2015, Theorem 1.1 and Remark 1.3(2): the mild solution solves the
Navier-Stokes system modulo gradients; the pressure is recovered afterwards).

Target: `RepLeray` (`Short/PartI/Sub/T02_1_4.lean`).  The mild pairing identity of the library
(`TrainB.inner_vecH3_mild_fixedPoint_eq`) says, for every weakly solenoidal `L²(cell)` test `ψ`,
```
⟨u(t), ψ⟩ = ⟨g(t), ψ⟩ - ∫_0^t ⟨compactMildStressOrbit u t r, ψ⟩ dr,       g = projected heat seed.
```
The "heat-generator step" (the library keeps it separate) is the `t`-derivative of the two terms on
the right; it is split into `SeedGenerator` and `StressGenerator`.  Everything else is bookkeeping
between `L²(cell)` classes and the smooth representative `w`:

* `DivFreeTestClass`, `LaplacianTestClosed`: a smooth periodic solenoidal field with `η`-compact
  support (`IsSolenoidalCellTest`) has a class in `divFree c`, and its Laplacian is again such a field.
* `RepPairing` (proved here): `⟨V₀ u(s), ψ⟩ = ∫_cell ⟨w s, ψ⟩`.
* `SeedGenerator`, `StressGenerator`: the generator step.
* `MildPairingDeriv` (proved here from the two generator leaves and the library's pairing
  identity): `d/dt ⟨V₀ u(t), φ⟩ = ν ⟨V₀ u(t), Δφ⟩ - ∫_cell ⟨(w·∇)w, φ⟩`.
* `TimeDerivUnderIntegral`, `LaplacianIBP`, `ResidualPairingSplit`: differentiation under the
  cell integral, double integration by parts against a periodic `η`-compact test, and the
  splitting of the momentum-residual integral into three integrals.

`repLeray_of` assembles `RepLeray` from these leaves and `RepSolenoidal` (`PartI:T02/1/4/3`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

/-! ### Test fields -/

/-- A smooth `c`-periodic field on the plane that vanishes for `|η|` large. -/
def IsCellTest (c : ℝ) (φ : Plane → Vec) : Prop :=
  ContDiff ℝ ∞ φ ∧ Cyl.IsPeriodic c φ ∧ ∃ R : ℝ, ∀ z : Plane, R < |z.2| → φ z = 0

/-- A smooth `c`-periodic solenoidal field with `η`-compact support. -/
def IsSolenoidalCellTest (c : ℝ) (φ : Plane → Vec) : Prop :=
  IsCellTest c φ ∧ ∀ z, Cyl.divergence φ z = 0

/-! ### The leaf statements -/

/-- **Leaf R1** (the `L²` class of a solenoidal test; source lines 261-288).  A smooth periodic
solenoidal field with `η`-compact support has an `L²(cell)` class lying in the weakly solenoidal
space `Cyl.divFree c`.  Proof idea: `φ` is continuous and vanishes for large `|η|`, so it lies in
`L²(cell)` (`Cyl.memLp_of_vanishes`, `Lib/CylinderB/Leray.lean`); for a cylinder test `χ`
(`Sob.IsCylTest c χ`) the pairing `⟪gradL χ, φL⟫ = ∫_cell ⟨∇χ, φ⟩` is `-∫_cell χ div φ = 0` by
integration by parts on the cell (`Cyl.integral_cell_partialQ_mul`,
`Cyl.integral_cell_partialEta_mul`, `Lib/Cylinder/IBP.lean`), using periodicity of both factors in
`q` and the `η`-compact support. -/
def DivFreeTestClass : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ φ : Plane → Vec, IsSolenoidalCellTest c φ →
    ∃ φL : Cyl.L2v c, ((φL : Cyl.L2v c) : Plane → Vec) =ᵐ[Cyl.cellμ c] φ ∧ φL ∈ Cyl.divFree c

/-- **Leaf R2** (the Laplacian of a solenoidal test is a solenoidal test).  `Δφ = vecLaplacian φ`
is smooth, `c`-periodic, vanishes for `|η|` large (the support is contained in the support of
`φ`, derivatives of a function vanishing on the open set `{|η| > R}` vanish there), and
`div Δφ = Δ div φ = 0` because the mixed second partials of a `C^∞` map commute.
`Cyl.partialQ` and `Cyl.partialEta` are `deriv`s of slices (`Cyl.partialQ_eq_fderiv`,
`Lib/Cylinder/IBP.lean:58`). -/
def LaplacianTestClosed : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ φ : Plane → Vec, IsSolenoidalCellTest c φ →
    IsSolenoidalCellTest c (Train.vecLaplacian φ)

/-- **Leaf R3** (pairing with the representative; proved below as `repPairing`).  For
`s ∈ [0,T]` the `L²` pairing of the zero-order class of `u s` with an `L²` class `φL` of `φ`
equals the cell integral of `⟨w s, φ⟩`. -/
def RepPairing : Prop :=
  ∀ (ν c T : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)),
    IsMildTrain ν c T hν hc hc1 hT u → ∀ w : ℝ → Plane → Vec, IsSpatialRepOn c T u w →
    ∀ s (hs : s ∈ Icc (0 : ℝ) T) (φ : Plane → Vec) (φL : Cyl.L2v c),
      ((φL : Cyl.L2v c) : Plane → Vec) =ᵐ[Cyl.cellμ c] φ →
      inner ℝ (vecH3CellDerivCLM Sob.Idx.zero (u ⟨s, hs⟩)) φL =
        ∫ z in Cyl.cell c, inner ℝ (w s z) (φ z)

/-- **Leaf R4a** (the seed generator, source lines 261-288, heat-generator step, part 1).  The
projected heat seed `g(τ) = P₀ e^{ντΔ} d` of the projected datum `d` satisfies, against weakly
solenoidal `L²` tests, `d/dτ ⟨V₀ g(τ), ψ⟩ = ν ⟨V₀ g(τ), Δψ⟩` for `τ > 0`.  Here `ψL` and `ψ'L`
are the `L²` classes of a smooth periodic `η`-compact `ψ` and of `Δψ`, both weakly solenoidal.
Proof idea: `P₀` is removed against solenoidal tests (`TrainB.inner_vecH3P0_eq_of_divFree`,
`Lib/TrainB/P0MildWeakSpatialPairing.lean:41`); `V₀ (heatVecH3Semigroup (ντ) d)` is the class of
the heat convolution `K_{ντ} * d` of the datum (`Lib/HeatCylinder/HeatVecH3ActualValue.lean`), the
heat semigroup is self-adjoint on the cell (`HeatVecCenteredSelfAdjoint.lean`), and
`∂_θ K_θ = ΔK_θ` (`heatKernel2AgeDerivative_eq_spatialLaplacian`,
`Lib/HeatCylinder/HeatKernelAgeLaplacian.lean:145`; `HeatVecAgeDerivative.lean:30` differentiates
the convolution in the age), so `d/dτ ⟨K_{ντ} * d, ψ⟩ = ν ⟨K_{ντ} * d, Δψ⟩` (the Laplacian is moved
onto the smooth periodic `η`-compact test by integration by parts on the cell, exactly as in
`LaplacianIBP`). -/
def SeedGenerator : Prop :=
  ∀ (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c) (ψ : Plane → Vec) (ψL ψ'L : Cyl.L2v c),
    IsCellTest c ψ →
    ((ψL : Cyl.L2v c) : Plane → Vec) =ᵐ[Cyl.cellμ c] ψ →
    ((ψ'L : Cyl.L2v c) : Plane → Vec) =ᵐ[Cyl.cellμ c] Train.vecLaplacian ψ →
    ψL ∈ Cyl.divFree c → ψ'L ∈ Cyl.divFree c →
    ∀ t : ℝ, 0 < t →
      HasDerivAt
        (fun τ : ℝ => inner ℝ (vecH3CellDerivCLM Sob.Idx.zero
          (projectedHeatSeedPath hc hν (projectedInitialDatumH3 hc) τ)) ψL)
        (ν * inner ℝ (vecH3CellDerivCLM Sob.Idx.zero
          (projectedHeatSeedPath hc hν (projectedInitialDatumH3 hc) t)) ψ'L) t

/-- **Leaf R4b** (the stress generator, source lines 261-288, heat-generator step, part 2).
For the mild train `u` with smooth solenoidal representative `w`, the Duhamel term
`X(τ) = ∫_0^τ ⟨compactMildStressOrbit u τ r, ψ⟩ dr` is differentiable for `0 < τ < T` with
`X'(τ) = ∫_cell ⟨(w τ·∇)w τ, ψ⟩ + ν ∫_0^τ ⟨compactMildStressOrbit u τ r, Δψ⟩ dr`.
Mathematics: `compactMildStressOrbit u τ r` is the zero-order class of `e^{ν(τ-r)Δ} div(u(r)⊗u(r))`
(`TrainB.compactMildStressOrbit`, `Lib/TrainB/P0MildWeakSpatialPairing.lean:28`) and
`div (w⊗w) = (w·∇)w` because `div w = 0`; the standard computation
`d/dτ ∫_0^τ ⟨e^{ν(τ-r)Δ}G(r), ψ⟩ dr = ⟨G(τ), ψ⟩ + ν ∫_0^τ ⟨e^{ν(τ-r)Δ}G(r), Δψ⟩ dr` for `G`
continuous in `L²` with values in `L²` (the boundary term uses strong continuity of the heat
semigroup, `Lib/HeatCylinder/HeatL2StrongContinuity.lean`, and the age derivative of the kernel).
Expect a further split (diagonal limit of the orbit pairing; differentiation of the parameter
integral). -/
def StressGenerator : Prop :=
  ∀ (ν c T : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)),
    IsMildTrain ν c T hν hc hc1 hT u → ∀ w : ℝ → Plane → Vec, IsSpatialRepOn c T u w →
    (∀ s ∈ Icc (0 : ℝ) T, ∀ z, Cyl.divergence (w s) z = 0) →
    ∀ (ψ : Plane → Vec) (ψL ψ'L : Cyl.L2v c), IsCellTest c ψ →
      ((ψL : Cyl.L2v c) : Plane → Vec) =ᵐ[Cyl.cellμ c] ψ →
      ((ψ'L : Cyl.L2v c) : Plane → Vec) =ᵐ[Cyl.cellμ c] Train.vecLaplacian ψ →
      ∀ t ∈ Ioo (0 : ℝ) T,
        HasDerivAt
          (fun τ : ℝ => ∫ r in Ioo (0 : ℝ) τ,
            inner ℝ (compactMildStressOrbit (ν := ν) hc hc1 hT.le u τ r) ψL)
          ((∫ z in Cyl.cell c, inner ℝ (Train.advection (w t) z) (ψ z)) +
            ν * ∫ r in Ioo (0 : ℝ) t,
              inner ℝ (compactMildStressOrbit (ν := ν) hc hc1 hT.le u t r) ψ'L) t

/-- **Leaf R5** (differentiation under the cell integral; source lines 261-288).  If `w` is
jointly `C^∞` (even `C¹` suffices) on `[0,T] × ℝ²` and `φ` is continuous and vanishes for `|η|`
large, then `t ↦ ∫_cell ⟨w t, φ⟩` is differentiable at every `s ∈ (0,T)` with derivative
`∫_cell ⟨∂ₜ w s, φ⟩`.  Proof idea: `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
(`Mathlib/Analysis/Calculus/ParametricIntegral.lean`) on the cell with the dominating function
`C · 1_{[-c/2,c/2]×[-R,R]}`; `∂ₜ w` is jointly continuous (it is `fderiv` of the joint map applied
to `(1,0)` on the open set `(0,T) × ℝ²`) hence bounded on `[s-δ,s+δ] × [-c/2,c/2] × [-R,R]`. -/
def TimeDerivUnderIntegral : Prop :=
  ∀ (c T : ℝ), 0 < c →
    ∀ w : ℝ → Plane → Vec, ContDiffOn ℝ ∞ (fun x : ℝ × Plane => w x.1 x.2) (Icc (0 : ℝ) T ×ˢ univ) →
    ∀ s ∈ Ioo (0 : ℝ) T, ∀ φ : Plane → Vec, Continuous φ →
      (∃ R : ℝ, ∀ z : Plane, R < |z.2| → φ z = 0) →
      HasDerivAt (fun t : ℝ => ∫ z in Cyl.cell c, inner ℝ (w t z) (φ z))
        (∫ z in Cyl.cell c, inner ℝ (deriv (fun t : ℝ => w t z) s) (φ z)) s

/-- **Leaf R6** (double integration by parts against a periodic `η`-compact test).  For smooth
`c`-periodic `v` and a smooth `c`-periodic `φ` vanishing for `|η|` large,
`∫_cell ⟨v, Δφ⟩ = ∫_cell ⟨Δv, φ⟩`.  Proof idea: apply `Cyl.integral_cell_partialQ_mul` and
`Cyl.integral_cell_partialEta_mul` (`Lib/Cylinder/IBP.lean`) twice to each component, one factor
in `q` and one in `η`; the boundary terms in `q` cancel by periodicity of both factors and the
`η`-boundary terms vanish because `φ` and its derivatives have compact `η`-support. -/
def LaplacianIBP : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ v φ : Plane → Vec, ContDiff ℝ ∞ v → Cyl.IsPeriodic c v →
    IsCellTest c φ →
    ∫ z in Cyl.cell c, inner ℝ (v z) (Train.vecLaplacian φ z) =
      ∫ z in Cyl.cell c, inner ℝ (Train.vecLaplacian v z) (φ z)

/-- **Leaf R7** (splitting the residual integral).  For a jointly smooth `w` and a smooth `φ`
vanishing for `|η|` large, the cell integral of `⟨momentumResidual ν w 0 s, φ⟩` is the sum of the
three cell integrals of the pieces `∂ₜw`, `w·∇w`, `-νΔw`.  Proof idea: `momentumResidual` with
the zero pressure is `deriv + advection - ν • vecLaplacian + gradS 0` (`Lib/Train/Ops.lean:105`,
`gradS 0 = 0`), `inner_add_left`, `inner_sub_left`, `inner_smul_left`, and `integral_add`,
`integral_sub`, `integral_const_mul` after checking integrability: each of the three fields is
continuous in `z` (joint smoothness on the open set `(0,T) × ℝ²`; `w s` is `C^∞`) and `φ`
vanishes outside `[-c/2,c/2] × [-R,R]`, so the integrands are continuous with compact support in
the cell (`Cyl.memLp_of_vanishes`-style argument). -/
def ResidualPairingSplit : Prop :=
  ∀ (ν c T : ℝ), 0 < c →
    ∀ w : ℝ → Plane → Vec, ContDiffOn ℝ ∞ (fun x : ℝ × Plane => w x.1 x.2) (Icc (0 : ℝ) T ×ˢ univ) →
    (∀ s ∈ Icc (0 : ℝ) T, ContDiff ℝ ∞ (w s)) →
    ∀ s ∈ Ioo (0 : ℝ) T, ∀ φ : Plane → Vec, ContDiff ℝ ∞ φ →
      (∃ R : ℝ, ∀ z : Plane, R < |z.2| → φ z = 0) →
      ∫ z in Cyl.cell c, inner ℝ (Train.momentumResidual ν w (fun _ _ => (0 : ℝ)) s z) (φ z) =
        (∫ z in Cyl.cell c, inner ℝ (deriv (fun t : ℝ => w t z) s) (φ z)) +
          (∫ z in Cyl.cell c, inner ℝ (Train.advection (w s) z) (φ z)) -
          ν * ∫ z in Cyl.cell c, inner ℝ (Train.vecLaplacian (w s) z) (φ z)

/-! ### Proved pieces -/

/-- `RepPairing` is `represents` with `α = 0` and the `L²` inner product formula. -/
theorem repPairing : RepPairing := by
  intro ν c T hν hc hc1 hT u _ w hw s hs φ φL hφ
  have hrep := hw.represents ⟨s, hs⟩ Sob.Idx.zero
  simp only [Sob.TestDomain.word_zero, Sob.iterD_nil] at hrep
  rw [MeasureTheory.L2.inner_def]
  change ∫ z, inner ℝ ((vecH3CellDerivCLM (c := c) Sob.Idx.zero (u ⟨s, hs⟩) : Cyl.L2v c) z)
      ((φL : Cyl.L2v c) z) ∂(Cyl.cellμ c) = _
  refine integral_congr_ae ?_
  filter_upwards [hrep, hφ] with z h1 h2
  rw [h1, h2]

/-- **The derivative of the mild pairing** (from the two generator leaves).  For a solenoidal test
`φ` with `L²` classes `φL` of `φ` and `φ'L` of `Δφ`, both weakly solenoidal, the extended path
`t ↦ ⟨V₀ u(t), φL⟩` has derivative `ν ⟨V₀ u(t), φ'L⟩ - ∫_cell ⟨(w t·∇)w t, φ⟩` at `t ∈ (0,T)`. -/
theorem mildPairingDeriv_of (h4a : SeedGenerator) (h4b : StressGenerator)
    (ν c T : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c))
    (hu : IsMildTrain ν c T hν hc hc1 hT u) (w : ℝ → Plane → Vec)
    (hw : IsSpatialRepOn c T u w)
    (hdiv : ∀ s ∈ Icc (0 : ℝ) T, ∀ z, Cyl.divergence (w s) z = 0)
    (φ : Plane → Vec) (φL φ'L : Cyl.L2v c) (hφ : IsCellTest c φ)
    (hφL : ((φL : Cyl.L2v c) : Plane → Vec) =ᵐ[Cyl.cellμ c] φ)
    (hφ'L : ((φ'L : Cyl.L2v c) : Plane → Vec) =ᵐ[Cyl.cellμ c] Train.vecLaplacian φ)
    (hφLd : φL ∈ Cyl.divFree c) (hφ'Ld : φ'L ∈ Cyl.divFree c)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun τ : ℝ => inner ℝ (vecH3CellDerivCLM Sob.Idx.zero (extendCompactPath hT.le u τ)) φL)
      (ν * inner ℝ (vecH3CellDerivCLM Sob.Idx.zero (extendCompactPath hT.le u t)) φ'L -
        ∫ z in Cyl.cell c, inner ℝ (Train.advection (w t) z) (φ z)) t := by
  have hfix := hu.1
  have hpair : ∀ (ψL : Cyl.L2v c), ψL ∈ Cyl.divFree c → ∀ τ ∈ Icc (0 : ℝ) T,
      inner ℝ (vecH3CellDerivCLM Sob.Idx.zero (extendCompactPath hT.le u τ)) ψL =
        inner ℝ (vecH3CellDerivCLM Sob.Idx.zero
          (projectedHeatSeedPath hc hν (projectedInitialDatumH3 hc) τ)) ψL -
        ∫ r in Ioo (0 : ℝ) τ,
          inner ℝ (compactMildStressOrbit (ν := ν) hc hc1 hT.le u τ r) ψL := by
    intro ψL hψL τ hτ
    have hp := inner_vecH3_mild_fixedPoint_eq hc hc1 hν hT
      ((projectedHeatSeedPath hc hν (projectedInitialDatumH3 hc)).comp compactTimeInclusion)
      u hfix ⟨τ, hτ⟩ hψL
    rw [extendCompactPath_apply_of_mem hT.le u hτ, sub_eq_add_neg]
    exact hp
  have hSeed := h4a ν c hν hc φ φL φ'L hφ hφL hφ'L hφLd hφ'Ld t ht.1
  have hStress := h4b ν c T hν hc hc1 hT u hu w hw hdiv φ φL φ'L hφ hφL hφ'L t ht
  have hD := hSeed.sub hStress
  have hnhds : Icc (0 : ℝ) T ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have hD' := hD.congr_of_eventuallyEq (f₁ := fun τ : ℝ =>
    inner ℝ (vecH3CellDerivCLM Sob.Idx.zero (extendCompactPath hT.le u τ)) φL) (by
    filter_upwards [hnhds] with τ hτ
    exact hpair φL hφLd τ hτ)
  refine hD'.congr_deriv ?_
  have h2 := hpair φ'L hφ'Ld t (Ioo_subset_Icc_self ht)
  rw [h2]
  ring

/-! ### The conditional theorem -/

/-- **`RepLeray` from the leaves.**  Apply `mildPairingDeriv_of` and `repPairing` to see that
`A(t) = ∫_cell ⟨w t, φ⟩` has derivative `ν ∫_cell ⟨w s, Δφ⟩ - ∫_cell ⟨(w s·∇)w s, φ⟩` at `s`; by
`TimeDerivUnderIntegral` the same derivative is `∫_cell ⟨∂ₜ w s, φ⟩`; `LaplacianIBP` moves `Δ`
onto `w s`, and `ResidualPairingSplit` turns the momentum residual into the sum.  The solenoidality
`RepSolenoidal` is used to identify `div (w⊗w)` with `w·∇w` inside `StressGenerator`. -/
theorem repLeray_of (h1 : DivFreeTestClass) (h2 : LaplacianTestClosed) (h3 : RepSolenoidal)
    (h4a : SeedGenerator) (h4b : StressGenerator) (h5 : TimeDerivUnderIntegral)
    (h6 : LaplacianIBP) (h7 : ResidualPairingSplit) : RepLeray := by
  intro ν c T hν hc hc1 hT u hu w hw hsm s hs φ hφs hφp hφd hφR
  have hsol : IsSolenoidalCellTest c φ := ⟨⟨hφs, hφp, hφR⟩, hφd⟩
  obtain ⟨φL, hφL, hφLd⟩ := h1 c hc φ hsol
  have hsol' := h2 c hc φ hsol
  obtain ⟨φ'L, hφ'L, hφ'Ld⟩ := h1 c hc _ hsol'
  have hdiv : ∀ s ∈ Icc (0 : ℝ) T, ∀ z, Cyl.divergence (w s) z = 0 :=
    h3 ν c T hν hc hc1 hT u hu w hw
  have hD := mildPairingDeriv_of h4a h4b ν c T hν hc hc1 hT u hu w hw hdiv φ φL φ'L hsol.1
    hφL hφ'L hφLd hφ'Ld s hs
  have hAφ : ∀ t ∈ Icc (0 : ℝ) T,
      inner ℝ (vecH3CellDerivCLM Sob.Idx.zero (extendCompactPath hT.le u t)) φL =
        ∫ z in Cyl.cell c, inner ℝ (w t z) (φ z) := by
    intro t ht
    rw [extendCompactPath_apply_of_mem hT.le u ht]
    exact repPairing ν c T hν hc hc1 hT u hu w hw t ht φ φL hφL
  have hAΔ : ∀ t ∈ Icc (0 : ℝ) T,
      inner ℝ (vecH3CellDerivCLM Sob.Idx.zero (extendCompactPath hT.le u t)) φ'L =
        ∫ z in Cyl.cell c, inner ℝ (w t z) (Train.vecLaplacian φ z) := by
    intro t ht
    rw [extendCompactPath_apply_of_mem hT.le u ht]
    exact repPairing ν c T hν hc hc1 hT u hu w hw t ht _ φ'L hφ'L
  have hnhds : Icc (0 : ℝ) T ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
  have hdA : HasDerivAt (fun t : ℝ => ∫ z in Cyl.cell c, inner ℝ (w t z) (φ z))
      (ν * (∫ z in Cyl.cell c, inner ℝ (w s z) (Train.vecLaplacian φ z)) -
        ∫ z in Cyl.cell c, inner ℝ (Train.advection (w s) z) (φ z)) s := by
    have hD' := hD.congr_of_eventuallyEq (f₁ := fun t : ℝ =>
      ∫ z in Cyl.cell c, inner ℝ (w t z) (φ z)) (by
      filter_upwards [hnhds] with t ht
      exact (hAφ t ht).symm)
    rw [hAΔ s (Ioo_subset_Icc_self hs)] at hD'
    exact hD'
  have hdB := h5 c T hc w hsm s hs φ hφs.continuous hφR
  have huniq := hdA.unique hdB
  have hibp := h6 c hc (w s) φ (hw.smooth s (Ioo_subset_Icc_self hs))
    (hw.periodic s (Ioo_subset_Icc_self hs)) ⟨hφs, hφp, hφR⟩
  have hsplit := h7 ν c T hc w hsm hw.smooth s hs φ hφs hφR
  rw [hsplit, ← hibp]
  linarith

end UnforcedLeray.Short.PartI
