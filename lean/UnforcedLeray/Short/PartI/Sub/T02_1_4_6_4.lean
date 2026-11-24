import UnforcedLeray.Short.PartI.Sub.T02_1_4_6
import UnforcedLeray.Lib.HeatCylinder.HeatVecCenteredSelfAdjoint
import UnforcedLeray.Lib.HeatCylinder.CenteredHeatProjectionConditional

/-!
# Part I, task `PartI:T02/1/4/6/4`: the stress generator (conditional decomposition)

Source of record: `the November 2 reference manuscript`, lines 261-288
(Gallay-Slijepcevic 2015, Theorem 1.1 and Remark 1.3(2): the mild solution is a classical
solution of the Navier-Stokes system modulo gradients; the Duhamel term of the mild equation is the
heat flow of the divergence of the stress `u ⊗ u`).

Target: `StressGenerator` (`Short/PartI/Sub/T02_1_4_6.lean`).  For the compact mild `H³` train `u`
with smooth solenoidal representative `w`, the Duhamel pairing
`X(τ) = ∫_0^τ ⟨compactMildStressOrbit u τ r, ψ⟩ dr` has, for `0 < τ < T`, the derivative
`⟨(w τ·∇) w τ, ψ⟩_{cell} + ν ∫_0^τ ⟨compactMildStressOrbit u τ r, Δψ⟩ dr`.

The proof is cut into four leaf statements (the bookkeeping `inner_eq_cell_integral` is proved
here):

* `StressOrbitIsHeat` (leaf 1): for `0 < r < t < T` the stress orbit is the centered heat flow
  `e^{ν(t-r)Δ}` of the `L²` class `G r` of the advection `(w r·∇)w r` (the class of
  `div (w r ⊗ w r)`, since `div (w r) = 0`);
* `CenteredHeatAgeDerivative` (leaf 2): the age derivative of the centered heat on a smooth
  periodic `η`-compact test `ψ` is the heat of `Δψ`, tested against any `L²` class;
* `CenteredHeatContinuity` (leaf 3): the centered heat orbit `θ ↦ e^{θΔ} x` is continuous in `L²`
  at every real age (identity for `θ ≤ 0`; strong continuity at age `0`);
* `DuhamelLeibnizL2` (leaf 4): the Leibniz rule for the Duhamel integral with moving upper limit
  (pure analysis, uses only the two preceding leaves as hypotheses and `‖heat‖ ≤ 1`);
* `AdvectionL2Representative` (leaf 5): the advection of the representative is a continuous
  `L²`-valued path.

`stressGenerator_of` assembles `StressGenerator` from the five leaves.  No `sorry`, `admit`,
`axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB
open UnforcedLeray.HeatCylinder

/-! ### The leaf statements -/

/-- **Leaf 1** (the stress orbit is a centered heat flow; source lines 261-288).  If `G r` is the
`L²(cell)` class of the advection `(w r·∇) w r` of the smooth solenoidal representative `w` of the
mild train `u`, then for `0 < r < t < T` the zero-order class of the Gaussian heat-divergence
orbit of the stress `u(r) ⊗ u(r)` at age `ν (t - r)` is `e^{ν(t-r)Δ} (G r)`
(`centeredHeatVecL2CLM hc (ν (t - r)) (G r)`).

Proof idea: `compactMildStressOrbit u t r = V₀ (actualHeatDivH3Orbit hc (stress r) (ν (t - r)))`
(`Lib/TrainB/P0MildWeakSpatialPairing.lean:28`, `stress r = tensorH3Bilinear (u r) (u r)`,
`Lib/TrainB/P0GaussianVelocityPath.lean:33`); for positive age `actualHeatDivH3Orbit = actualHeatDivH3CLM`
(`Lib/HeatCylinder/H3RoughOrbitContinuity.lean:26`) and
`vectorH3NormalizedValue_actualHeatDivH3` (`Lib/HeatCylinder/H3Operator.lean:84`) says its
normalized value is `heatDivVecL2CLM` applied to the normalized value of the tensor; the tensor has
the literal row representative `w r ⊗ w r` almost everywhere (`tensorH3Bilinear_value_ae`,
`Lib/TrainB/TensorBridge.lean:584`, together with `IsSpatialRepOn.represents` at the zero word), and
`B0296.heatDiv θ T z = ∫ ∇K_θ(y)·T(z - y) dy` (`Units/B0296/Conv.lean:271`) equals
`∫ K_θ(y) div T(z - y) dy` by integration by parts against the Gaussian (`T = w r ⊗ w r` is smooth
with bounded derivatives), and `div (w r ⊗ w r) = (w r·∇) w r + (div w r) w r = (w r·∇) w r`.
Finally the heat convolution with `K_θ` of the `L²` class `G r` is `centeredHeatVecL2CLM hc θ (G r)`
(`Lib/HeatCylinder/CenteredHeatProjectionConditional.lean:37`, the centered/normalized transport
`centeredVecToNormalizedCLM`, `normalizedVecToCenteredCLM`).  The sign is `+`: `heatDiv` is
`e^{θΔ} div` with `div S = Σ_j ∂_j S_j` for the row tensor `S = (u_0 v, u_1 v)`. -/
def StressOrbitIsHeat : Prop :=
  ∀ (ν c T : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)),
    IsMildTrain ν c T hν hc hc1 hT u → ∀ w : ℝ → Plane → Vec, IsSpatialRepOn c T u w →
    (∀ s ∈ Icc (0 : ℝ) T, ∀ z, Cyl.divergence (w s) z = 0) →
    ∀ G : ℝ → Cyl.L2v c,
      (∀ r ∈ Icc (0 : ℝ) T, ((G r : Cyl.L2v c) : Plane → Vec) =ᵐ[Cyl.cellμ c]
        Train.advection (w r)) →
      ∀ t ∈ Ioo (0 : ℝ) T, ∀ r ∈ Ioo (0 : ℝ) t,
        compactMildStressOrbit (ν := ν) hc hc1 hT.le u t r =
          centeredHeatVecL2CLM hc (ν * (t - r)) (G r)

/-- **Leaf 2** (age derivative of the centered heat on a smooth periodic test; source lines
261-288).  For a smooth periodic `η`-compact test `ψ` with `L²` classes `ψL` of `ψ` and `ψ'L` of
`Δψ`, and any `L²` class `G`, the function `s ↦ ⟨G, e^{sΔ} ψL⟩` is differentiable at every `θ > 0`
with derivative `⟨G, e^{θΔ} ψ'L⟩`.

Proof idea: `∂_θ K_θ = Δ K_θ` (`heatKernel2AgeDerivative_eq_spatialLaplacian`,
`Lib/HeatCylinder/HeatKernelAgeLaplacian.lean:145`; the age derivative of the convolution is
`hasDerivAt_heatVecConvolution_age`, `Lib/HeatCylinder/HeatVecAgeDerivative.lean:30`), the centered
heat of the smooth periodic test is the Gaussian convolution of `ψ`
(`Lib/HeatCylinder/CenteredHeatProjectionConditional.lean`, `HeatVecGaussian*.lean`), and
`K_θ * Δψ = Δ (K_θ * ψ)`; pass from the pointwise derivative to the `L²` pairing by dominated
convergence (the difference quotient of `K_s * ψ` is `K_s * (difference quotient of ψ-flow)`,
bounded by `sup |Δψ|` on the compact `η`-support of `ψ`) or, equivalently, from the
semigroup identity `heat(h) ψL - ψL = ∫_0^h heat(r) ψ'L dr` (weak form) plus strong continuity. -/
def CenteredHeatAgeDerivative : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (ψ : Plane → Vec) (ψL ψ'L : Cyl.L2v c), IsCellTest c ψ →
    ((ψL : Cyl.L2v c) : Plane → Vec) =ᵐ[Cyl.cellμ c] ψ →
    ((ψ'L : Cyl.L2v c) : Plane → Vec) =ᵐ[Cyl.cellμ c] Train.vecLaplacian ψ →
    ∀ (G : Cyl.L2v c) (θ : ℝ), 0 < θ →
      HasDerivAt (fun s : ℝ => inner ℝ G (centeredHeatVecL2CLM hc s ψL))
        (inner ℝ G (centeredHeatVecL2CLM hc θ ψ'L)) θ

/-- **Leaf 3** (continuity of the centered heat orbit in the age; source lines 261-288).  For
every `L²` class `x`, the orbit `θ ↦ e^{θΔ} x` is continuous `ℝ → L²(cell)`; for `θ ≤ 0` it is the
constant `x` (`centeredHeatVecL2CLM_eq_id_of_nonpos`,
`Lib/HeatCylinder/HeatVecCenteredSemigroup.lean:58`), so continuity at `0` is the strong continuity of
the heat semigroup at age `0` and implies `e^{θΔ} x → x` as `θ → 0+`.

Proof idea: `centeredHeatVecL2CLM hc θ = normalizedVecToCenteredCLM ∘ heatVecL2CLM hc θ ∘
centeredVecToNormalizedCLM` (`Lib/HeatCylinder/CenteredHeatProjectionConditional.lean:37`) and
`heatVecL2CLM hc θ = compLpL toVecL ∘ heatL2CLM hc θ ∘ compLpL toVecL.symm`
(`Lib/HeatCylinder/HeatVecL2.lean:26`); `θ ↦ heatL2CLM hc θ y` is continuous for every `y`
(`continuous_heatL2CLM_apply`, `Lib/HeatCylinder/HeatL2StrongContinuity.lean:79`, which already
covers all real ages), and the other three maps are fixed continuous linear maps (apply
`ContinuousLinearMap.continuous` to the composite). -/
def CenteredHeatContinuity : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (x : Cyl.L2v c), Continuous (fun θ : ℝ => centeredHeatVecL2CLM hc θ x)

/-- **Leaf 4** (Leibniz rule for the Duhamel integral with moving limit; source lines 261-288;
pure analysis).  Let `G` be continuous on `[0,T]` with values in `L²(cell)`, and `ψL`, `ψ'L` be
`L²` classes such that (hypothesis `h2`) `s ↦ ⟨G', e^{sΔ} ψL⟩` has derivative `⟨G', e^{θΔ} ψ'L⟩`
at each `θ > 0`, for every `G'`, and (hypothesis `h3`) every orbit `θ ↦ e^{θΔ} x` is continuous.
Then for
`0 < τ < T`
`d/dσ ∫_0^σ ⟨G r, e^{ν(σ-r)Δ} ψL⟩ dr |_{σ=τ} = ⟨G τ, ψL⟩ + ν ∫_0^τ ⟨G r, e^{ν(τ-r)Δ} ψ'L⟩ dr`.

Proof idea (no semigroup law is needed): put `Q(σ,r) = ⟨G r, P(ν(σ-r)) ψL⟩` for `r < σ`, where
`P = centeredHeatVecL2CLM hc`, `‖P θ‖ ≤ 1` for `θ > 0` (`norm_centeredHeatVecL2CLM_le_one`,
`Lib/HeatCylinder/CenteredHeatProjectionConditional.lean:61`).  By `h2` and the chain rule
`∂_σ Q(σ,r) = ν⟨G r, P(ν(σ-r)) ψ'L⟩`, bounded by `ν ‖G r‖ ‖ψ'L‖`; `G` is bounded on the compact
`[0,T]`.  Differentiate under the integral with the variable upper limit:
`I(σ+h) - I(σ) = ∫_0^σ (Q(σ+h,r) - Q(σ,r)) dr + ∫_σ^{σ+h} Q(σ+h,r) dr` (for `h < 0` use
`I(σ) - I(σ+h)`); the first term divided by `h` tends to `ν ∫_0^σ ⟨G r, P(ν(σ-r)) ψ'L⟩ dr` by the mean
value inequality and dominated convergence
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`,
`Mathlib/Analysis/Calculus/ParametricIntegral.lean`), the second divided by `h` tends to
`Q(τ,τ) := ⟨G τ, ψL⟩` because `r ↦ G r` is continuous and `P θ ψL → ψL` (`h3`) with
`‖P θ ψL‖ ≤ ‖ψL‖` (and `P 0 = id`, `h3` at age `0`), so `Q(σ+h, r) → ⟨G τ, ψL⟩` as
`(h, r) → (0, τ)`; the continuity `h3` also gives measurability and integrability of
`r ↦ ⟨G r, P(ν(σ-r)) x⟩` on `(0,σ)`.  Alternatively use
`intervalIntegral.integral_hasDerivAt_right`-style FTC after splitting
`I(σ) = ∫_0^{τ_0} Q(σ,r) dr + ∫_{τ_0}^σ Q(σ,r) dr` with `τ_0 < τ` fixed. -/
def DuhamelLeibnizL2 : Prop :=
  ∀ (c ν T : ℝ) (hc : 0 < c) (hν : 0 < ν) (G : ℝ → Cyl.L2v c) (ψL ψ'L : Cyl.L2v c),
    ContinuousOn G (Icc (0 : ℝ) T) →
    (∀ (G' : Cyl.L2v c) (θ : ℝ), 0 < θ →
      HasDerivAt (fun s : ℝ => inner ℝ G' (centeredHeatVecL2CLM hc s ψL))
        (inner ℝ G' (centeredHeatVecL2CLM hc θ ψ'L)) θ) →
    (∀ x : Cyl.L2v c, Continuous (fun θ : ℝ => centeredHeatVecL2CLM hc θ x)) →
    ∀ τ ∈ Ioo (0 : ℝ) T,
      HasDerivAt
        (fun σ : ℝ => ∫ r in Ioo (0 : ℝ) σ,
          inner ℝ (G r) (centeredHeatVecL2CLM hc (ν * (σ - r)) ψL))
        (inner ℝ (G τ) ψL + ν * ∫ r in Ioo (0 : ℝ) τ,
          inner ℝ (G r) (centeredHeatVecL2CLM hc (ν * (τ - r)) ψ'L)) τ

/-- **Leaf 5** (the advection of the representative is a continuous `L²` path; source lines
261-288).  For the smooth representative `w` of the compact mild `H³` train, there is a path
`G : ℝ → L²(cell)`, continuous on `[0,T]`, with `G r = (w r·∇) w r` almost everywhere on the cell
for each `r ∈ [0,T]`.

Proof idea: `w r` is the continuous representative of `u r ∈ H³`, with bounded derivatives
(`IsSpatialRepOn.bounded`) and `represents` identifying its derivative words of length `≤ 3` with the
`L²` classes `vecH3CellDerivCLM α (u r)`.  The advection is a continuous bilinear map: the zero-order
value is bounded (`H²(cell) ⊂ L^∞`, `B0151.enorm_le_H2`, `Lib/Cylinder/SupBound.lean`, `c ≥ 1`) and
the first derivatives are in `L²`, so `‖(a·∇)b‖_{L²} ≤ C ‖a‖_{H²} ‖b‖_{H¹}`; hence
`r ↦ [(w r·∇) w r] = Σ_j [w_j r] ∂_j [w r]` (product of an `L^∞`-bounded and an `L²` class) is
continuous in `L²` because `u` is continuous into `H³` (`u.continuous`). -/
def AdvectionL2Representative : Prop :=
  ∀ (ν c T : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)),
    IsMildTrain ν c T hν hc hc1 hT u → ∀ w : ℝ → Plane → Vec, IsSpatialRepOn c T u w →
    ∃ G : ℝ → Cyl.L2v c, ContinuousOn G (Icc (0 : ℝ) T) ∧
      ∀ r ∈ Icc (0 : ℝ) T, ((G r : Cyl.L2v c) : Plane → Vec) =ᵐ[Cyl.cellμ c]
        Train.advection (w r)

/-! ### Bookkeeping (proved) -/

/-- The `L²` pairing of two classes with given a.e. representatives is the cell integral of the
pointwise inner product of the representatives. -/
theorem inner_eq_cell_integral {c : ℝ} (f ψ : Plane → Vec) (G ψL : Cyl.L2v c)
    (hG : ((G : Cyl.L2v c) : Plane → Vec) =ᵐ[Cyl.cellμ c] f)
    (hψ : ((ψL : Cyl.L2v c) : Plane → Vec) =ᵐ[Cyl.cellμ c] ψ) :
    inner ℝ G ψL = ∫ z in Cyl.cell c, inner ℝ (f z) (ψ z) := by
  rw [MeasureTheory.L2.inner_def]
  change ∫ z, inner ℝ ((G : Cyl.L2v c) z) ((ψL : Cyl.L2v c) z) ∂(Cyl.cellμ c) = _
  refine integral_congr_ae ?_
  filter_upwards [hG, hψ] with z h1 h2
  rw [h1, h2]

/-! ### The conditional theorem -/

/-- **`StressGenerator` from the five leaves.**  Take the continuous advection path `G` of leaf 5.
Near `t` the Duhamel pairing `∫_0^τ ⟨orbit τ r, ψ⟩ dr` equals
`∫_0^τ ⟨G r, e^{ν(τ-r)Δ} ψL⟩ dr` by leaf 1 and the self-adjointness of the centered heat
(`inner_centeredHeatVecL2CLM_symm`); leaf 4 (with leaves 2 and 3 as hypotheses) differentiates it,
the boundary term `⟨G t, ψL⟩` is the cell integral of `⟨(w t·∇)w t, ψ⟩`, and the Laplacian term is
turned back into an orbit pairing by leaf 1 and the self-adjointness. -/
theorem stressGenerator_of (h1 : StressOrbitIsHeat) (h2 : CenteredHeatAgeDerivative)
    (h3 : CenteredHeatContinuity) (h4 : DuhamelLeibnizL2)
    (h5 : AdvectionL2Representative) : StressGenerator := by
  intro ν c T hν hc hc1 hT u hu w hw hdiv ψ ψL ψ'L hψ hψL hψ'L t ht
  obtain ⟨G, hGc, hGae⟩ := h5 ν c T hν hc hc1 hT u hu w hw
  have horb := h1 ν c T hν hc hc1 hT u hu w hw hdiv G hGae
  -- the orbit pairing as a pairing of `G r` with the heat flow of the test
  have hpair : ∀ τ ∈ Ioo (0 : ℝ) T, ∀ r ∈ Ioo (0 : ℝ) τ, ∀ φL : Cyl.L2v c,
      inner ℝ (compactMildStressOrbit (ν := ν) hc hc1 hT.le u τ r) φL =
        inner ℝ (G r) (centeredHeatVecL2CLM hc (ν * (τ - r)) φL) := by
    intro τ hτ r hr φL
    rw [horb τ hτ r hr]
    exact inner_centeredHeatVecL2CLM_symm hc (mul_nonneg hν.le (sub_nonneg.mpr hr.2.le)) _ _
  have hD := h4 c ν T hc hν G ψL ψ'L hGc (h2 c hc ψ ψL ψ'L hψ hψL hψ'L) (h3 c hc) t ht
  -- the Duhamel pairing agrees with the Leibniz integral near `t`
  have hnhds : Ioo (0 : ℝ) T ∈ 𝓝 t := Ioo_mem_nhds ht.1 ht.2
  have hcongr : (fun σ : ℝ => ∫ r in Ioo (0 : ℝ) σ,
        inner ℝ (G r) (centeredHeatVecL2CLM hc (ν * (σ - r)) ψL)) =ᶠ[𝓝 t]
      (fun τ : ℝ => ∫ r in Ioo (0 : ℝ) τ,
        inner ℝ (compactMildStressOrbit (ν := ν) hc hc1 hT.le u τ r) ψL) := by
    filter_upwards [hnhds] with τ hτ
    refine setIntegral_congr_fun measurableSet_Ioo (fun r hr => ?_)
    exact (hpair τ hτ r hr ψL).symm
  have hD' := hD.congr_of_eventuallyEq hcongr.symm
  refine hD'.congr_deriv ?_
  have hb : inner ℝ (G t) ψL = ∫ z in Cyl.cell c, inner ℝ (Train.advection (w t) z) (ψ z) :=
    inner_eq_cell_integral _ _ _ _ (hGae t (Ioo_subset_Icc_self ht)) hψL
  have hl : ∫ r in Ioo (0 : ℝ) t, inner ℝ (G r) (centeredHeatVecL2CLM hc (ν * (t - r)) ψ'L) =
      ∫ r in Ioo (0 : ℝ) t,
        inner ℝ (compactMildStressOrbit (ν := ν) hc hc1 hT.le u t r) ψ'L := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun r hr => ?_)
    exact (hpair t ht r hr ψ'L).symm
  rw [hb, hl]

end UnforcedLeray.Short.PartI
