import UnforcedLeray.Short.PartI.Sub.T02_1_4_4

/-!
# Part I, task `PartI:T02/1/4/4/1`: the time derivative of the mild path in every `H^m` (conditional)

Source of record: `the November 2 reference manuscript`, lines 261-288
(Gallay-Slijepcevic 2015, Theorem 1.1: the mild solution is smooth for positive time; the datum
`trainDatum c` is smooth, solenoidal and lies in every `H^k`).

Target: `MildPathDerivRhs` (`Short/PartI/Sub/T02_1_4_4.lean`).

## Strategy

1. **Level reduction (proved here).**  `Sob.W.restrict : H^k → H^j` is injective
   (`restrict_injective`; `value_restrict` is `rfl` and `Sob.W.value_injective`).  Hence an
   identity between `H^{k+3}`-valued objects follows from its restriction to `H^3`.  The family
   `R_k` is therefore required to be *compatible with restriction* to `R_0 : H^5 → H^3`, the
   level-3 right-hand side `v ↦ νΔv - P₀((v·∇)v)`; and the whole analytic content is the single
   identity at level 3,
   `u(t) = u(0) + ∫_0^t R_0(ub(s)) ds` in `H^3` for a mild train `u` with an `H^5` lift `ub`
   (`MildCoreIdentity`).  The step from this identity to `HasDerivWithinAt` at every `t ∈ [0,T]`
   (including the end points) is the fundamental theorem of calculus for the continuous integrand
   `R_k ∘ ukB` and is proved here in `mildPathDerivRhs_of`.
2. **The family `R_k`** (`RhsFamily`): bounded advection `H^{m+1} × H^{m+1} → H^m` (`m ≥ 3`),
   the Leray projection on `H^m`, and the Laplacian `H^{m+2} → H^m` (`hLap`, defined here) make
   `R_k` a continuous linear map plus a bounded quadratic map, hence `C^∞`.
3. **The level-3 identity** (`MildCoreIdentity = MildDuhamelStrongForm + HeatStrongDuhamel`):
   the mild equation of the library, rewritten with the `H^3` heat semigroup `S`, is
   `u(t) = S(νt)u(0) - ∫_0^t S(ν(t-r))G(r)dr` with `G = P₀((u·∇)u)` continuous in `H^3`
   (`MildDuhamelStrongForm`, from `HeatDivIdent`: `P₀ e^{θΔ}div(u⊗u) = S(θ)P₀(u·∇)u`);
   and an abstract semigroup argument (`AbstractStrongDuhamel`) together with the generator
   property of `S` on `H^5` (`HeatGeneratorH5`) turns this into the strong form
   `u(t) = u(0) + ∫_0^t (νΔu - G) ds` (`HeatStrongDuhamel`).

Leaves (to be proved by separate tasks, each in its own file): `AdvectionBase`, `AdvectionStep`,
`LerayStep`, `HeatDivIdent`, `HeatGeneratorH5`, `AbstractStrongDuhamel`; assemblies
`rhsFamily_of`, `mildDuhamelStrongForm_of`, `heatStrongDuhamel_of`.
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

/-! ### Concrete objects -/

/-- The representative of the zero-order part of an `H^m` element of the periodic cylinder scale
`Cyl.H ℝ Vec2 c 0 m` (unweighted), as a function on the plane. -/
def hVal {c : ℝ} {m : ℕ} (x : Cyl.H ℝ Cyl.Vec2 c 0 m) : Plane → Cyl.Vec2 :=
  (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 m 2 x : Plane → Cyl.Vec2)

/-- The Laplacian `Δ = ∂_q∂_q + ∂_η∂_η : H^{k+2} → H^k` built from the weak partial derivatives
`Sob.W.partialDeriv` (`Lib/Sobolev/Space.lean`). -/
def hLap (c : ℝ) (k : ℕ) :
    Cyl.H ℝ Cyl.Vec2 c 0 (k + 2) →L[ℝ] Cyl.H ℝ Cyl.Vec2 c 0 k :=
  ∑ i : Fin 2,
    (Sob.W.partialDeriv (k := k) i : Cyl.H ℝ Cyl.Vec2 c 0 (k + 1) →L[ℝ] Cyl.H ℝ Cyl.Vec2 c 0 k).comp
      (Sob.W.partialDeriv (k := k + 1) i :
        Cyl.H ℝ Cyl.Vec2 c 0 (k + 2) →L[ℝ] Cyl.H ℝ Cyl.Vec2 c 0 (k + 1))

/-- **Restriction is injective** (`value_restrict` is `rfl` and `Sob.W.value_injective`): an
element of `H^k` is determined by its image in `H^j`, `j ≤ k`. -/
theorem restrict_injective (c : ℝ) {j k : ℕ} (h : j ≤ k) :
    Function.Injective
      (Sob.W.restrict h : Cyl.H ℝ Cyl.Vec2 c 0 k → Cyl.H ℝ Cyl.Vec2 c 0 j) := by
  intro x y hxy
  apply Sob.W.value_injective
  have := congrArg (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 j 2) hxy
  exact this

/-- Restrictions compose (by injectivity). -/
theorem restrict_restrict (c : ℝ) {i j k : ℕ} (h₁ : i ≤ j) (h₂ : j ≤ k) (h₃ : i ≤ k)
    (x : Cyl.H ℝ Cyl.Vec2 c 0 k) :
    Sob.W.restrict h₁ (Sob.W.restrict h₂ x : Cyl.H ℝ Cyl.Vec2 c 0 j) =
      (Sob.W.restrict h₃ x : Cyl.H ℝ Cyl.Vec2 c 0 i) := by
  apply Sob.W.value_injective
  rfl

/-! ### The advection term and the right-hand side at level 3 -/

/-- `A ∈ H^3` is the advection term `(w·∇)w` of `w ∈ H^5` (source lines 261-288, the nonlinearity
of the Navier-Stokes system): its representative is a.e. the pointwise `∑_i w_i ∂_i w`, where
`∂_i` is the weak partial derivative of `w` viewed in `H^4`.  The element `A` is unique when it
exists (`Sob.W.value_injective`). -/
def IsAdvectionTerm (c : ℝ) (w : Cyl.H ℝ Cyl.Vec2 c 0 5) (A : Cyl.H ℝ Cyl.Vec2 c 0 3) : Prop :=
  hVal A =ᵐ[Cyl.cellμ c] fun z =>
    ∑ i : Fin 2, (hVal w z i) •
      hVal (Sob.W.partialDeriv (k := 3) i
        (Sob.W.restrict (by norm_num : 4 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 4)) z

/-- `R0 : H^5 → H^3` is the level-3 right-hand side of the Navier-Stokes system modulo
gradients, `R0 w = νΔw - P₀((w·∇)w)`: continuous, and for every `w` there is the advection term
`A = (w·∇)w ∈ H^3` with `R0 w = ν hLap w - P₀ A`.  (The operator is determined by this property:
`A` is unique, so `R0` is unique; `RhsFamily` shows it exists and is smooth.) -/
def IsRhsOp (ν c : ℝ) (hc : 0 < c)
    (R0 : Cyl.H ℝ Cyl.Vec2 c 0 5 → Cyl.H ℝ Cyl.Vec2 c 0 3) : Prop :=
  Continuous R0 ∧ ∀ w : Cyl.H ℝ Cyl.Vec2 c 0 5, ∃ A : Cyl.H ℝ Cyl.Vec2 c 0 3,
    IsAdvectionTerm c w A ∧ R0 w = ν • hLap c 3 w - P0H3CLM hc A

/-! ### Leaf statements: the advection bilinear map -/

/-- `B` is the bounded advection bilinear map `H^{m+1} × H^{m+1} → H^m`,
`B v w = ∑_i v_i ∂_i w`, in the a.e. sense. -/
def IsAdvectionOp (c : ℝ) (m : ℕ)
    (B : Cyl.H ℝ Cyl.Vec2 c 0 (m + 1) →L[ℝ] Cyl.H ℝ Cyl.Vec2 c 0 (m + 1) →L[ℝ]
      Cyl.H ℝ Cyl.Vec2 c 0 m) : Prop :=
  ∀ v w, hVal (B v w) =ᵐ[Cyl.cellμ c] fun z =>
    ∑ i : Fin 2, (hVal v z i) • hVal (Sob.W.partialDeriv (k := m) i w) z

/-- Level `m` of the product estimate: the advection map exists as a bounded bilinear map
`H^{m+1} × H^{m+1} → H^m`. -/
def AdvectionAt (c : ℝ) (m : ℕ) : Prop :=
  ∃ B : Cyl.H ℝ Cyl.Vec2 c 0 (m + 1) →L[ℝ] Cyl.H ℝ Cyl.Vec2 c 0 (m + 1) →L[ℝ]
      Cyl.H ℝ Cyl.Vec2 c 0 m, IsAdvectionOp c m B

/-- **Leaf A1** (base case of the product estimate; source lines 261-288).  For `m = 3`,
`(v,w) ↦ ∑_i v_i ∂_i w` is a bounded bilinear map `H^4 × H^4 → H^3`.  Proof idea: `∂_i w ∈ H^3`
and `v_i ∈ H^4 ⊂ H^3`, and the library has the bounded scalar product `H^3 × H^3 → H^3` with the
a.e. product formula (`TrainB.scalarH3Mul`, `scalarH3Mul_value_ae`, `scalarH3Mul_norm_le`,
`scalarH3Bilinear`, `Lib/TrainB/WeakGraph.lean`; vector components `vectorH3Component` in
`Lib/TrainB/TensorBridge.lean`); sum over `i : Fin 2`, precompose with the restriction
`H^4 → H^3` and the partial derivative `H^4 → H^3`. -/
def AdvectionBase : Prop :=
  ∀ (c : ℝ), 0 < c → 1 ≤ c → AdvectionAt c 3

/-- **Leaf A2** (inductive step of the product estimate; source lines 261-288).  If the
advection map exists at level `m ≥ 3` then it exists at level `m + 1`.  Proof idea: for
`v, w ∈ H^{m+2}` the function `f = ∑_i v_i ∂_i w = B_m(res v, res w) ∈ H^m` (`res` the
restriction to `H^{m+1}`) has, in the weak sense, `∂_j f = B_m(∂_j v, res w) + B_m(res v, ∂_j w)`
(Leibniz rule: both terms lie in `H^m` since `∂_j v, ∂_j w ∈ H^{m+1}`), so `f ∈ H^{m+1}`,
with norm bounded by `C ‖v‖ ‖w‖` from the bound of `B_m`; build `B_{m+1}` with
`Sob.W.ofFields`/`LinearMap.mkContinuous₂`.  The weak Leibniz rule for `H^{m+1}`-fields with
`m ≥ 3` is the technical core (library: `Lib/TrainB/SmoothProduct.lean`,
`Lib/TrainB/WeakEmbedding.lean`, `Lib/Sobolev/WeakDeriv.lean`). -/
def AdvectionStep : Prop :=
  ∀ (c : ℝ), 0 < c → 1 ≤ c → ∀ m : ℕ, 3 ≤ m → AdvectionAt c m → AdvectionAt c (m + 1)

/-- The product estimate at every level `m ≥ 3` (the content of leaves A1, A2). -/
def AdvectionBilinear : Prop :=
  ∀ (c : ℝ), 0 < c → 1 ≤ c → ∀ m : ℕ, 3 ≤ m → AdvectionAt c m

/-- `AdvectionBilinear` from the base case and the inductive step. -/
theorem advectionBilinear_of (h0 : AdvectionBase) (h1 : AdvectionStep) : AdvectionBilinear := by
  intro c hc hc1 m hm
  induction m, hm using Nat.le_induction with
  | base => exact h0 c hc hc1
  | succ m hm ih => exact h1 c hc hc1 m hm ih

/-! ### Leaf statements: the Leray projection on `H^m` -/

/-- Level `m ≥ 3` of the statement that `P₀` (known on `H^3`, `TrainB.P0H3CLM`) preserves `H^m`:
there is a bounded operator on `H^m` that restricts to `P₀` on `H^3`. -/
def LerayAt (c : ℝ) (hc : 0 < c) (m : ℕ) (hm : 3 ≤ m) : Prop :=
  ∃ P : Cyl.H ℝ Cyl.Vec2 c 0 m →L[ℝ] Cyl.H ℝ Cyl.Vec2 c 0 m, ∀ x,
    (Sob.W.restrict hm (P x) : Cyl.H ℝ Cyl.Vec2 c 0 3) =
      P0H3CLM hc (Sob.W.restrict hm x : Cyl.H ℝ Cyl.Vec2 c 0 3)

/-- **Leaf P1** (inductive step: `P₀` preserves `H^{m+1}`; source lines 261-288).  Proof idea:
`P₀` commutes with the weak derivatives `∂_q, ∂_η` (library: `hasWeakDeriv_P0_q_of_vecH1` and the
`η` analogue, `Lib/TrainB/P0SmoothH3.lean`, `Lib/CylinderB/Leray.lean`); for `x ∈ H^{m+1}` the
element `P_m(res x) ∈ H^m` therefore has the weak derivatives `P_m(∂_i x) ∈ H^m`, so it lies in
`H^{m+1}`; the norm bound is `‖P_{m+1} x‖² = ‖P_m x‖² + ∑_i ‖P_m ∂_i x‖²`. -/
def LerayStep : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (m : ℕ) (hm : 3 ≤ m),
    LerayAt c hc m hm → LerayAt c hc (m + 1) (hm.trans (Nat.le_succ m))

/-- `P₀` preserves `H^m` for every `m ≥ 3`. -/
def LerayLevels : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (m : ℕ) (hm : 3 ≤ m), LerayAt c hc m hm

/-- `LerayLevels` from the inductive step (the base case `m = 3` is `P₀H3CLM` itself). -/
theorem lerayLevels_of (h : LerayStep) : LerayLevels := by
  intro c hc m hm
  induction m, hm using Nat.le_induction with
  | base =>
    refine ⟨P0H3CLM hc, fun x => ?_⟩
    have hx : ∀ z : Cyl.H ℝ Cyl.Vec2 c 0 3, (Sob.W.restrict (le_refl 3) z : Cyl.H ℝ Cyl.Vec2 c 0 3) = z := by
      intro z
      apply Sob.W.value_injective
      rfl
    rw [hx, hx]
  | succ m hm ih => exact h c hc m hm ih

/-! ### The family `R_k` -/

/-- **Lemma R** (the family `R_k`, source lines 261-288; assembled from `AdvectionBilinear`
and `LerayLevels`, see `rhsFamily_of` in its own file).  For `ν > 0`, `c ≥ 1` there are smooth
maps `R_k : H^{k+5} → H^{k+3}` such that `R_0` is the level-3 right-hand side `IsRhsOp` and
`R_k` is compatible with restriction: `restrict (R_k v) = R_0 (restrict v)`.  Proof idea:
`R_k v = ν hLap v - P_{k+3} B_{k+3}(res v, res v)` with `res : H^{k+5} → H^{k+4}`;
`ContDiff` from a continuous linear map plus a bounded quadratic map
(`ContinuousLinearMap.isBoundedBilinearMap`, `IsBoundedBilinearMap.contDiff`); compatibility from
`Sob.W.value_injective` (the a.e. formula of `IsAdvectionOp` and the restriction property of
`LerayAt`; `hLap` commutes with restriction since it is built from `partialDeriv`,
`Sob.W.deriv_partialDeriv`, `Sob.W.deriv_restrict`). -/
def RhsFamily : Prop :=
  ∀ (ν c : ℝ) (_hν : 0 < ν) (hc : 0 < c) (_hc1 : 1 ≤ c),
    ∃ R : ∀ k : ℕ, Cyl.H ℝ Cyl.Vec2 c 0 (k + 2 + 3) → Cyl.H ℝ Cyl.Vec2 c 0 (k + 3),
      (∀ k : ℕ, ContDiff ℝ ∞ (R k)) ∧ IsRhsOp ν c hc (R 0) ∧
      ∀ (k : ℕ) (v : Cyl.H ℝ Cyl.Vec2 c 0 (k + 2 + 3)),
        (Sob.W.restrict (Nat.le_add_left 3 k) (R k v) : Cyl.H ℝ Cyl.Vec2 c 0 3) =
          R 0 (Sob.W.restrict (show 5 ≤ k + 2 + 3 by omega) v : Cyl.H ℝ Cyl.Vec2 c 0 5)

/-! ### Leaf statements: the level-3 identity -/

/-- **Leaf D1** (`div(w⊗w) = (w·∇)w` under the heat-divergence kernel; source lines 261-288).
For `w ∈ H^5` whose restriction to `H^3` is `P₀`-fixed (hence weakly solenoidal) and with
advection term `A = (w·∇)w`, the projected Gaussian heat-divergence response of the row tensor
`w⊗w ∈ TensorH3` at age `θ > 0` is `S(θ)P₀A` (`S = heatVecH3Semigroup`).  Proof idea:
`actualHeatDivH3Orbit` is the Gaussian-derivative convolution of the tensor (it equals `S(θ)
div` on tensors with `div ∈ H^3`; check on smooth tensors via
`actualHeatDivH3CLM_apply_ofCylSmooth`, `Lib/HeatCylinder/H3RoughOrbitContinuity.lean`, and
extend by the density `Lib/HeatCylinder/H3Density.lean` and continuity), `div(w⊗w) = A + (div w)w
= A` since `div w = 0`, and `P₀` commutes with `S` (`heatVecH3Semigroup_P0H3CLM_comm`). -/
def HeatDivIdent : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (hc1 : 1 ≤ c) (w : Cyl.H ℝ Cyl.Vec2 c 0 5)
    (A : Cyl.H ℝ Cyl.Vec2 c 0 3),
    P0H3CLM hc (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3) =
      (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3) →
    IsAdvectionTerm c w A →
    ∀ θ : ℝ, 0 < θ →
      P0H3CLM hc (HeatCylinder.actualHeatDivH3Orbit hc
          (tensorH3Bilinear hc1 (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3)
            (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3)) θ) =
        HeatCylinder.heatVecH3Semigroup (c := c) (θ := θ) hc (P0H3CLM hc A)

/-- **Lemma D** (the mild equation in semigroup form; source lines 261-288; from `HeatDivIdent`,
see `mildDuhamelStrongForm_of` in its own file).  If `u` is a mild train with an `H^5` lift `ub`
and `R0` is the level-3 right-hand side, then with `G = νΔub - R0 ub = P₀((ub·∇)ub)`,
`u(t) = S(νt)u(0) - ∫_0^t S(ν(t-r)) G(r) dr` for `t ∈ [0,T]`.  Proof idea: unfold `IsMildTrain`
(`hu.1`, `projectedNonlinearDuhamelCompactMap_apply`, `projectedHeatNonlinearityIntegral`,
`projectedHeatDuhamelOrbit`), identify the seed `projectedHeatSeedPath` with `S(νt)u(0)`
(`heatVecH3Semigroup_P0H3CLM_comm`, `hu.2.2`), use `HeatDivIdent` pointwise for `r < t`, and
`intervalIntegral.integral_of_le` / `integral_Ioc_eq_integral_Ioo`. -/
def MildDuhamelStrongForm : Prop :=
  ∀ (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (T : ℝ) (hT : 0 < T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)),
    IsMildTrain ν c T hν hc hc1 hT u →
    ∀ ub : ContinuousMap (Icc (0 : ℝ) T) (Cyl.H ℝ Cyl.Vec2 c 0 5),
      (∀ t, (Sob.W.restrict (by norm_num : 3 ≤ 5) (ub t) : Cyl.H ℝ Cyl.Vec2 c 0 3) = u t) →
      ∀ R0 : Cyl.H ℝ Cyl.Vec2 c 0 5 → Cyl.H ℝ Cyl.Vec2 c 0 3, IsRhsOp ν c hc R0 →
      ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T),
        u ⟨t, ht⟩ =
          HeatCylinder.heatVecH3Semigroup (c := c) (θ := ν * t) hc (u (compactEvolutionZero hT)) -
            ∫ r in (0 : ℝ)..t,
              HeatCylinder.heatVecH3Semigroup (c := c) (θ := ν * (t - r)) hc
                (ν • hLap c 3 (extendCompactPath hT.le ub r) - R0 (extendCompactPath hT.le ub r))

/-- **Leaf G** (the generator of the `H^3` heat semigroup contains `νΔ` on `H^5`; source lines
261-288).  For `y ∈ H^5`, `(S(νh)y - y)/h → νΔy` in `H^3` as `h → 0+`.  Proof idea: for smooth
periodic `η`-compact `y`, `S(νh)y - y = ν∫_0^h S(νσ)Δy dσ` (age derivative of the kernel,
`heatKernel2AgeDerivative_eq_spatialLaplacian`, `Lib/HeatCylinder/HeatKernelAgeLaplacian.lean:145`,
`hasDerivAt_heatVecConvolution_age`, `Lib/HeatCylinder/HeatVecAgeDerivative.lean:30`; strong
continuity of `S`); both sides are bounded in `H^3` by `C‖y‖_{H^5}` uniformly in `h ≤ 1`
(contraction `norm_heatVecH3Semigroup_le_one`), and smooth fields are dense in `H^5`
(`Lib/HeatCylinder/H3Density.lean` for `H^3`; the density of smooth `η`-compact fields in `H^5`
is part of this leaf), so the limit extends to all `y ∈ H^5` by a `3ε` argument. -/
def HeatGeneratorH5 : Prop :=
  ∀ (ν c : ℝ), 0 < ν → ∀ hc : 0 < c, ∀ y : Cyl.H ℝ Cyl.Vec2 c 0 5,
    Tendsto (fun h : ℝ => h⁻¹ •
        (HeatCylinder.heatVecH3Semigroup (c := c) (θ := ν * h) hc
          (Sob.W.restrict (by norm_num : 3 ≤ 5) y : Cyl.H ℝ Cyl.Vec2 c 0 3) -
          (Sob.W.restrict (by norm_num : 3 ≤ 5) y : Cyl.H ℝ Cyl.Vec2 c 0 3)))
      (𝓝[>] (0 : ℝ)) (𝓝 (ν • hLap c 3 y))

/-- **Leaf S** (abstract strong Duhamel; source lines 261-288, semigroup theory; no heat
equation involved).  Let `X, Y` be Banach spaces, `j, L : Y →L X` bounded, and `S : ℝ → X →L X` a
contraction family on `[0,∞)` with `S 0 = 1`, the semigroup law, and strongly continuous, whose
generator contains `L` on `j(Y)`: `(S h (j y) - j y)/h → L y` as `h → 0+` for every `y ∈ Y`.
Let `G : ℝ → X` and `v : ℝ → Y` be continuous, `T > 0`, with the mild equation
`j(v t) = S t (j(v 0)) - ∫_0^t S(t-r) G(r) dr` for `t ∈ [0,T]`.  Then
`j(v t) = j(v 0) + ∫_0^t (L(v s) - G s) ds` for `t ∈ [0,T]`.

Proof idea (all steps elementary): with `Φ(τ) = ∫_0^τ S` and `Θ_h = (S h - 1)/h`, put
`I(t) = ∫_0^t v ∈ Y` (Bochner in `Y`; `j` and `L` commute with the integral).  By the generator
property `Θ_h j(I t) → L(I t) = ∫_0^t L v`.  By the mild equation and Fubini
`∫_0^t j v = Φ(t)j(v 0) - ∫_0^t Φ(t-r)G(r) dr`, and for `z ∈ X`,
`Θ_h Φ(τ) z = h⁻¹(∫_τ^{τ+h} - ∫_0^h) S z → S(τ)z - z` by strong continuity; dominated convergence
(bound `2 sup‖G‖`) in `r` gives `Θ_h j(I t) → (S(t)x - x) - (w(t) - ∫_0^t G)` with
`w(t) = ∫_0^t S(t-r)G(r)dr`; compare the two limits. -/
def AbstractStrongDuhamel : Prop :=
  ∀ (X Y : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (j L : Y →L[ℝ] X) (S : ℝ → X →L[ℝ] X),
    (∀ θ : ℝ, 0 ≤ θ → ‖S θ‖ ≤ 1) → S 0 = ContinuousLinearMap.id ℝ X →
    (∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (S a).comp (S b) = S (a + b)) →
    (∀ x : X, Continuous fun θ : ℝ => S θ x) →
    (∀ y : Y, Tendsto (fun h : ℝ => h⁻¹ • (S h (j y) - j y)) (𝓝[>] (0 : ℝ)) (𝓝 (L y))) →
    ∀ (T : ℝ), 0 < T → ∀ (G : ℝ → X) (v : ℝ → Y), Continuous G → Continuous v →
      (∀ t ∈ Icc (0 : ℝ) T,
        j (v t) = S t (j (v 0)) - ∫ r in (0 : ℝ)..t, S (t - r) (G r)) →
      ∀ t ∈ Icc (0 : ℝ) T, j (v t) = j (v 0) + ∫ s in (0 : ℝ)..t, (L (v s) - G s)

/-- **Lemma S** (strong Duhamel for the `H^3` heat semigroup with an `H^5` solution; from
`HeatGeneratorH5` and `AbstractStrongDuhamel`, see `heatStrongDuhamel_of` in its own file).
Instantiate `AbstractStrongDuhamel` with `X = H^3`, `Y = H^5`, `j = restrict`,
`L = ν • hLap c 3`, `S θ = heatVecH3Semigroup (ν θ)` (library: `norm_heatVecH3Semigroup_le_one`,
`heatVecH3Semigroup_viscous_comp_of_nonneg`, `heatVecH3Semigroup_eq_id_of_nonpos`,
`continuous_heatVecH3Semigroup_joint`) and `v = extendCompactPath hT.le ub`. -/
def HeatStrongDuhamel : Prop :=
  ∀ (ν c : ℝ), 0 < ν → ∀ hc : 0 < c, ∀ (T : ℝ) (hT : 0 < T)
    (ub : ContinuousMap (Icc (0 : ℝ) T) (Cyl.H ℝ Cyl.Vec2 c 0 5))
    (G : ContinuousMap ℝ (VectorH3 c)),
    (∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T),
      (Sob.W.restrict (by norm_num : 3 ≤ 5) (ub ⟨t, ht⟩) : Cyl.H ℝ Cyl.Vec2 c 0 3) =
        HeatCylinder.heatVecH3Semigroup (c := c) (θ := ν * t) hc
            (Sob.W.restrict (by norm_num : 3 ≤ 5) (ub (compactEvolutionZero hT)) :
              Cyl.H ℝ Cyl.Vec2 c 0 3) -
          ∫ r in (0 : ℝ)..t, HeatCylinder.heatVecH3Semigroup (c := c) (θ := ν * (t - r)) hc (G r)) →
    ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T),
      (Sob.W.restrict (by norm_num : 3 ≤ 5) (ub ⟨t, ht⟩) : Cyl.H ℝ Cyl.Vec2 c 0 3) =
        (Sob.W.restrict (by norm_num : 3 ≤ 5) (ub (compactEvolutionZero hT)) :
            Cyl.H ℝ Cyl.Vec2 c 0 3) +
          ∫ s in (0 : ℝ)..t, (ν • hLap c 3 (extendCompactPath hT.le ub s) - G s)

/-- **The level-3 identity** (source lines 261-288): a mild train with an `H^5` lift is a strong
solution in `H^3`, `u(t) = u(0) + ∫_0^t R0(ub s) ds`. -/
def MildCoreIdentity : Prop :=
  ∀ (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (T : ℝ) (hT : 0 < T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)),
    IsMildTrain ν c T hν hc hc1 hT u →
    ∀ ub : ContinuousMap (Icc (0 : ℝ) T) (Cyl.H ℝ Cyl.Vec2 c 0 5),
      (∀ t, (Sob.W.restrict (by norm_num : 3 ≤ 5) (ub t) : Cyl.H ℝ Cyl.Vec2 c 0 3) = u t) →
      ∀ R0 : Cyl.H ℝ Cyl.Vec2 c 0 5 → Cyl.H ℝ Cyl.Vec2 c 0 3, IsRhsOp ν c hc R0 →
      ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T),
        u ⟨t, ht⟩ = u (compactEvolutionZero hT) +
          ∫ s in (0 : ℝ)..t, R0 (extendCompactPath hT.le ub s)

/-! ### The conditional theorems -/

/-- `MildCoreIdentity` from the semigroup form of the mild equation and the strong Duhamel lemma:
with `G = νΔub - R0 ub` (continuous because `R0` is), `νΔub - G = R0 ub`. -/
theorem mildCoreIdentity_of (hD : MildDuhamelStrongForm) (hS : HeatStrongDuhamel) :
    MildCoreIdentity := by
  intro ν c hν hc hc1 T hT u hu ub hub R0 hR0 t ht
  let ub' : ContinuousMap ℝ (Cyl.H ℝ Cyl.Vec2 c 0 5) := extendCompactPath hT.le ub
  let G : ContinuousMap ℝ (VectorH3 c) :=
    ⟨fun r => ν • hLap c 3 (ub' r) - R0 (ub' r),
      ((ν • hLap c 3).continuous.comp ub'.continuous).sub (hR0.1.comp ub'.continuous)⟩
  have hmild := hD ν c hν hc hc1 T hT u hu ub hub R0 hR0
  have h1 : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T),
      (Sob.W.restrict (by norm_num : 3 ≤ 5) (ub ⟨t, ht⟩) : Cyl.H ℝ Cyl.Vec2 c 0 3) =
        HeatCylinder.heatVecH3Semigroup (c := c) (θ := ν * t) hc
            (Sob.W.restrict (by norm_num : 3 ≤ 5) (ub (compactEvolutionZero hT)) :
              Cyl.H ℝ Cyl.Vec2 c 0 3) -
          ∫ r in (0 : ℝ)..t,
            HeatCylinder.heatVecH3Semigroup (c := c) (θ := ν * (t - r)) hc (G r) := by
    intro t ht
    rw [hub ⟨t, ht⟩, hub (compactEvolutionZero hT)]
    exact hmild t ht
  have h2 := hS ν c hν hc T hT ub G h1 t ht
  rw [hub ⟨t, ht⟩, hub (compactEvolutionZero hT)] at h2
  rw [h2]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  change ν • hLap c 3 (ub' s) - (ν • hLap c 3 (ub' s) - R0 (ub' s)) = R0 (ub' s)
  exact sub_sub_cancel _ _

/-- **`MildPathDerivRhs` from the leaves.**  Level reduction (restriction is injective) turns the
level-3 identity `MildCoreIdentity` into the integral identity at level `k + 3`, and the
fundamental theorem of calculus for the continuous integrand `R_k ∘ ukB` gives the derivative at
every point of `[0,T]`, one-sided at the end points. -/
theorem mildPathDerivRhs_of (hR : RhsFamily) (hD : MildDuhamelStrongForm)
    (hS : HeatStrongDuhamel) : MildPathDerivRhs := by
  have hCore := mildCoreIdentity_of hD hS
  intro ν c hν hc hc1
  obtain ⟨R, hRsm, hRop, hRcompat⟩ := hR ν c hν hc hc1
  refine ⟨R, hRsm, ?_⟩
  intro T hT u hu k ukA ukB hA hB t ht
  -- the level-5 lift of `u`
  let ub : ContinuousMap (Icc (0 : ℝ) T) (Cyl.H ℝ Cyl.Vec2 c 0 5) :=
    ⟨fun s => (Sob.W.restrict (show 5 ≤ k + 2 + 3 by omega) (ukB s) : Cyl.H ℝ Cyl.Vec2 c 0 5),
      (Sob.W.restrict (show 5 ≤ k + 2 + 3 by omega) :
        Cyl.H ℝ Cyl.Vec2 c 0 (k + 2 + 3) →L[ℝ] Cyl.H ℝ Cyl.Vec2 c 0 5).continuous.comp
          ukB.continuous⟩
  have hub : ∀ s, (Sob.W.restrict (by norm_num : 3 ≤ 5) (ub s) : Cyl.H ℝ Cyl.Vec2 c 0 3) = u s := by
    intro s
    rw [← hB s]
    exact restrict_restrict c (by norm_num) (show 5 ≤ k + 2 + 3 by omega)
      (Nat.le_add_left 3 (k + 2)) (ukB s)
  have hid := hCore ν c hν hc hc1 T hT u hu ub hub (R 0) hRop
  let g : ℝ → Cyl.H ℝ Cyl.Vec2 c 0 (k + 3) := fun r => R k (extendCompactPath hT.le ukB r)
  have hg : Continuous g := (hRsm k).continuous.comp (extendCompactPath hT.le ukB).continuous
  have hrest0 : (Sob.W.restrict (Nat.le_add_left 3 k) (extendCompactPath hT.le ukA 0) :
      Cyl.H ℝ Cyl.Vec2 c 0 3) = u (compactEvolutionZero hT) := by
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
    rw [extendCompactPath_apply_of_mem hT.le ukA h0]
    exact hA (compactEvolutionZero hT)
  have key : ∀ s ∈ Icc (0 : ℝ) T, extendCompactPath hT.le ukA s =
      extendCompactPath hT.le ukA 0 + ∫ r in (0 : ℝ)..s, g r := by
    intro s hs
    apply restrict_injective c (Nat.le_add_left 3 k)
    rw [map_add, hrest0]
    have hint : IntervalIntegrable g MeasureTheory.volume 0 s := hg.intervalIntegrable 0 s
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
    rw [extendCompactPath_apply_of_mem hT.le ukA hs, hA ⟨s, hs⟩, hid s hs]
    congr 1
    apply intervalIntegral.integral_congr
    intro r _
    simp only [g]
    rw [hRcompat k (extendCompactPath hT.le ukB r)]
    rfl
  have hderiv : HasDerivAt (fun s => extendCompactPath hT.le ukA 0 + ∫ r in (0 : ℝ)..s, g r)
      (g t) t :=
    ((hg.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add _
  exact (hderiv.hasDerivWithinAt).congr (fun s hs => key s hs) (key t ht)

end UnforcedLeray.Short.PartI
