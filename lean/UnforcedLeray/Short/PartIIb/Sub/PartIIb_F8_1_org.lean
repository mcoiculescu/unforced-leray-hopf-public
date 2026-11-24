import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8
import UnforcedLeray.Short.Spine.PartI

/-!
# Part II-b, organize task `PartII-b:F8/1/org`: the cylinder Oseen flow and the unit-horizon
`H¹ → H²` Duhamel smoothing (`CylinderParabolicH2Duhamel`, SP 2296–2305)

Source of record: `the November 2 reference manuscript`
(SP), lines 2296–2305:

  "Local smoothing introduces no further exponential. To check this, differentiate
  (short-bg:body-eq) homogeneously twice. Incompressibility, orthogonality of `P_0`, and
  (short-bg:train-uniform) give `E_j' + ν E_{j+1} ≤ C ∑_{i ≤ j} E_i`, `j ≤ 2`. Multiplication by
  successive powers of `ν(t - s)` and summation gives `H¹ → H²` norm `C [ν(t - s)]^{-1/2}` for
  `t - s ≤ 1`. On `0 < s < 2`, Duhamel and (short-bg:hardy) give the weighted
  `L^p(s^{13/8} ds; H²)` estimate. For `s ≥ 2` use Duhamel only on `[s - 1, s]`; weights at `s`
  and `s - r`, `0 < r < 1`, are comparable."

The equation is (short-bg:body-eq), SP 2213–2217: `z_s - νΔz + P_0(v·∇z + z·∇v) = g` on the
periodic cylinder `C_c = (ℝ/cℤ) × ℝ`; the train bounds are (short-bg:train-uniform), SP 2052–2053.

## Objects (namespace `F8U`)

* `pd i w`, `ps w`, `pdIter α w`: classical spatial (`∂_q`, `∂_η`) and age derivatives of a smooth
  profile; `slice w τ = w(τ, ·)`; `cellL2 c f = ‖f‖_{L²(cell)}`; `cylH1 c u uq uη` the `H¹(C_c)` norm
  (`sliceH1Norm` at one slice).
* `IsCylH1Datum c u uq uη`: `u ∈ H¹_σ(C_c)` (weak cylinder derivatives `uq, uη`, weakly solenoidal).
* `homResidual p w = ∂_s w - νΔw + B_v w` and `IsCylOseenOrbit p σ w u uq uη`: the smooth solution on
  `(σ, σ + 2)` of the homogeneous equation (residual orthogonal to `L²_σ(C_c)`: "orthogonality of
  `P_0`") with `H¹` initial value `u` at `σ`; this is the orbit `S_0(·, σ)u` of the periodic-cylinder
  Oseen propagator of SP 2296–2301.
* `CylOseenFlowBound A p`: orbits exist from every `H¹_σ` datum and every orbit obeys
  `‖S_0(t,σ)u‖_{H¹} ≤ A ‖u‖_{H¹}` and `‖D² S_0(t,σ)u‖ ≤ A [ν(t - σ)]^{-1/2} ‖u‖_{H¹}` on `t - σ ≤ 1`.
* Section 1 copies (namespace `F8U`) the ODE lemmas of `Tasks/LocalSmoothing/ParabolicH2Duhamel.lean`
  (`parabolic_multiplier_gronwall`, `parabolic_E2_le_of_hierarchy`,
  `parabolic_sqrt_E2_le_of_hierarchy`): the age-weighted Lyapunov functional
  `Ψ = E₁ + ν(τ - s)E₂` of SP 2300 ("multiplication by successive powers of `ν(t - s)`").

## Leaves (shared namespace)

1. `CylOseenOrbitSmoothing` (`PartII-b:F8/1/org/1`, SP 2296–2301): energy hierarchy for orbits and
   the `H¹ → H²` bound.
2. `CylOseenOrbitExists` (`PartII-b:F8/1/org/2`, SP 2213–2217, 2296–2297): existence of orbits.
3. `MeridionalDuhamelRegularity` (`PartII-b:F8/1/org/3`, SP 2301–2305): Duhamel on `(0, s]` and on
   `[s - 1, s]` for the weak meridional correction.
4. `MeridionalLinearVersion` (`PartII-b:F8/1/org/4`): linear strongly measurable versions.

## Assembly

`cylinderParabolicH2Duhamel_of_org` proves `CylinderParabolicH2Duhamel` from `TrainUniform`
(SP 2052–2053) and the four leaves, with the unit-to-band conversion of SP 2302–2305 on
`1 < s ≤ p.H` (`p.H = Σ/ν ≥ 1` since `ν ≤ Σ`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace F8U

/-! ## 0. Objects: derivatives, slices, the `H¹_σ(C_c)` datum and the Oseen orbit -/

/-- The spatial chart directions of `Coord = (s, (q, η))`: `0 ↦ ∂_q`, `1 ↦ ∂_η`. -/
def sdir : Fin 2 → Coord := ![(0, (1, 0)), (0, (0, 1))]

/-- Classical spatial partial derivative `∂_q w` (`i = 0`) or `∂_η w` (`i = 1`). -/
def pd (i : Fin 2) (w : CProf) (x : Coord) : CMerid := fderiv ℝ w x (sdir i)

/-- Classical age derivative `∂_s w`. -/
def ps (w : CProf) (x : Coord) : CMerid := fderiv ℝ w x (1, (0, 0))

/-- Iterated spatial derivative `∂^α w = ∂_{α 0} (∂_{α 1} ⋯ w)` for a multi-index `α : Fin n → Fin 2`. -/
def pdIter : {n : ℕ} → (Fin n → Fin 2) → CProf → CProf
  | 0, _, w => w
  | n + 1, α, w => pd (α 0) (pdIter (n := n) (Fin.tail α) w)

/-- The slice `y ↦ w(τ, y)` at age `τ`. -/
def slice (w : CProf) (τ : ℝ) : B0579.Plane → CMerid := fun y => w (τ, y)

/-- The `L²` norm over the cell `[-c/2, c/2) × ℝ` of `C_c`. -/
def cellL2 (c : ℝ) (f : B0579.Plane → CMerid) : ℝ≥0∞ :=
  eLpNorm f 2 (volume.restrict (B0579.cell c))

/-- The `H¹(C_c)` norm `‖u‖ + ‖u_q‖ + ‖u_η‖` (`sliceH1Norm` at a single slice). -/
def cylH1 (c : ℝ) (u uq uη : B0579.Plane → CMerid) : ℝ≥0∞ :=
  cellL2 c u + cellL2 c uq + cellL2 c uη

/-- Weak solenoidality on `C_c`: `∫_cell (f_0 ∂_q ψ + f_1 ∂_η ψ) = 0` for every cylinder test `ψ`
(the space `L²_σ(C_c)` of SP 2213–2217 on which `P_0` is the identity). -/
def IsCellSolenoidal (c : ℝ) (f : B0579.Plane → CMerid) : Prop :=
  ∀ ψ, B0579.IsCylTest c ψ →
    IntegrableOn (fun y => f y 0 * (B0579.pd 0 ψ y : ℂ) + f y 1 * (B0579.pd 1 ψ y : ℂ))
        (B0579.cell c) ∧
      ∫ y in B0579.cell c, (f y 0 * (B0579.pd 0 ψ y : ℂ) + f y 1 * (B0579.pd 1 ψ y : ℂ)) = 0

/-- An `H¹_σ(C_c)` datum: `u, u_q, u_η ∈ L²(cell)`, `u_q, u_η` the weak cylinder derivatives of `u`
(tested against `c`-periodic tests), and `u` weakly solenoidal (SP 2296–2301: the data of
`S_0(t, s)`). -/
structure IsCylH1Datum (c : ℝ) (u uq uη : B0579.Plane → CMerid) : Prop where
  weak_q : ∀ k : Fin 2, IIIa.HasWeakCellDerivC c 0 (fun y => u y k) (fun y => uq y k)
  weak_eta : ∀ k : Fin 2, IIIa.HasWeakCellDerivC c 1 (fun y => u y k) (fun y => uη y k)
  solenoidal : IsCellSolenoidal c u
  memL2 : MemLp u 2 (volume.restrict (B0579.cell c)) ∧
    MemLp uq 2 (volume.restrict (B0579.cell c)) ∧ MemLp uη 2 (volume.restrict (B0579.cell c))

/-- The homogeneous meridional residual `∂_s w - ν(∂_q² + ∂_η²) w + (v·∇w + w·∇v)` of
(short-bg:body-eq) (SP 2216) with `g = 0`, `v = p.train.v`. -/
def homResidual (p : Params) (w : CProf) (x : Coord) : CMerid :=
  ps w x - p.ν • (pd 0 (pd 0 w) x + pd 1 (pd 1 w) x) + flatBv p.train w (pd 0 w) (pd 1 w) x

/-- **The orbit `t ↦ S_0(t, σ)u` of the periodic-cylinder Oseen propagator** (SP 2296–2301, equation
(short-bg:body-eq) of SP 2216 with `g = 0`): on `(σ, σ + 2) × ℝ²` the profile `w` is smooth,
`c`-periodic in `q` and divergence free; its spatial derivatives up to order four and the age
derivatives of its spatial derivatives up to order two have `L²(cell)` slices depending continuously
on the age; the residual `∂_s w - νΔw + B_v w` is orthogonal to `L²_σ(C_c)` at every age
("orthogonality of `P_0`", i.e. it is a pressure gradient); and `(w, ∂_q w, ∂_η w)(t) → (u, uq, uη)`
in `L²(cell)` as `t → σ⁺`. -/
structure IsCylOseenOrbit (p : Params) (σ : ℝ) (w : CProf) (u uq uη : B0579.Plane → CMerid) :
    Prop where
  smooth : ContDiffOn ℝ ∞ w (Ioo σ (σ + 2) ×ˢ univ)
  periodic : ∀ x : Coord, x.1 ∈ Ioo σ (σ + 2) → w (qShift p.c x) = w x
  div_free : ∀ x : Coord, x.1 ∈ Ioo σ (σ + 2) → pd 0 w x 0 + pd 1 w x 1 = 0
  memL2 : ∀ τ ∈ Ioo σ (σ + 2), ∀ n : ℕ, n ≤ 4 → ∀ α : Fin n → Fin 2,
    MemLp (slice (pdIter α w) τ) 2 (volume.restrict (B0579.cell p.c))
  memL2_s : ∀ τ ∈ Ioo σ (σ + 2), ∀ n : ℕ, n ≤ 2 → ∀ α : Fin n → Fin 2,
    MemLp (slice (ps (pdIter α w)) τ) 2 (volume.restrict (B0579.cell p.c))
  cont : ∀ τ ∈ Ioo σ (σ + 2), ∀ n : ℕ, n ≤ 4 → ∀ α : Fin n → Fin 2,
    Tendsto (fun t => cellL2 p.c (fun y => pdIter α w (t, y) - pdIter α w (τ, y))) (𝓝 τ) (𝓝 0)
  cont_s : ∀ τ ∈ Ioo σ (σ + 2), ∀ n : ℕ, n ≤ 2 → ∀ α : Fin n → Fin 2,
    Tendsto (fun t => cellL2 p.c (fun y => ps (pdIter α w) (t, y) - ps (pdIter α w) (τ, y)))
      (𝓝 τ) (𝓝 0)
  projected : ∀ τ ∈ Ioo σ (σ + 2), ∀ φ : B0579.Plane → CMerid,
    MemLp φ 2 (volume.restrict (B0579.cell p.c)) → IsCellSolenoidal p.c φ →
      ∫ y in B0579.cell p.c, inner ℂ (φ y) (homResidual p w (τ, y)) = 0
  initial : Tendsto (fun t => cylH1 p.c (fun y => w (t, y) - u y) (fun y => pd 0 w (t, y) - uq y)
      (fun y => pd 1 w (t, y) - uη y)) (𝓝[>] σ) (𝓝 0)

/-- **Unit-horizon bounds of the cylinder Oseen flow with constant `A`** (SP 2296–2301): from every
`H¹_σ` datum at every age `σ ≥ 0` an orbit exists, and every orbit obeys, for `0 < t - σ ≤ 1`,
`‖S_0(t,σ)u‖_{H¹} ≤ A ‖u‖_{H¹}` and `∑_{i,j} ‖∂_i∂_j S_0(t,σ)u‖_{L²} ≤ A [ν(t-σ)]^{-1/2} ‖u‖_{H¹}`. -/
def CylOseenFlowBound (A : ℝ) (p : Params) : Prop :=
  ∀ σ : ℝ, 0 ≤ σ → ∀ u uq uη : B0579.Plane → CMerid, IsCylH1Datum p.c u uq uη →
    (∃ w : CProf, IsCylOseenOrbit p σ w u uq uη) ∧
    ∀ w : CProf, IsCylOseenOrbit p σ w u uq uη → ∀ t ∈ Ioc σ (σ + 1),
      cylH1 p.c (slice w t) (slice (pd 0 w) t) (slice (pd 1 w) t) ≤
          ENNReal.ofReal A * cylH1 p.c u uq uη ∧
        ∑ i : Fin 2, ∑ j : Fin 2, cellL2 p.c (slice (pd i (pd j w)) t) ≤
          ENNReal.ofReal (A * p.ν ^ (-1 / 2 : ℝ) * (t - σ) ^ (-1 / 2 : ℝ)) * cylH1 p.c u uq uη

/-! ## 1. Parabolic `H¹ → H²` smoothing from the cylinder energy hierarchy (SP 2299–2301) -/

/-- Age-weighted parabolic Lyapunov functional `Ψ(τ) = E₁(τ) + ν (τ - s) E₂(τ)` (SP 2300:
"Multiplication by successive powers of `ν(t - s)` and summation"). -/
def parabolicLyapunov (ν s : ℝ) (E₁ E₂ : ℝ → ℝ) (τ : ℝ) : ℝ :=
  E₁ τ + ν * (τ - s) * E₂ τ

/-- Right derivative of `parabolicLyapunov ν s E₁ E₂` at `τ`. -/
def parabolicLyapunovDeriv (ν s : ℝ) (E₂ E₁' E₂' : ℝ → ℝ) (τ : ℝ) : ℝ :=
  E₁' τ + (ν * E₂ τ + ν * (τ - s) * E₂' τ)

theorem hasDerivWithinAt_parabolicLyapunov {ν s τ : ℝ} {E₁ E₂ E₁' E₂' : ℝ → ℝ}
    (hE₁ : HasDerivWithinAt E₁ (E₁' τ) (Ici τ) τ)
    (hE₂ : HasDerivWithinAt E₂ (E₂' τ) (Ici τ) τ) :
    HasDerivWithinAt (parabolicLyapunov ν s E₁ E₂)
      (parabolicLyapunovDeriv ν s E₂ E₁' E₂' τ) (Ici τ) τ := by
  unfold parabolicLyapunov parabolicLyapunovDeriv
  have hlin : HasDerivWithinAt (fun r : ℝ => ν * (r - s)) ν (Ici τ) τ := by
    have h1 : HasDerivAt (fun r : ℝ => r - s) 1 τ := (hasDerivAt_id τ).sub_const s
    simpa using (h1.const_mul ν).hasDerivWithinAt
  have hprod : HasDerivWithinAt (fun r : ℝ => (ν * (r - s)) * E₂ r)
      (ν * E₂ τ + (ν * (τ - s)) * E₂' τ) (Ici τ) τ :=
    hlin.mul hE₂
  exact hE₁.add hprod

/-- Pointwise differential inequality `Ψ'(τ) ≤ 2 K Ψ(τ)` from the hierarchy
`E₁'(τ) + ν E₂(τ) ≤ K E₁(τ)` and `E₂'(τ) + ν E₃(τ) ≤ K (E₁(τ) + E₂(τ))`
with `0 ≤ E₁(τ) ≤ E₂(τ)` and `0 ≤ E₃(τ)` (SP 2299–2301). -/
theorem parabolicLyapunovDeriv_le {ν K s τ : ℝ} {E₁ E₂ E₃ E₁' E₂' : ℝ → ℝ}
    (hν : 0 ≤ ν) (hK : 0 ≤ K) (hsτ : s ≤ τ)
    (hE₁_nn : 0 ≤ E₁ τ) (hE₁₂ : E₁ τ ≤ E₂ τ) (hE₃_nn : 0 ≤ E₃ τ)
    (h1 : E₁' τ + ν * E₂ τ ≤ K * E₁ τ)
    (h2 : E₂' τ + ν * E₃ τ ≤ K * (E₁ τ + E₂ τ)) :
    parabolicLyapunovDeriv ν s E₂ E₁' E₂' τ ≤
      2 * K * parabolicLyapunov ν s E₁ E₂ τ := by
  unfold parabolicLyapunovDeriv parabolicLyapunov
  have hν_ts : 0 ≤ ν * (τ - s) := mul_nonneg hν (sub_nonneg.mpr hsτ)
  have hE₂' : E₂' τ ≤ 2 * K * E₂ τ := by
    have hνE₃ : 0 ≤ ν * E₃ τ := mul_nonneg hν hE₃_nn
    have hKE : K * (E₁ τ + E₂ τ) ≤ 2 * K * E₂ τ := by
      have : E₁ τ + E₂ τ ≤ 2 * E₂ τ := by linarith
      calc K * (E₁ τ + E₂ τ) ≤ K * (2 * E₂ τ) := mul_le_mul_of_nonneg_left this hK
        _ = 2 * K * E₂ τ := by ring
    linarith
  have hmul : ν * (τ - s) * E₂' τ ≤ ν * (τ - s) * (2 * K * E₂ τ) :=
    mul_le_mul_of_nonneg_left hE₂' hν_ts
  have hKE₁ : K * E₁ τ ≤ 2 * K * E₁ τ := by
    have : 0 ≤ K * E₁ τ := mul_nonneg hK hE₁_nn
    linarith
  linarith

/-- **Gronwall bound for the parabolic Lyapunov functional `Ψ(τ) = E₁(τ) + ν(τ - s) E₂(τ)`**
(SP 2299–2301): if `E₁, E₂` are continuous on `[s, t]` and satisfy the cylinder energy hierarchy on
`[s, t)`, then `Ψ(t) ≤ e^{2 K (t - s)} E₁(s)`. -/
theorem parabolic_multiplier_gronwall {ν K s t : ℝ} {E₁ E₂ E₃ E₁' E₂' : ℝ → ℝ}
    (hν : 0 ≤ ν) (hK : 0 ≤ K) (hst : s ≤ t)
    (hcont₁ : ContinuousOn E₁ (Icc s t))
    (hcont₂ : ContinuousOn E₂ (Icc s t))
    (hE₁_nn : ∀ τ ∈ Ico s t, 0 ≤ E₁ τ)
    (hE₁₂ : ∀ τ ∈ Ico s t, E₁ τ ≤ E₂ τ)
    (hE₃_nn : ∀ τ ∈ Ico s t, 0 ≤ E₃ τ)
    (hderiv₁ : ∀ τ ∈ Ico s t, HasDerivWithinAt E₁ (E₁' τ) (Ici τ) τ)
    (hderiv₂ : ∀ τ ∈ Ico s t, HasDerivWithinAt E₂ (E₂' τ) (Ici τ) τ)
    (hineq₁ : ∀ τ ∈ Ico s t, E₁' τ + ν * E₂ τ ≤ K * E₁ τ)
    (hineq₂ : ∀ τ ∈ Ico s t, E₂' τ + ν * E₃ τ ≤ K * (E₁ τ + E₂ τ)) :
    parabolicLyapunov ν s E₁ E₂ t ≤ Real.exp (2 * K * (t - s)) * E₁ s := by
  let Ψ := parabolicLyapunov ν s E₁ E₂
  let Ψ' := parabolicLyapunovDeriv ν s E₂ E₁' E₂'
  let h : ℝ → ℝ := fun τ => Real.exp (-(2 * K) * τ)
  let g : ℝ → ℝ := fun τ => Ψ τ * h τ
  let g' : ℝ → ℝ := fun τ => Ψ' τ * h τ + Ψ τ * (h τ * (-(2 * K)))
  have hh : ∀ τ : ℝ, HasDerivAt h (h τ * (-(2 * K))) τ := by
    intro τ
    have h1 : HasDerivAt (fun y : ℝ => -(2 * K) * y) (-(2 * K)) τ := by
      simpa using (hasDerivAt_id τ).const_mul (-(2 * K))
    exact h1.exp
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun τ => (hh τ).continuousAt
  have hΨ_cont : ContinuousOn Ψ (Icc s t) := by
    unfold Ψ parabolicLyapunov
    refine hcont₁.add ?_
    exact (continuousOn_const.mul (continuousOn_id.sub continuousOn_const)).mul hcont₂
  have hg_cont : ContinuousOn g (Icc s t) := hΨ_cont.mul hhc.continuousOn
  have hg' : ∀ τ ∈ Ico s t, HasDerivWithinAt g (g' τ) (Ici τ) τ := by
    intro τ hτ
    exact (hasDerivWithinAt_parabolicLyapunov (hderiv₁ τ hτ) (hderiv₂ τ hτ)).mul
      (hh τ).hasDerivWithinAt
  have hbound : ∀ τ ∈ Ico s t, g' τ ≤ 0 := by
    intro τ hτ
    have hΨ'_le := parabolicLyapunovDeriv_le hν hK hτ.1 (hE₁_nn τ hτ) (hE₁₂ τ hτ)
      (hE₃_nn τ hτ) (hineq₁ τ hτ) (hineq₂ τ hτ)
    have hpos : 0 < h τ := Real.exp_pos _
    have hkey : g' τ = h τ * (Ψ' τ - 2 * K * Ψ τ) := by
      dsimp [g']
      ring
    rw [hkey]
    exact mul_nonpos_of_nonneg_of_nonpos hpos.le (by linarith)
  have hgt := image_le_of_deriv_right_le_deriv_boundary (f := g) (f' := g') (a := s) (b := t)
    hg_cont hg' (B := fun _ => g s) (B' := fun _ => 0) le_rfl continuousOn_const
    (fun τ _ => hasDerivWithinAt_const τ (Ici τ) (g s)) hbound
  have hfin : g t ≤ g s := hgt ⟨hst, le_rfl⟩
  have hΨs : Ψ s = E₁ s := by
    unfold Ψ parabolicLyapunov
    ring
  have hexp1 : Real.exp (-(2 * K) * t) * Real.exp (2 * K * t) = 1 := by
    rw [← Real.exp_add, show -(2 * K) * t + 2 * K * t = 0 by ring, Real.exp_zero]
  have hexp2 : Real.exp (2 * K * (t - s)) = Real.exp (-(2 * K) * s) * Real.exp (2 * K * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfin' : Ψ t * Real.exp (-(2 * K) * t) ≤ E₁ s * Real.exp (-(2 * K) * s) := by
    simpa [g, h, hΨs] using hfin
  calc Ψ t
      = (Ψ t * Real.exp (-(2 * K) * t)) * Real.exp (2 * K * t) := by
        rw [mul_assoc, hexp1, mul_one]
    _ ≤ (E₁ s * Real.exp (-(2 * K) * s)) * Real.exp (2 * K * t) :=
        mul_le_mul_of_nonneg_right hfin' (Real.exp_pos _).le
    _ = Real.exp (2 * K * (t - s)) * E₁ s := by
        rw [hexp2]
        ring

/-- **Squared `H¹ → H²` smoothing bound** (SP 2299–2301): for `0 < ν` and `s < t`,
`E₂(t) ≤ (ν (t - s))⁻¹ e^{2 K (t - s)} E₁(s)`. -/
theorem parabolic_E2_le_of_hierarchy {ν K s t : ℝ} {E₁ E₂ E₃ E₁' E₂' : ℝ → ℝ}
    (hν : 0 < ν) (hK : 0 ≤ K) (hst : s < t)
    (hcont₁ : ContinuousOn E₁ (Icc s t))
    (hcont₂ : ContinuousOn E₂ (Icc s t))
    (hE₁_nn : ∀ τ ∈ Icc s t, 0 ≤ E₁ τ)
    (hE₁₂ : ∀ τ ∈ Ico s t, E₁ τ ≤ E₂ τ)
    (hE₃_nn : ∀ τ ∈ Ico s t, 0 ≤ E₃ τ)
    (hderiv₁ : ∀ τ ∈ Ico s t, HasDerivWithinAt E₁ (E₁' τ) (Ici τ) τ)
    (hderiv₂ : ∀ τ ∈ Ico s t, HasDerivWithinAt E₂ (E₂' τ) (Ici τ) τ)
    (hineq₁ : ∀ τ ∈ Ico s t, E₁' τ + ν * E₂ τ ≤ K * E₁ τ)
    (hineq₂ : ∀ τ ∈ Ico s t, E₂' τ + ν * E₃ τ ≤ K * (E₁ τ + E₂ τ)) :
    E₂ t ≤ (ν * (t - s))⁻¹ * Real.exp (2 * K * (t - s)) * E₁ s := by
  have hgron := parabolic_multiplier_gronwall hν.le hK hst.le hcont₁ hcont₂
    (fun τ hτ => hE₁_nn τ ⟨hτ.1, hτ.2.le⟩) hE₁₂ hE₃_nn hderiv₁ hderiv₂ hineq₁ hineq₂
  have hE₁t : 0 ≤ E₁ t := hE₁_nn t ⟨hst.le, le_rfl⟩
  have hle : ν * (t - s) * E₂ t ≤ Real.exp (2 * K * (t - s)) * E₁ s := by
    unfold parabolicLyapunov at hgron
    linarith
  have hpos : 0 < ν * (t - s) := mul_pos hν (sub_pos.mpr hst)
  calc E₂ t
      = (ν * (t - s))⁻¹ * (ν * (t - s) * E₂ t) := by
        rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
    _ ≤ (ν * (t - s))⁻¹ * (Real.exp (2 * K * (t - s)) * E₁ s) :=
        mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hpos.le)
    _ = (ν * (t - s))⁻¹ * Real.exp (2 * K * (t - s)) * E₁ s := by ring

/-- **Norm `H¹ → H²` smoothing bound on `0 < t - s ≤ 1`** (SP 2300–2301:
"gives `H¹ → H²` norm `C [ν(t - s)]^{-1/2}` for `t - s ≤ 1`"):
`√(E₂(t)) ≤ e^K · ν^{-1/2} · (t - s)^{-1/2} · √(E₁(s))`. -/
theorem parabolic_sqrt_E2_le_of_hierarchy {ν K s t : ℝ} {E₁ E₂ E₃ E₁' E₂' : ℝ → ℝ}
    (hν : 0 < ν) (hK : 0 ≤ K) (hst : s < t) (ht1 : t - s ≤ 1)
    (hcont₁ : ContinuousOn E₁ (Icc s t))
    (hcont₂ : ContinuousOn E₂ (Icc s t))
    (hE₁_nn : ∀ τ ∈ Icc s t, 0 ≤ E₁ τ)
    (hE₁₂ : ∀ τ ∈ Ico s t, E₁ τ ≤ E₂ τ)
    (hE₃_nn : ∀ τ ∈ Ico s t, 0 ≤ E₃ τ)
    (hderiv₁ : ∀ τ ∈ Ico s t, HasDerivWithinAt E₁ (E₁' τ) (Ici τ) τ)
    (hderiv₂ : ∀ τ ∈ Ico s t, HasDerivWithinAt E₂ (E₂' τ) (Ici τ) τ)
    (hineq₁ : ∀ τ ∈ Ico s t, E₁' τ + ν * E₂ τ ≤ K * E₁ τ)
    (hineq₂ : ∀ τ ∈ Ico s t, E₂' τ + ν * E₃ τ ≤ K * (E₁ τ + E₂ τ)) :
    Real.sqrt (E₂ t) ≤
      Real.exp K * ν ^ (-1 / 2 : ℝ) * (t - s) ^ (-1 / 2 : ℝ) * Real.sqrt (E₁ s) := by
  have hE₂ := parabolic_E2_le_of_hierarchy hν hK hst hcont₁ hcont₂
    hE₁_nn hE₁₂ hE₃_nn hderiv₁ hderiv₂ hineq₁ hineq₂
  have hts : 0 < t - s := sub_pos.mpr hst
  have hE₁s : 0 ≤ E₁ s := hE₁_nn s ⟨le_rfl, hst.le⟩
  have hexp_le : Real.exp (2 * K * (t - s)) ≤ Real.exp (2 * K) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hE₂' : E₂ t ≤ (ν * (t - s))⁻¹ * Real.exp (2 * K) * E₁ s := by
    refine hE₂.trans ?_
    have hpos : 0 ≤ (ν * (t - s))⁻¹ := inv_nonneg.mpr (mul_pos hν hts).le
    have h1 : (ν * (t - s))⁻¹ * Real.exp (2 * K * (t - s)) ≤
        (ν * (t - s))⁻¹ * Real.exp (2 * K) :=
      mul_le_mul_of_nonneg_left hexp_le hpos
    exact mul_le_mul_of_nonneg_right h1 hE₁s
  have hsqrt := Real.sqrt_le_sqrt hE₂'
  have hpos_νts : 0 ≤ (ν * (t - s))⁻¹ := inv_nonneg.mpr (mul_pos hν hts).le
  have hpos_exp : 0 ≤ Real.exp (2 * K) := (Real.exp_pos _).le
  rw [Real.sqrt_mul (mul_nonneg hpos_νts hpos_exp), Real.sqrt_mul hpos_νts] at hsqrt
  have hsqrt_exp : Real.sqrt (Real.exp (2 * K)) = Real.exp K := by
    rw [show 2 * K = K + K by ring, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos K).le]
  have hsqrt_inv : Real.sqrt ((ν * (t - s))⁻¹) = ν ^ (-1 / 2 : ℝ) * (t - s) ^ (-1 / 2 : ℝ) := by
    rw [Real.sqrt_inv, Real.sqrt_mul hν.le, mul_inv,
      Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_neg hν.le, ← Real.rpow_neg hts.le]
    ring_nf
  rw [hsqrt_exp, hsqrt_inv] at hsqrt
  linarith


/-! ## 2. Elementary helpers of the assembly (train transport, change of variables, constants) -/

/-- Transport of the uniform train bound along `c = c'` (here `p.c = ν⁻² = Train.per ν`). -/
theorem train_bound_transport {ν c c' C : ℝ} (h : c = c') (T : B0140.TrainSol ν c)
    (H : ∀ T' : B0140.TrainSol ν c', UnforcedLeray.Short.PartI.IsBUCTrain T' →
      ∀ s : ℝ, 0 ≤ s → ∀ j : ℕ, j ≤ 3 → ∀ z, ‖iteratedFDeriv ℝ j (T'.v s) z‖ ≤ C)
    (hT : UnforcedLeray.Short.PartI.IsBUCTrain T) :
    ∀ s : ℝ, 0 ≤ s → ∀ j : ℕ, j ≤ 3 → ∀ z, ‖iteratedFDeriv ℝ j (T.v s) z‖ ≤ C := by
  subst h
  exact H T hT

/-- Change of variables `t = s - r`: `∫_{(0,1]} H(r) dr = ∫_{[s-1,s)} H(s - t) dt`. -/
theorem lintegral_Ioc_zero_one_sub (s : ℝ) (H : ℝ → ℝ≥0∞) :
    ∫⁻ r in Ioc (0 : ℝ) 1, H r = ∫⁻ t in Ico (s - 1) s, H (s - t) := by
  have himg : (fun t : ℝ => s - t) '' Ico (s - 1) s = Ioc (0 : ℝ) 1 := by
    ext r
    simp only [mem_image, mem_Ico, mem_Ioc]
    constructor
    · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨hr0, hr1⟩
      exact ⟨s - r, ⟨by linarith, by linarith⟩, by ring⟩
  have hderiv : ∀ t ∈ Ico (s - 1) s,
      HasDerivWithinAt (fun u : ℝ => s - u) (-1) (Ico (s - 1) s) t := by
    intro t _
    exact ((hasDerivAt_id' t).const_sub s).hasDerivWithinAt
  have hinj : InjOn (fun u : ℝ => s - u) (Ico (s - 1) s) := (sub_right_injective).injOn
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ico hderiv hinj]
  simp

/-- For `1 < s`: `∫_0^1 r^{-1/2} G(s - r) dr ≤ ∫_0^s (s - t)^{-1/2} G(t) dt` (SP 2304–2305). -/
theorem unit_duhamel_le_full {s : ℝ} (hs1 : 1 < s) (G : ℝ → ℝ≥0∞) :
    ∫⁻ r in Ioc (0 : ℝ) 1, ENNReal.ofReal (r ^ (-1 / 2 : ℝ)) * G (s - r) ≤
      ∫⁻ t in Ioc (0 : ℝ) s, ENNReal.ofReal ((s - t) ^ (-1 / 2 : ℝ)) * G t := by
  rw [lintegral_Ioc_zero_one_sub s (fun r => ENNReal.ofReal (r ^ (-1 / 2 : ℝ)) * G (s - r))]
  simp only [sub_sub_cancel]
  refine lintegral_mono_set (fun t ht => ?_)
  simp only [mem_Ico, mem_Ioc] at ht ⊢
  exact ⟨by linarith, ht.2.le⟩

/-- On the band `0 < s ≤ Σ/ν` (`0 < ν ≤ 1`): `1 ≤ (Σ^{1/2} + 1) ν⁻¹ s^{-1/2}`. -/
theorem one_le_band {Sig ν s : ℝ} (hSig : 0 < Sig) (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hs0 : 0 < s)
    (hsH : s ≤ Sig / ν) : 1 ≤ (Sig ^ (1 / 2 : ℝ) + 1) * ν⁻¹ * s ^ (-1 / 2 : ℝ) := by
  have hsq : s ^ (1 / 2 : ℝ) ≤ (Sig / ν) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hs0.le hsH (by norm_num)
  have hprod : s ^ (1 / 2 : ℝ) * s ^ (-1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hs0]
    norm_num
  have hsn : 0 ≤ s ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
  have hdiv : (Sig / ν) ^ (1 / 2 : ℝ) ≤ (Sig ^ (1 / 2 : ℝ) + 1) * ν⁻¹ := by
    rw [Real.div_rpow hSig.le hν0.le]
    have hνh : ν ≤ ν ^ (1 / 2 : ℝ) := by
      have := Real.rpow_le_rpow_of_exponent_ge hν0 hν1 (show (1 / 2 : ℝ) ≤ 1 by norm_num)
      rwa [Real.rpow_one] at this
    have hSn : 0 ≤ Sig ^ (1 / 2 : ℝ) := Real.rpow_nonneg hSig.le _
    calc Sig ^ (1 / 2 : ℝ) / ν ^ (1 / 2 : ℝ) ≤ Sig ^ (1 / 2 : ℝ) / ν :=
          div_le_div_of_nonneg_left hSn hν0 hνh
      _ ≤ (Sig ^ (1 / 2 : ℝ) + 1) / ν := by
          apply div_le_div_of_nonneg_right _ hν0.le
          linarith
      _ = (Sig ^ (1 / 2 : ℝ) + 1) * ν⁻¹ := div_eq_mul_inv _ _
  calc (1 : ℝ) = s ^ (1 / 2 : ℝ) * s ^ (-1 / 2 : ℝ) := hprod.symm
    _ ≤ (Sig / ν) ^ (1 / 2 : ℝ) * s ^ (-1 / 2 : ℝ) := mul_le_mul_of_nonneg_right hsq hsn
    _ ≤ (Sig ^ (1 / 2 : ℝ) + 1) * ν⁻¹ * s ^ (-1 / 2 : ℝ) := mul_le_mul_of_nonneg_right hdiv hsn

/-- Absorbing the `H¹` part: `X ≤ M` and a unit-horizon `D²` bound `Y` give
`X + Y ≤ (C₁ + 1) ν^{-1/2} (M + J)`. -/
theorem unit_absorb {ν M C₁ : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hC₁ : 0 < C₁) {X Y J : ℝ≥0∞}
    (hX : X ≤ ENNReal.ofReal M)
    (hY : Y ≤ ENNReal.ofReal (C₁ * ν ^ (-1 / 2 : ℝ)) * (ENNReal.ofReal M + J)) :
    X + Y ≤ ENNReal.ofReal ((C₁ + 1) * ν ^ (-1 / 2 : ℝ)) * (ENNReal.ofReal M + J) := by
  have hνr : 1 ≤ ν ^ (-1 / 2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν0 hν1 (by norm_num)
  have hνr0 : 0 ≤ ν ^ (-1 / 2 : ℝ) := zero_le_one.trans hνr
  have hX' : X ≤ ENNReal.ofReal (ν ^ (-1 / 2 : ℝ)) * (ENNReal.ofReal M + J) := by
    calc X ≤ ENNReal.ofReal M := hX
      _ = 1 * ENNReal.ofReal M := (one_mul _).symm
      _ ≤ ENNReal.ofReal (ν ^ (-1 / 2 : ℝ)) * (ENNReal.ofReal M + J) :=
          mul_le_mul' (ENNReal.one_le_ofReal.mpr hνr) le_self_add
  calc X + Y ≤ ENNReal.ofReal (ν ^ (-1 / 2 : ℝ)) * (ENNReal.ofReal M + J) +
        ENNReal.ofReal (C₁ * ν ^ (-1 / 2 : ℝ)) * (ENNReal.ofReal M + J) := add_le_add hX' hY
    _ = ENNReal.ofReal ((C₁ + 1) * ν ^ (-1 / 2 : ℝ)) * (ENNReal.ofReal M + J) := by
        rw [← add_mul, ← ENNReal.ofReal_add hνr0 (mul_nonneg hC₁.le hνr0),
          show ν ^ (-1 / 2 : ℝ) + C₁ * ν ^ (-1 / 2 : ℝ) = (C₁ + 1) * ν ^ (-1 / 2 : ℝ) by ring]

/-- `1 ≤ (Σ^{1/2} + 1) ν⁻¹` for `0 < ν ≤ 1`, `0 < Σ`. -/
theorem one_le_band_const {Sig ν : ℝ} (hSig : 0 < Sig) (hν0 : 0 < ν) (hν1 : ν ≤ 1) :
    1 ≤ (Sig ^ (1 / 2 : ℝ) + 1) * ν⁻¹ := by
  have hS : 1 ≤ Sig ^ (1 / 2 : ℝ) + 1 := by
    have := Real.rpow_nonneg hSig.le (1 / 2 : ℝ)
    linarith
  have hνi : 1 ≤ ν⁻¹ := (one_le_inv₀ hν0).mpr hν1
  exact one_le_mul_of_one_le_of_one_le hS hνi

/-- Early unit bound on `(0, 1]` combined with the `H¹` part (target constant, `k_sm = 1`). -/
theorem early_unit_combine {ν s M C₁ Sig : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hs0 : 0 < s)
    (hs1 : s ≤ 1) (hM : 0 ≤ M) (hC₁ : 0 < C₁) (hSig : 0 < Sig) {X Y I : ℝ≥0∞}
    (hX : X ≤ ENNReal.ofReal M)
    (hY : Y ≤ ENNReal.ofReal (C₁ * ν ^ (-1 / 2 : ℝ)) *
      (ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * M) + I)) :
    X + Y ≤ ENNReal.ofReal (((C₁ + 1) * (Sig ^ (1 / 2 : ℝ) + 1) * (ν ^ 1)⁻¹) *
        ν ^ (-1 / 2 : ℝ)) * (ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * M) + I) := by
  have hsr : 1 ≤ s ^ (-1 / 2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs0 hs1 (by norm_num)
  have hνr : 1 ≤ ν ^ (-1 / 2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν0 hν1 (by norm_num)
  have hνr0 : 0 ≤ ν ^ (-1 / 2 : ℝ) := zero_le_one.trans hνr
  have hMle : M ≤ s ^ (-1 / 2 : ℝ) * M := le_mul_of_one_le_left hM hsr
  have hX' : X ≤ ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * M) :=
    hX.trans (ENNReal.ofReal_le_ofReal hMle)
  have hY' : Y ≤ ENNReal.ofReal (C₁ * ν ^ (-1 / 2 : ℝ)) *
      (ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * M) + I) := hY
  have h1 := unit_absorb hν0 hν1 hC₁ hX' hY'
  refine h1.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
  refine mul_le_mul_of_nonneg_right ?_ hνr0
  have hL := one_le_band_const hSig hν0 hν1
  have hC : 0 ≤ C₁ + 1 := by linarith
  rw [pow_one]
  calc C₁ + 1 = (C₁ + 1) * 1 := (mul_one _).symm
    _ ≤ (C₁ + 1) * ((Sig ^ (1 / 2 : ℝ) + 1) * ν⁻¹) := mul_le_mul_of_nonneg_left hL hC
    _ = (C₁ + 1) * (Sig ^ (1 / 2 : ℝ) + 1) * ν⁻¹ := by ring

/-- Unit bound on `1 < s ≤ Σ/ν` converted to the band form (SP 2302–2305: `M ≤ (Σ^{1/2}+1)ν⁻¹ s^{-1/2} M`
and `∫_0^1 r^{-1/2} G(s - r) dr ≤ ∫_0^s (s - t)^{-1/2} G(t) dt`). -/
theorem band_unit_combine {ν s M C₁ Sig : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hs1 : 1 < s)
    (hsH : s ≤ Sig / ν) (hM : 0 ≤ M) (hC₁ : 0 < C₁) (hSig : 0 < Sig) {X Y I J : ℝ≥0∞}
    (hX : X ≤ ENNReal.ofReal M)
    (hY : Y ≤ ENNReal.ofReal (C₁ * ν ^ (-1 / 2 : ℝ)) * (ENNReal.ofReal M + J))
    (hJ : J ≤ I) :
    X + Y ≤ ENNReal.ofReal (((C₁ + 1) * (Sig ^ (1 / 2 : ℝ) + 1) * (ν ^ 1)⁻¹) *
        ν ^ (-1 / 2 : ℝ)) * (ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * M) + I) := by
  have hs0 : 0 < s := zero_lt_one.trans hs1
  have hνr : 1 ≤ ν ^ (-1 / 2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν0 hν1 (by norm_num)
  have hνr0 : 0 ≤ ν ^ (-1 / 2 : ℝ) := zero_le_one.trans hνr
  have hL1 := one_le_band_const hSig hν0 hν1
  have hL0 : 0 ≤ (Sig ^ (1 / 2 : ℝ) + 1) * ν⁻¹ := zero_le_one.trans hL1
  have hband := one_le_band hSig hν0 hν1 hs0 hsH
  have hMle : M ≤ (Sig ^ (1 / 2 : ℝ) + 1) * ν⁻¹ * (s ^ (-1 / 2 : ℝ) * M) := by
    calc M = 1 * M := (one_mul M).symm
      _ ≤ ((Sig ^ (1 / 2 : ℝ) + 1) * ν⁻¹ * s ^ (-1 / 2 : ℝ)) * M :=
          mul_le_mul_of_nonneg_right hband hM
      _ = (Sig ^ (1 / 2 : ℝ) + 1) * ν⁻¹ * (s ^ (-1 / 2 : ℝ) * M) := by ring
  have hstep1 := unit_absorb hν0 hν1 hC₁ hX hY
  have hstep2 : ENNReal.ofReal M + J ≤ ENNReal.ofReal ((Sig ^ (1 / 2 : ℝ) + 1) * ν⁻¹) *
      (ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * M) + I) := by
    rw [mul_add]
    refine add_le_add ?_ ?_
    · rw [← ENNReal.ofReal_mul hL0]
      exact ENNReal.ofReal_le_ofReal hMle
    · calc J ≤ I := hJ
        _ = 1 * I := (one_mul _).symm
        _ ≤ ENNReal.ofReal ((Sig ^ (1 / 2 : ℝ) + 1) * ν⁻¹) * I :=
            mul_le_mul_left (ENNReal.one_le_ofReal.mpr hL1) _
  have hC0 : 0 ≤ (C₁ + 1) * ν ^ (-1 / 2 : ℝ) := mul_nonneg (by linarith) hνr0
  calc X + Y ≤ ENNReal.ofReal ((C₁ + 1) * ν ^ (-1 / 2 : ℝ)) * (ENNReal.ofReal M + J) := hstep1
    _ ≤ ENNReal.ofReal ((C₁ + 1) * ν ^ (-1 / 2 : ℝ)) *
        (ENNReal.ofReal ((Sig ^ (1 / 2 : ℝ) + 1) * ν⁻¹) *
          (ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * M) + I)) := mul_le_mul_right hstep2 _
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hC0, pow_one,
          show (C₁ + 1) * ν ^ (-1 / 2 : ℝ) * ((Sig ^ (1 / 2 : ℝ) + 1) * ν⁻¹) =
            (C₁ + 1) * (Sig ^ (1 / 2 : ℝ) + 1) * ν⁻¹ * ν ^ (-1 / 2 : ℝ) by ring]

/-- Late unit bound (`s > p.H ≥ 1`) combined with the `H¹` part (target constant). -/
theorem late_unit_combine {ν M C₁ Sig : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hC₁ : 0 < C₁)
    (hSig : 0 < Sig) {X Y J : ℝ≥0∞}
    (hX : X ≤ ENNReal.ofReal M)
    (hY : Y ≤ ENNReal.ofReal (C₁ * ν ^ (-1 / 2 : ℝ)) * (ENNReal.ofReal M + J)) :
    X + Y ≤ ENNReal.ofReal ((C₁ + 1) * (Sig ^ (1 / 2 : ℝ) + 1) * ν ^ (-1 / 2 : ℝ)) *
      (ENNReal.ofReal M + J) := by
  have hνr : 1 ≤ ν ^ (-1 / 2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν0 hν1 (by norm_num)
  have hνr0 : 0 ≤ ν ^ (-1 / 2 : ℝ) := zero_le_one.trans hνr
  refine (unit_absorb hν0 hν1 hC₁ hX hY).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
  refine mul_le_mul_of_nonneg_right ?_ hνr0
  have hS : 1 ≤ Sig ^ (1 / 2 : ℝ) + 1 := by
    have := Real.rpow_nonneg hSig.le (1 / 2 : ℝ)
    linarith
  have hC : 0 ≤ C₁ + 1 := by linarith
  calc C₁ + 1 = (C₁ + 1) * 1 := (mul_one _).symm
    _ ≤ (C₁ + 1) * (Sig ^ (1 / 2 : ℝ) + 1) := mul_le_mul_of_nonneg_left hS hC

end F8U

/-! ## 3. The four leaves -/

/-- **Leaf `PartII-b:F8/1/org/1` (`CylOseenOrbitSmoothing`, SP 2296–2301)**: "differentiate
(short-bg:body-eq) homogeneously twice. Incompressibility, orthogonality of `P_0`, and
(short-bg:train-uniform) give `E_j' + ν E_{j+1} ≤ C ∑_{i ≤ j} E_i`, `j ≤ 2`. Multiplication by
successive powers of `ν(t - s)` and summation gives `H¹ → H²` norm `C [ν(t - s)]^{-1/2}` for
`t - s ≤ 1`." For a train with `∑_{j ≤ 3} ‖D^j v(s)‖_∞ ≤ C_tr` at all ages and `ν ≤ 1`, every orbit
`w = S_0(·, σ)u` (`F8U.IsCylOseenOrbit`) from an `H¹_σ` datum obeys, for `0 < t - σ ≤ 1`,
`‖w(t)‖_{H¹} ≤ A ‖u‖_{H¹}` and `∑_{i,j} ‖∂_i∂_j w(t)‖_{L²(cell)} ≤ A [ν(t - σ)]^{-1/2} ‖u‖_{H¹}`,
with `A` depending only on `C_tr`. -/
def CylOseenOrbitSmoothing : Prop :=
  ∀ C_tr : ℝ, 0 < C_tr → ∃ A : ℝ, 0 < A ∧
    ∀ (dm dp : ℝ) (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ 1 →
      (∀ s : ℝ, 0 ≤ s → ∀ j : ℕ, j ≤ 3 → ∀ z, ‖iteratedFDeriv ℝ j (p.train.v s) z‖ ≤ C_tr) →
      ∀ σ : ℝ, 0 ≤ σ → ∀ (u uq uη : B0579.Plane → CMerid) (w : CProf),
        F8U.IsCylH1Datum p.c u uq uη → F8U.IsCylOseenOrbit p σ w u uq uη →
        ∀ t ∈ Ioc σ (σ + 1),
          F8U.cylH1 p.c (F8U.slice w t) (F8U.slice (F8U.pd 0 w) t) (F8U.slice (F8U.pd 1 w) t) ≤
              ENNReal.ofReal A * F8U.cylH1 p.c u uq uη ∧
            ∑ i : Fin 2, ∑ j : Fin 2, F8U.cellL2 p.c (F8U.slice (F8U.pd i (F8U.pd j w)) t) ≤
              ENNReal.ofReal (A * p.ν ^ (-1 / 2 : ℝ) * (t - σ) ^ (-1 / 2 : ℝ)) *
                F8U.cylH1 p.c u uq uη

/-- **Leaf `PartII-b:F8/1/org/2` (`CylOseenOrbitExists`, SP 2213–2217, 2296–2297)**: at every
parameter point of the regime and every age `σ ≥ 0`, the homogeneous meridional equation
`w_s - νΔw + P_0(v·∇w + w·∇v) = 0` on the periodic cylinder `C_c` has, from every `H¹_σ(C_c)` datum,
a solution `F8U.IsCylOseenOrbit` on `(σ, σ + 2)` (Galerkin or semigroup existence and parabolic
regularity; the train is smooth with bounded spatial derivatives on bounded age intervals,
`BgRegime.train_buc`). -/
def CylOseenOrbitExists : Prop :=
  ∀ (dm dp : ℝ) (p : Params) (d : ℝ), BgRegime p d dm dp →
    ∀ σ : ℝ, 0 ≤ σ → ∀ u uq uη : B0579.Plane → CMerid, F8U.IsCylH1Datum p.c u uq uη →
      ∃ w : CProf, F8U.IsCylOseenOrbit p σ w u uq uη

/-- **Leaf `PartII-b:F8/1/org/3` (`MeridionalDuhamelRegularity`, SP 2301–2305)**: "On `0 < s < 2`,
Duhamel ... For `s ≥ 2` use Duhamel only on `[s - 1, s]`." Given the flow bounds
`F8U.CylOseenFlowBound A p`, every weak global meridional correction `z` (forcing `g` weakly
solenoidal with `‖g(·)‖_{H¹}` in `L^p((0,T₀], s^{13/8}ds)` and in `L^p((T₁,∞), s^{-9/8}ds)`,
`0 < T₁ ≤ T₀`, and `‖z(s)‖_{H¹} ≤ M` at every age) has a strongly measurable version
`(z', zq', zη')`, equal to `(z, zq, zη)` a.e. on `s > 0` and continuous in `H¹(C_c)` at every age,
and weak second derivatives `D2` with the Duhamel bounds
`∑ ‖D²z(s)‖ ≤ C₁ ν^{-1/2} [s^{-1/2} M + ∫_0^s (s - t)^{-1/2} ‖g(t)‖_{H¹} dt]` (a.e. `s ∈ (0, 1]`) and
`∑ ‖D²z(s)‖ ≤ C₁ ν^{-1/2} [M + ∫_0^1 r^{-1/2} ‖g(s - r)‖_{H¹} dr]` (a.e. `s > 1`). -/
def MeridionalDuhamelRegularity : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C₁ : ℝ, 0 < C₁ ∧
    ∀ (dm dp : ℝ) (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ 1 →
      F8U.CylOseenFlowBound A p →
      ∀ (g gq gη z zq zη : CProf) (α : E2) (M T₀ T₁ : ℝ),
        QPeriodic p.c g → HasWeakVec vQ0 dZero g gq → HasWeakVec vEta dZero g gη →
        (∀ φ, IsCoordTest φ →
          Integrable (fun x => g x 0 * (cpd 1 φ x : ℂ) + g x 1 * (cpd 2 φ x : ℂ)) ∧
            ∫ x, (g x 0 * (cpd 1 φ x : ℂ) + g x 1 * (cpd 2 φ x : ℂ)) = 0) →
        IsGlobalMeridionalCorrection p g z zq zη α →
        (∀ s : ℝ, 0 < s → sliceH1Norm p.c z zq zη s ≤ ENNReal.ofReal M) →
        Measurable (sliceH1Norm p.c g gq gη) →
        0 < T₁ → T₁ ≤ T₀ →
        sLpNorm (13 / 8) T₀ (sliceH1Norm p.c g gq gη) < ⊤ →
        tailLpNorm (-9 / 8) T₁ (sliceH1Norm p.c g gq gη) < ⊤ →
        ∃ (z' zq' zη' : CProf) (D2 : Fin 2 → Fin 2 → CProf),
          StronglyMeasurable z' ∧ StronglyMeasurable zq' ∧ StronglyMeasurable zη' ∧
          (∀ i j, StronglyMeasurable (D2 i j)) ∧
          (∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), z' x = z x) ∧
          (∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), zq' x = zq x) ∧
          (∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), zη' x = zη x) ∧
          (∀ s : ℝ, 0 < s →
            Tendsto (fun s' => F8U.cylH1 p.c (fun y => z' (s', y) - z' (s, y))
              (fun y => zq' (s', y) - zq' (s, y)) (fun y => zη' (s', y) - zη' (s, y)))
              (𝓝 s) (𝓝 0)) ∧
          HasWeakVec vQ0 dZero zq' (D2 0 0) ∧ HasWeakVec vEta dZero zq' (D2 0 1) ∧
          HasWeakVec vQ0 dZero zη' (D2 1 0) ∧ HasWeakVec vEta dZero zη' (D2 1 1) ∧
          (∀ᵐ s ∂volume, s ∈ Ioc (0 : ℝ) 1 →
            ∑ i : Fin 2, ∑ j : Fin 2, F8U.cellL2 p.c (F8U.slice (D2 i j) s) ≤
              ENNReal.ofReal (C₁ * p.ν ^ (-1 / 2 : ℝ)) *
                (ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * M) +
                  ∫⁻ t in Ioc 0 s, ENNReal.ofReal ((s - t) ^ (-1 / 2 : ℝ)) *
                    sliceH1Norm p.c g gq gη t)) ∧
          (∀ᵐ s ∂volume, 1 < s →
            ∑ i : Fin 2, ∑ j : Fin 2, F8U.cellL2 p.c (F8U.slice (D2 i j) s) ≤
              ENNReal.ofReal (C₁ * p.ν ^ (-1 / 2 : ℝ)) *
                (ENNReal.ofReal M +
                  ∫⁻ r in Ioc 0 1, ENNReal.ofReal (r ^ (-1 / 2 : ℝ)) *
                    sliceH1Norm p.c g gq gη (s - r)))

/-- **Leaf `PartII-b:F8/1/org/4` (`MeridionalLinearVersion`)**: the `F`-wise regular versions of
`MeridionalDuhamelRegularity` assemble into *linear* maps `F ↦ (z, z_q, z_η, D²z)` (extend the
versions chosen on a Hamel basis of `H_p` linearly; a.e. identities, weak derivative relations,
the meridional equation and the `H¹`-continuity are preserved by finite linear combinations, and
the bounds `Mz F`, `Bnd F s` transfer because two weak derivatives of a.e. equal functions agree
a.e. on `s > 0` and the `H¹`-continuous version is bounded at every age where it is bounded at a.e.
age). The source map `F ↦ z` of SP 2213–2217 is linear; this is its representative-level form. -/
def MeridionalLinearVersion : Prop :=
  ∀ (p : Params) (αMap : HpR p.c →L[ℝ] E2) (gOf zOf₀ zqOf₀ zηOf₀ : HpR p.c →ₗ[ℝ] CProf)
    (Mz : HpR p.c → ℝ) (Bnd : HpR p.c → ℝ → ℝ≥0∞),
    (∀ F, IsGlobalMeridionalCorrection p (gOf F) (zOf₀ F) (zqOf₀ F) (zηOf₀ F) (αMap F)) →
    (∀ F, ∀ s : ℝ, 0 < s → sliceH1Norm p.c (zOf₀ F) (zqOf₀ F) (zηOf₀ F) s +
      ENNReal.ofReal ‖αMap F‖ ≤ ENNReal.ofReal (Mz F)) →
    (∀ F, ∃ (z' zq' zη' : CProf) (D2 : Fin 2 → Fin 2 → CProf),
      StronglyMeasurable z' ∧ StronglyMeasurable zq' ∧ StronglyMeasurable zη' ∧
      (∀ i j, StronglyMeasurable (D2 i j)) ∧
      (∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), z' x = zOf₀ F x) ∧
      (∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), zq' x = zqOf₀ F x) ∧
      (∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), zη' x = zηOf₀ F x) ∧
      (∀ s : ℝ, 0 < s →
        Tendsto (fun s' => F8U.cylH1 p.c (fun y => z' (s', y) - z' (s, y))
          (fun y => zq' (s', y) - zq' (s, y)) (fun y => zη' (s', y) - zη' (s, y)))
          (𝓝 s) (𝓝 0)) ∧
      HasWeakVec vQ0 dZero zq' (D2 0 0) ∧ HasWeakVec vEta dZero zq' (D2 0 1) ∧
      HasWeakVec vQ0 dZero zη' (D2 1 0) ∧ HasWeakVec vEta dZero zη' (D2 1 1) ∧
      ∀ᵐ s ∂volume, 0 < s →
        ∑ i : Fin 2, ∑ j : Fin 2, F8U.cellL2 p.c (F8U.slice (D2 i j) s) ≤ Bnd F s) →
    ∃ (zOf zqOf zηOf : HpR p.c →ₗ[ℝ] CProf) (D2zOf : Fin 2 → Fin 2 → HpR p.c →ₗ[ℝ] CProf),
      ∀ F : HpR p.c,
        IsGlobalMeridionalCorrection p (gOf F) (zOf F) (zqOf F) (zηOf F) (αMap F) ∧
        QPeriodic p.c (zOf F) ∧ QPeriodic p.c (zqOf F) ∧ QPeriodic p.c (zηOf F) ∧
        StronglyMeasurable (zOf F) ∧ StronglyMeasurable (zqOf F) ∧
        StronglyMeasurable (zηOf F) ∧ (∀ i j, StronglyMeasurable (D2zOf i j F)) ∧
        HasWeakVec vQ0 dZero (zqOf F) (D2zOf 0 0 F) ∧
        HasWeakVec vEta dZero (zqOf F) (D2zOf 0 1 F) ∧
        HasWeakVec vQ0 dZero (zηOf F) (D2zOf 1 0 F) ∧
        HasWeakVec vEta dZero (zηOf F) (D2zOf 1 1 F) ∧
        (∀ s : ℝ, 0 < s → sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F) s +
          ENNReal.ofReal ‖αMap F‖ ≤ ENNReal.ofReal (Mz F)) ∧
        (∀ᵐ s ∂volume, 0 < s →
          ∑ i : Fin 2, ∑ j : Fin 2, F8U.cellL2 p.c (F8U.slice (D2zOf i j F) s) ≤ Bnd F s)

/-! ## 4. Assembly -/

/-- **Conditional assembly of `CylinderParabolicH2Duhamel` (`PartII-b:F8/1`, SP 2296–2305)** from
the uniform train bound `TrainUniform` (SP 2052–2053; proved as `Spine.trainEstimates.2`) and the
four leaves. Constants: `C_sm = (C₁ + 1)(Σ^{1/2} + 1)`, `k_sm = 1`, `ν_sm = min (min ν_tu 1) Σ`, so
`p.H = Σ/ν ≥ 1`; on `(0, 1]` and `(p.H, ∞)` the unit-horizon bounds are used directly, on
`1 < s ≤ p.H` they are converted with `F8U.band_unit_combine`. Composed in task `PartII-b:F8/1`. -/
theorem cylinderParabolicH2Duhamel_of_org (hTU : UnforcedLeray.Short.Spine.TrainUniform)
    (h1 : CylOseenOrbitSmoothing) (h2 : CylOseenOrbitExists)
    (h3 : MeridionalDuhamelRegularity) (h4 : MeridionalLinearVersion) :
    CylinderParabolicH2Duhamel := by
  intro C_late hC_late Sig lam q hSig _hEig a' ha'0 _ha'1 dm dp hdm C_ge k_ge hC_ge
  obtain ⟨C_tu, ν_tu, hν_tu, hTrain⟩ := hTU
  have hC_tr : (0 : ℝ) < max C_tu 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨A, hA, hSm⟩ := h1 (max C_tu 1) hC_tr
  obtain ⟨C₁, hC₁, hDuh⟩ := h3 A hA
  have hSig_rpow : 0 ≤ Sig ^ (1 / 2 : ℝ) := Real.rpow_nonneg hSig.le _
  refine ⟨(C₁ + 1) * (Sig ^ (1 / 2 : ℝ) + 1), 1, min (min ν_tu 1) Sig,
    mul_pos (by linarith) (by linarith), lt_min (lt_min hν_tu one_pos) hSig, ?_⟩
  intro p d hreg hν_le hAge _hMode αMap b0Of b0qOf b0ηOf gOf gqOf gηOf zOf₀ zqOf₀ zηOf₀ hGE
  have hν0 : 0 < p.ν := p.ν_pos
  have hν_tu' : p.ν ≤ ν_tu := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν1 : p.ν ≤ 1 := hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_Sig : p.ν ≤ Sig := hν_le.trans (min_le_right _ _)
  have hH_eq : p.H = Sig / p.ν := by
    show p.ageCut / p.ν = Sig / p.ν
    rw [hAge]
  have hH1 : 1 ≤ p.H := by
    rw [hH_eq, one_le_div hν0]
    exact hν_Sig
  have hc : p.c = UnforcedLeray.Train.per p.ν := by
    rw [hreg.c_eq, UnforcedLeray.Train.per, inv_pow]
  have htr : ∀ s : ℝ, 0 ≤ s → ∀ j : ℕ, j ≤ 3 → ∀ z,
      ‖iteratedFDeriv ℝ j (p.train.v s) z‖ ≤ max C_tu 1 := by
    intro s hs j hj z
    exact (F8U.train_bound_transport hc p.train (hTrain p.ν ⟨hν0, hν_tu'⟩) hreg.train_buc
      s hs j hj z).trans (le_max_left _ _)
  have hFlow : F8U.CylOseenFlowBound A p := fun σ hσ u uq uη hdat =>
    ⟨h2 dm dp p d hreg σ hσ u uq uη hdat,
      fun w hw t ht => hSm dm dp p d hreg hν1 htr σ hσ u uq uη w hdat hw t ht⟩
  let Mz : HpR p.c → ℝ := fun F =>
    C_ge * (p.ν ^ k_ge)⁻¹ *
      Real.exp ((a' * Sig + C_late / (1 + Sig)) / p.ν + C_late * p.ν ^ 3) * ‖F‖
  have hMz : ∀ F, 0 ≤ Mz F := fun F => by
    dsimp only [Mz]
    positivity
  let G : HpR p.c → ℝ → ℝ≥0∞ := fun F => sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)
  let Bnd : HpR p.c → ℝ → ℝ≥0∞ := fun F s =>
    if s ≤ 1 then
      ENNReal.ofReal (C₁ * p.ν ^ (-1 / 2 : ℝ)) *
        (ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * Mz F) +
          ∫⁻ t in Ioc 0 s, ENNReal.ofReal ((s - t) ^ (-1 / 2 : ℝ)) * G F t)
    else
      ENNReal.ofReal (C₁ * p.ν ^ (-1 / 2 : ℝ)) *
        (ENNReal.ofReal (Mz F) +
          ∫⁻ r in Ioc 0 1, ENNReal.ofReal (r ^ (-1 / 2 : ℝ)) * G F (s - r))
  have hT1 : (0 : ℝ) < max 1 (p.H - 1) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hT10 : max 1 (p.H - 1) ≤ p.H := max_le hH1 (by linarith)
  have hGlob : ∀ F, IsGlobalMeridionalCorrection p (gOf F) (zOf₀ F) (zqOf₀ F) (zηOf₀ F)
      (αMap F) := fun F => by
    obtain ⟨-, -, -, -, -, -, -, -, hglob, -⟩ := hGE F
    exact hglob
  have hBd : ∀ F, ∀ s : ℝ, 0 < s → sliceH1Norm p.c (zOf₀ F) (zqOf₀ F) (zηOf₀ F) s +
      ENNReal.ofReal ‖αMap F‖ ≤ ENNReal.ofReal (Mz F) := fun F => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hzbd⟩ := hGE F
    exact hzbd
  have hPer : ∀ F : HpR p.c, ∃ (z' zq' zη' : CProf) (D2 : Fin 2 → Fin 2 → CProf),
      StronglyMeasurable z' ∧ StronglyMeasurable zq' ∧ StronglyMeasurable zη' ∧
      (∀ i j, StronglyMeasurable (D2 i j)) ∧
      (∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), z' x = zOf₀ F x) ∧
      (∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), zq' x = zqOf₀ F x) ∧
      (∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), zη' x = zηOf₀ F x) ∧
      (∀ s : ℝ, 0 < s →
        Tendsto (fun s' => F8U.cylH1 p.c (fun y => z' (s', y) - z' (s, y))
          (fun y => zq' (s', y) - zq' (s, y)) (fun y => zη' (s', y) - zη' (s, y)))
          (𝓝 s) (𝓝 0)) ∧
      HasWeakVec vQ0 dZero zq' (D2 0 0) ∧ HasWeakVec vEta dZero zq' (D2 0 1) ∧
      HasWeakVec vQ0 dZero zη' (D2 1 0) ∧ HasWeakVec vEta dZero zη' (D2 1 1) ∧
      ∀ᵐ s ∂volume, 0 < s →
        ∑ i : Fin 2, ∑ j : Fin 2, F8U.cellL2 p.c (F8U.slice (D2 i j) s) ≤ Bnd F s := by
    intro F
    obtain ⟨-, -, -, -, hgper, hgq, hgη, hbody, hglob, hGmeas, -, hGearly, hGtail, hzbd⟩ :=
      hGE F
    have hzM : ∀ s : ℝ, 0 < s →
        sliceH1Norm p.c (zOf₀ F) (zqOf₀ F) (zηOf₀ F) s ≤ ENNReal.ofReal (Mz F) :=
      fun s hs => le_trans le_self_add (hzbd s hs)
    have hfin1 : sLpNorm (13 / 8) p.H (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) < ⊤ :=
      lt_of_le_of_lt hGearly ENNReal.ofReal_lt_top
    have hfin2 : tailLpNorm (-9 / 8) (max 1 (p.H - 1))
        (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) < ⊤ :=
      lt_of_le_of_lt hGtail ENNReal.ofReal_lt_top
    obtain ⟨z', zq', zη', D2, hz', hzq', hzη', hD2, hae1, hae2, hae3, hct, hw1, hw2, hw3, hw4,
        hb1, hb2⟩ :=
      hDuh dm dp p d hreg hν1 hFlow (gOf F) (gqOf F) (gηOf F) (zOf₀ F) (zqOf₀ F) (zηOf₀ F)
        (αMap F) (Mz F) p.H (max 1 (p.H - 1)) hgper hgq hgη hbody.solenoidal hglob hzM hGmeas
        hT1 hT10 hfin1 hfin2
    refine ⟨z', zq', zη', D2, hz', hzq', hzη', hD2, hae1, hae2, hae3, hct, hw1, hw2, hw3, hw4, ?_⟩
    filter_upwards [hb1, hb2] with s hs01 hs1 hs0
    by_cases hs : s ≤ 1
    · dsimp only [Bnd]
      rw [if_pos hs]
      exact hs01 ⟨hs0, hs⟩
    · dsimp only [Bnd]
      rw [if_neg hs]
      exact hs1 (lt_of_not_ge hs)
  obtain ⟨zOf, zqOf, zηOf, D2zOf, hOut⟩ := h4 p αMap gOf zOf₀ zqOf₀ zηOf₀ Mz Bnd hGlob hBd hPer
  refine ⟨zOf, zqOf, zηOf, D2zOf, fun F => ?_⟩
  obtain ⟨hglob, hp1, hp2, hp3, hs1, hs2, hs3, hs4, hw1, hw2, hw3, hw4, hH1b, hD2⟩ := hOut F
  intro M_exp M_z0 GF Z2
  refine ⟨hglob, hp1, hp2, hp3, hs1, hs2, hs3, hs4, hw1, hw2, hw3, hw4, hH1b, ?_, ?_⟩
  · filter_upwards [hD2] with s hDs hsH
    have hs0 : 0 < s := hsH.1
    have hX : sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F) s ≤ ENNReal.ofReal (Mz F) :=
      le_trans le_self_add (hH1b s hs0)
    have hY := hDs hs0
    show sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F) s +
        ∑ i : Fin 2, ∑ j : Fin 2, F8U.cellL2 p.c (F8U.slice (D2zOf i j F) s) ≤ _
    by_cases hs1' : s ≤ 1
    · dsimp only [Bnd] at hY
      rw [if_pos hs1'] at hY
      exact F8U.early_unit_combine hν0 hν1 hs0 hs1' (hMz F) hC₁ hSig hX hY
    · have hs1'' : 1 < s := lt_of_not_ge hs1'
      dsimp only [Bnd] at hY
      rw [if_neg hs1'] at hY
      have hsH' : s ≤ Sig / p.ν := by
        rw [← hH_eq]
        exact hsH.2
      exact F8U.band_unit_combine hν0 hν1 hs1'' hsH' (hMz F) hC₁ hSig hX hY
        (F8U.unit_duhamel_le_full hs1'' (G F))
  · filter_upwards [hD2] with s hDs hsH
    have hs1'' : 1 < s := lt_of_le_of_lt hH1 hsH
    have hs0 : 0 < s := zero_lt_one.trans hs1''
    have hX : sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F) s ≤ ENNReal.ofReal (Mz F) :=
      le_trans le_self_add (hH1b s hs0)
    have hY := hDs hs0
    dsimp only [Bnd] at hY
    rw [if_neg (not_le.mpr hs1'')] at hY
    show sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F) s +
        ∑ i : Fin 2, ∑ j : Fin 2, F8U.cellL2 p.c (F8U.slice (D2zOf i j F) s) ≤ _
    exact F8U.late_unit_combine hν0 hν1 hC₁ hSig hX hY

end UnforcedLeray.Short.IIb

end
