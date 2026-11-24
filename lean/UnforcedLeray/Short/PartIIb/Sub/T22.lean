import UnforcedLeray.Short.PartIIb.StatementsMixed
import UnforcedLeray.Short.PartIIb.Sub.TrainCloseCell

/-!
# Part II-b, task `PartII-b:T22`: the free cylinder energy estimate (conditional)

Source of record: `the November 2 reference manuscript`, lines 2074-2105
(`short-bg:actual-cylinder`, `short-bg:free-cylinder`): "The central radial Gaussian transports
the radial weight exactly; image velocities, the seam region, and the displayed error contribute
at most `C(δ_c + e^{-b_Σ c²})` to its logarithmic derivative. The weight is continuous across the
seam and its normal derivative has a negative jump. Its distributional Laplacian is therefore
bounded above by `C_m` times the weight. Weighted integration by parts gives
`‖S_{ν,c}(t,s)‖ ≤ exp[(C_mν + Cδ_c + Ce^{-b_Σ c²})(t-s)]`" (2092-2101), and "one may smooth the
weight ... to justify this calculation" (2103-2104).

## The target

`FreeCylEnergy` is the energy form of that bound for smooth data: for `m > 8`, `Σ > 0` there are
constants `C_m, C, b > 0` such that for every parameter point with `c ≥ 1`, every `δ ≥ 0` with
`TrainClose`, every age `s ≥ 0`, every smooth `c`-periodic datum `f` with compact `η`-support
(`B0579.IsCylTest p.c f`) and every weak solution `ω` of `IsFreeCylFlow` from `f`, the energy
`t ↦ ‖ω t‖²_{X_{m,c}}` has a right derivative bounded by `2K‖ω t‖²` on `[s, Σ/ν)`, with
`K = C_mν + Cδ + Ce^{-b c²}`, and `‖ω t‖ ≤ exp(K(t-s)) ‖f‖` for `s ≤ t ≤ Σ/ν`.



* The datum class is `IsCylTest p.c f` (smooth, `c`-periodic in `q`, compact in `η`), not
  "smooth with compact support in the plane": a datum that is not `c`-periodic has a jump at the
  seam of its periodic extension, the energy then has right derivative `-∞` at `t = s`
  (`E(σ) - E(s) ~ -√(σ - s)`), and the right-derivative statement is false.
* The statement is for `c ≥ 1` (`ν ≤ 1` on `BgRegime`, `c = ν⁻²`). The `e^{-b c²}` bound for the
  image velocities `Σ_{n≠0} V(x - n c e₁)` on the cell has a constant that grows like `1/c` as
  `c → 0` (the sum is a Riemann sum of `∫ V dq ≠ 0`); `FreeCylinderBound` in `StatementsMixed.lean`
  quantifies over all `ν > 0` (`BgRegime` has no upper bound on `ν`), so the author should add
  `p.ν ≤ ν₀` there or `PartII-b:T24` must treat `p.c < 1` separately.

## Route (as in the source) and what is proved here

For a *regular* flow (smooth, periodic, rapidly decaying with its first two derivatives) the
energy `E(σ) = ∫_cell ω² w`, `w = (1 + q² + η²)^m`, satisfies
`E' = 2∫ ω(νΔω - v·∇ω) w`. Then
* the diffusion term gives `2ν∫ωΔω w ≤ C_m ν E` by the seam inequality of T21
  (`weight_laplacian_le`, applied to `ω²`, with a cut-off in `η` for the decay),
* the transport term is `-2∫ω v·∇ω w = ∫ω² v·∇w` (`div v = 0`, `v`, `ω`, `w` even across the seam),
  the central Gaussian `isoVelocity` is orthogonal to `∇w` (T21,
  `weight_logderiv_isoVelocity`), and `|∇w| ≤ m w` pointwise, so the transport term is at most
  `m sup_cell|v - isoVelocity| E`,
* `sup_cell|v - isoVelocity| ≤ C(δ + e^{-b c²})`: `TrainClose` gives `|v - V_c^p| ≤ δ` on the cell
  (hence on the plane, `TrainClose.norm_sub_le`: both are `c`-periodic in `q`) and the images
  of the (Gaussian-stream) periodized vortex are at distance `≥ c/2` from every point of the cell.

Proved here (complete proofs): the Gronwall step `cyl_gronwall_of_rate`, the pointwise weight
bound and the orthogonality of the central vortex, the dissipation inequality
`t22_dissipation` (diffusion + transport + train gap), the bridge between `cylEnergy` and
`eLpNorm` (`t22_energy_eq_sq_eLpNorm`) and the glue `free_cyl_energy_of`, which combines the leaves
below.

Leaves (tasks `PartII-b:T22/1-6`, exact Lean types below):
1. `CylClassicalExists` (parabolic existence with decay, SIZE XL; decomposed in
   `Sub/T22_1/Plan.lean`),
2. `CylWeakEqClassical` (uniqueness of weak solutions by duality, SIZE XL),
3. `RegularEnergyDeriv` (differentiation under the integral sign),
4. `CylDiffusionBound` (direct weighted integration by parts with an `η` cut-off),
5. `CylTransportIBP` (periodic integration by parts with `div v = 0`),
6. `CylTrainGap` (the train gap and the image estimate on the cell).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

/-! ## Definitions -/

/-- The squared weighted norm `‖g‖²_{X_{m,c}} = ∫_{C_c} g² (1+q²+η²)^m` (real form). -/
def cylEnergy (c m : ℝ) (g : B0579.Plane → ℝ) : ℝ :=
  ∫ x in B0579.cell c, g x ^ 2 * (B0579.density m x : ℝ)

/-- The energy `t ↦ ‖ω t‖²` has a right derivative `E'` at every `τ ∈ I`, and `E' τ ≤ 2K‖ω τ‖²`. -/
def CylEnergyRate (c m K : ℝ) (I : Set ℝ) (ω : ℝ → B0579.Plane → ℝ) : Prop :=
  ∃ E' : ℝ → ℝ, ∀ τ ∈ I,
    HasDerivWithinAt (fun σ => cylEnergy c m (ω σ)) (E' τ) (Ici τ) τ ∧
      E' τ ≤ 2 * K * cylEnergy c m (ω τ)

/-- A smooth `c`-periodic function on the plane (a function on the cylinder `C_c`) such that it and
its first two derivatives decay faster than any power of `1 + η²`: the class in which the
weighted integrations by parts of SP 2092-2101 are justified.

The decay is in the axial variable `η` only. A `c`-periodic function in `q` cannot decay in the
full weight `jb = 1 + q² + η²` (it would vanish identically; the first version of this file used
that weight, see `Sub/T22_1.lean`). The weight `(1 + q² + η²)^m` of SP 2074-2076 lives on the
centered cell `C_c`, where `|q| ≤ c/2` and `1 + η² ≤ jb ≤ (1 + c²/4)(1 + η²)`
(`Sub/T22/CylDecayBridge.lean`), so decay in `η` is decay in `jb` on the cell.

The smoothness is `C²` (not `C^∞`), the order that the three integrations by parts of SP 2092-2101
(diffusion, transport, energy derivative) use and that a classical solution of `ω_σ = νΔω - v·∇ω`
has when the train velocity `v` is only known to have bounded derivatives up to order `4`
(`TrainClose` controls `D^j(v - V_c^p)` for `j ≤ 4`): a global `C^∞` solution would need bounds on
all derivatives of `v`, which `TrainClose` does not give (`ORG:cyl-weight`, second change). -/
structure CylSmoothDecay (c : ℝ) (g : B0579.Plane → ℝ) : Prop where
  smooth : ContDiff ℝ 2 g
  periodic : ∀ x : B0579.Plane, g (x.1 + c, x.2) = g x
  decay : ∀ N : ℝ, ∃ C : ℝ, ∀ x : B0579.Plane,
    (|g x| + |B0579.pd 0 g x| + |B0579.pd 1 g x| + |lapP g x|) * (1 + x.2 ^ 2) ^ N ≤ C

/-- A *regular* (classical) solution on `[s, T]` of `ω_σ = νΔω - v·∇ω` on the cylinder `C_c`:
jointly continuous, every slice in `CylSmoothDecay` (`C²` in the plane variable), the decay in `η` (weight `(1 + η²)^N`) uniform in
the age `σ ∈ [s, T]`, and the equation holding pointwise (with the one-sided derivative in `σ`). -/
structure IsRegularCylFlow (c ν : ℝ) (v : ℝ → B0579.Plane → UnforcedLeray.Train.Vec) (s T : ℝ)
    (ω : ℝ → B0579.Plane → ℝ) : Prop where
  jointCont : ContinuousOn (fun z : ℝ × B0579.Plane => ω z.1 z.2) (Icc s T ×ˢ univ)
  slice : ∀ σ ∈ Icc s T, CylSmoothDecay c (ω σ)
  decay : ∀ N : ℝ, ∃ C : ℝ, ∀ σ ∈ Icc s T, ∀ x : B0579.Plane,
    (|ω σ x| + |B0579.pd 0 (ω σ) x| + |B0579.pd 1 (ω σ) x| + |lapP (ω σ) x|) *
      (1 + x.2 ^ 2) ^ N ≤ C
  pde : ∀ σ ∈ Icc s T, ∀ x : B0579.Plane,
    HasDerivWithinAt (fun r => ω r x)
      (ν * lapP (ω σ) x - (v σ x 0 * B0579.pd 0 (ω σ) x + v σ x 1 * B0579.pd 1 (ω σ) x))
      (Icc s T) σ

/-- **Target of `PartII-b:T22`** (SP 2092-2103): the energy form of the free cylinder bound for
smooth data. See the module docstring for the two differences from the first draft. -/
def FreeCylEnergy : Prop :=
  ∀ m : ℝ, 8 < m → ∀ Sg : ℝ, 0 < Sg → ∃ (Cm C b : ℝ), 0 < Cm ∧ 0 < C ∧ 0 < b ∧
    ∀ (p : Params), 1 ≤ p.c → ∀ δ : ℝ, 0 ≤ δ → TrainClose p.train Sg δ →
      ∀ s : ℝ, 0 ≤ s → ∀ f : B0579.Plane → ℝ, B0579.IsCylTest p.c f →
        ∀ ω : ℝ → B0579.Plane → ℝ, IsFreeCylFlow m p.train s f ω →
          CylEnergyRate p.c m (Cm * p.ν + C * δ + C * Real.exp (-b * p.c ^ 2))
              (Ico s (Sg / p.ν)) ω ∧
            ∀ t : ℝ, s ≤ t → t ≤ Sg / p.ν →
              eLpNorm (ω t) 2 (B0579.cellMeasure p.c m) ≤
                ENNReal.ofReal (Real.exp ((Cm * p.ν + C * δ + C * Real.exp (-b * p.c ^ 2)) *
                  (t - s))) * eLpNorm f 2 (B0579.cellMeasure p.c m)

/-! ## The leaves -/

/-- **Leaf 1: classical solutions with Gaussian-type decay** (SP 2103-2105, "smoothing"; standard
parabolic theory). For `ν > 0`, `c ≥ 1`, a train `tr` with `TrainClose tr Σ δ` (so `v` is smooth,
bounded with its first derivative, `c`-periodic and divergence free on `[0, Σ/ν]`) and a smooth
datum `f` of class `IsCylTest c`, the problem `ω_σ = νΔω - v·∇ω`, `ω(s) = f` has a regular solution
on `[s, Σ/ν]` (regular: `C²` slices decaying faster than any power of `1 + η²`; see
`Sub/T22_1/Plan.lean` for the decomposition and `Sub/T22_1.lean` for the history). `c ≥ 1` is the
regime of `FreeCylEnergy` (the lattice sum of image vortices is bounded with its derivatives
uniformly in `c ≥ 1`). -/
def CylClassicalExists : Prop :=
  ∀ (Sg : ℝ), 0 < Sg → ∀ (ν c δ : ℝ), 0 < ν → 1 ≤ c → 0 ≤ δ → ∀ tr : B0140.TrainSol ν c,
    TrainClose tr Sg δ → ∀ s : ℝ, 0 ≤ s → s ≤ Sg / ν → ∀ f : B0579.Plane → ℝ,
      B0579.IsCylTest c f →
        ∃ ω : ℝ → B0579.Plane → ℝ, IsRegularCylFlow c ν tr.v s (Sg / ν) ω ∧ ω s = f

/-- **Leaf 2: uniqueness of weak solutions** (SP 2100-2105; duality with the regular backward
problem; a regular solution is a weak solution on `[s, Σ/ν]`). A weak solution `ω` of
`IsFreeCylFlow` with the datum `f` coincides, for every age in `[s, Σ/ν]`, almost everywhere on the
cell with a regular solution `ω'` with datum `f`. -/
def CylWeakEqClassical : Prop :=
  ∀ m : ℝ, 8 < m → ∀ (Sg : ℝ), 0 < Sg → ∀ (ν c δ : ℝ), 0 < ν → 0 < c → 0 ≤ δ →
    ∀ tr : B0140.TrainSol ν c, TrainClose tr Sg δ → ∀ s : ℝ, 0 ≤ s →
      ∀ f : B0579.Plane → ℝ, B0579.IsCylTest c f →
        ∀ ω' : ℝ → B0579.Plane → ℝ, IsRegularCylFlow c ν tr.v s (Sg / ν) ω' → ω' s = f →
          ∀ ω : ℝ → B0579.Plane → ℝ, IsFreeCylFlow m tr s f ω →
            ∀ σ ∈ Icc s (Sg / ν), ω' σ =ᵐ[volume.restrict (B0579.cell c)] ω σ

/-- **Leaf 3: the energy of a regular flow** (differentiation under the integral sign, justified
by the uniform decay in `IsRegularCylFlow`): `σ ↦ ∫_cell ω² w` is continuous on `[s, T]` and has
the right derivative `2∫ ω (νΔω - v·∇ω) w` on `[s, T)`, for a bounded velocity `v`. -/
def RegularEnergyDeriv : Prop :=
  ∀ (c ν m s T : ℝ) (v : ℝ → B0579.Plane → UnforcedLeray.Train.Vec) (ω : ℝ → B0579.Plane → ℝ),
    0 < c → IsRegularCylFlow c ν v s T ω →
    (∃ M : ℝ, ∀ σ ∈ Icc s T, ∀ x : B0579.Plane, |v σ x 0| + |v σ x 1| ≤ M) →
    ContinuousOn (fun σ => cylEnergy c m (ω σ)) (Icc s T) ∧
      ∀ τ ∈ Ico s T, HasDerivWithinAt (fun σ => cylEnergy c m (ω σ))
        (2 * ∫ x in B0579.cell c, ω τ x * (ν * lapP (ω τ) x -
            (v τ x 0 * B0579.pd 0 (ω τ) x + v τ x 1 * B0579.pd 1 (ω τ) x)) *
              (B0579.density m x : ℝ)) (Ici τ) τ

/-- **Leaf 4: the diffusion term** (SP 2095-2097): `2∫ gΔg w ≤ C_m ∫ g² w` with `C_m` independent
of `c`. The two integrands are integrable.

Route for `C²` slices (`CylSmoothDecay`): the direct integration by parts on the cell, with a cut-off
`χ(η/R)`, `R → ∞`, removed using the decay: `div(g w ∇g) = w|∇g|² + g ∇w·∇g + g w Δg`, and
`∫_cell div(g w ∇g) = 0` (the seam terms cancel because `g`, `∇g` are `c`-periodic and `w = jb^m` is
even in `q`), so `2∫ gΔg w = -2∫ w|∇g|² - 2∫ g ∇w·∇g ≤ 2m²∫ g² w` by `|∇w| ≤ m w` componentwise
(`t22_pd_jb_le`) and `2m|g||p| ≤ |p|² + m²g²`. (`C_m = 2m²`; the earlier route through T21
`weight_laplacian_le` applied to `g²` needs `g² ∈ IsCylTest`, i.e. `C^∞`.) -/
def CylDiffusionBound : Prop :=
  ∀ m : ℝ, 0 < m → ∃ Cd : ℝ, ∀ c : ℝ, 0 < c → ∀ g : B0579.Plane → ℝ, CylSmoothDecay c g →
    IntegrableOn (fun x => g x ^ 2 * (B0579.density m x : ℝ)) (B0579.cell c) ∧
      IntegrableOn (fun x => g x * lapP g x * (B0579.density m x : ℝ)) (B0579.cell c) ∧
      2 * ∫ x in B0579.cell c, g x * lapP g x * (B0579.density m x : ℝ)
        ≤ Cd * cylEnergy c m g

/-- **Leaf 5: the transport term** (SP 2092-2093, 2097-2101; `div v = 0`, `v`, `g` and the weight
are even across the seam `q = ±c/2`, `g` decays in `η`): the periodic integration by parts
`-2∫ g (v·∇g) w = ∫ g² (v·∇w)` over the cell, `w = jb^m`, for the velocity of a train at an age
`σ ≥ 0`. Both integrands are integrable. -/
def CylTransportIBP : Prop :=
  ∀ (ν c : ℝ) (tr : B0140.TrainSol ν c) (σ : ℝ), 0 ≤ σ → 0 < c →
    (∃ M : ℝ, ∀ x : B0579.Plane, |tr.v σ x 0| + |tr.v σ x 1| ≤ M) →
    ∀ (m : ℝ) (g : B0579.Plane → ℝ), CylSmoothDecay c g →
      IntegrableOn (fun x => g x * (tr.v σ x 0 * B0579.pd 0 g x + tr.v σ x 1 * B0579.pd 1 g x) *
          (B0579.density m x : ℝ)) (B0579.cell c) ∧
        IntegrableOn (fun x => g x ^ 2 * (tr.v σ x 0 * B0579.pd 0 (fun y => B0579.jb y ^ m) x +
          tr.v σ x 1 * B0579.pd 1 (fun y => B0579.jb y ^ m) x)) (B0579.cell c) ∧
        -2 * ∫ x in B0579.cell c, g x * (tr.v σ x 0 * B0579.pd 0 g x +
            tr.v σ x 1 * B0579.pd 1 g x) * (B0579.density m x : ℝ)
          = ∫ x in B0579.cell c, g x ^ 2 * (tr.v σ x 0 * B0579.pd 0 (fun y => B0579.jb y ^ m) x +
            tr.v σ x 1 * B0579.pd 1 (fun y => B0579.jb y ^ m) x)

/-- **Leaf 6: the train gap** (SP 2085-2093). For `Σ > 0` there are `C, b > 0` such that for
`ν > 0`, `c ≥ 1`, `δ ≥ 0` and a train with `TrainClose tr Σ δ`, at every age `σ ∈ [0, Σ/ν]`:
the velocity is bounded by `C(δ + 1)` on the plane, and on the cell it differs from the central
Gaussian vortex `isoVelocity ν σ` (stream `-(2/a)e^{-|x|²/(4a)}`, `a = 1 + νσ ≤ 1 + Σ`) by at most
`C(δ + e^{-b c²})`. (`TrainClose` at order `0` gives `|v - V_c^p| ≤ δ` on the cell, and on the
whole plane because both are `c`-periodic in `q`, `TrainClose.norm_sub_le`; `V_c^p - isoVelocity` is
the sum of the images `isoVelocity(x - n c e₁)`, `n ≠ 0`, each at distance `≥ |n| c/2` from every
point of the cell, with Gaussian decay `|isoVelocity y| ≤ |y| e^{-|y|²/(4(1+Σ))}`.) -/
def CylTrainGap : Prop :=
  ∀ Sg : ℝ, 0 < Sg → ∃ (C b : ℝ), 0 < C ∧ 0 < b ∧
    ∀ (ν c δ : ℝ), 0 < ν → 1 ≤ c → 0 ≤ δ → ∀ tr : B0140.TrainSol ν c, TrainClose tr Sg δ →
      ∀ σ ∈ Icc (0 : ℝ) (Sg / ν),
        (∀ x : B0579.Plane, |tr.v σ x 0| + |tr.v σ x 1| ≤ C * (δ + 1)) ∧
          ∀ x ∈ B0579.cell c,
            |tr.v σ x 0 - (UnforcedLeray.B0146.isoVelocity ν σ x).1| +
              |tr.v σ x 1 - (UnforcedLeray.B0146.isoVelocity ν σ x).2|
                ≤ C * (δ + Real.exp (-b * c ^ 2))

/-!-/

/-- The Gronwall step. If the energy has right derivative `E'` with `E' ≤ 2K E` on `[s, t)` and is
continuous on `[s, t]`, then `E t ≤ exp(2K(t - s)) E s`. -/
theorem cyl_gronwall_of_rate {c m K s t : ℝ} {ω : ℝ → B0579.Plane → ℝ}
    (hcont : ContinuousOn (fun σ => cylEnergy c m (ω σ)) (Icc s t))
    (hrate : CylEnergyRate c m K (Ico s t) ω) (hst : s ≤ t) :
    cylEnergy c m (ω t) ≤ Real.exp (2 * K * (t - s)) * cylEnergy c m (ω s) := by
  obtain ⟨E', hE⟩ := hrate
  let h : ℝ → ℝ := fun x => Real.exp (-(2 * K) * x)
  let g : ℝ → ℝ := fun x => cylEnergy c m (ω x) * h x
  let g' : ℝ → ℝ := fun x => E' x * h x + cylEnergy c m (ω x) * (h x * (-(2 * K)))
  have hh : ∀ x : ℝ, HasDerivAt h (h x * (-(2 * K))) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => -(2 * K) * y) (-(2 * K)) x := by
      simpa using (hasDerivAt_id x).const_mul (-(2 * K))
    exact h1.exp
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun x => (hh x).continuousAt
  have hg_cont : ContinuousOn g (Icc s t) := hcont.mul hhc.continuousOn
  have hg' : ∀ x ∈ Ico s t, HasDerivWithinAt g (g' x) (Ici x) x := by
    intro x hx
    exact (hE x hx).1.mul (hh x).hasDerivWithinAt
  have hbound : ∀ x ∈ Ico s t, g' x ≤ 0 := by
    intro x hx
    have hx' := (hE x hx).2
    have hpos : 0 < h x := Real.exp_pos _
    have key : g' x = h x * (E' x - 2 * K * cylEnergy c m (ω x)) := by
      simp only [g']
      ring
    rw [key]
    exact mul_nonpos_of_nonneg_of_nonpos hpos.le (by linarith)
  have hgt := image_le_of_deriv_right_le_deriv_boundary (f := g) (f' := g') (a := s) (b := t)
    hg_cont hg' (B := fun _ => g s) (B' := fun _ => 0) le_rfl continuousOn_const
    (fun x _ => hasDerivWithinAt_const x (Ici x) (g s)) hbound
  have hfin : g t ≤ g s := hgt ⟨hst, le_rfl⟩
  have hexp1 : Real.exp (-(2 * K) * t) * Real.exp (2 * K * t) = 1 := by
    rw [← Real.exp_add, show -(2 * K) * t + 2 * K * t = 0 by ring, Real.exp_zero]
  have hexp2 : Real.exp (2 * K * (t - s)) = Real.exp (-(2 * K) * s) * Real.exp (2 * K * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hgt' : cylEnergy c m (ω t) * Real.exp (-(2 * K) * t) ≤
      cylEnergy c m (ω s) * Real.exp (-(2 * K) * s) := hfin
  calc cylEnergy c m (ω t)
      = (cylEnergy c m (ω t) * Real.exp (-(2 * K) * t)) * Real.exp (2 * K * t) := by
        rw [mul_assoc, hexp1, mul_one]
    _ ≤ (cylEnergy c m (ω s) * Real.exp (-(2 * K) * s)) * Real.exp (2 * K * t) :=
        mul_le_mul_of_nonneg_right hgt' (Real.exp_pos _).le
    _ = Real.exp (2 * K * (t - s)) * cylEnergy c m (ω s) := by
        rw [hexp2]
        ring

/-! ## Elementary facts about the energy and the weight -/

theorem t22_energy_nonneg (c m : ℝ) (g : B0579.Plane → ℝ) : 0 ≤ cylEnergy c m g :=
  integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (NNReal.coe_nonneg _)

theorem t22_energy_congr {c m : ℝ} {g h : B0579.Plane → ℝ}
    (hgh : g =ᵐ[volume.restrict (B0579.cell c)] h) : cylEnergy c m g = cylEnergy c m h := by
  unfold cylEnergy
  refine integral_congr_ae ?_
  filter_upwards [hgh] with x hx
  rw [hx]

/-- The squared `X_{m,c}`-norm is the energy. -/
theorem t22_energy_eq_sq_eLpNorm {c m : ℝ} {g : B0579.Plane → ℝ}
    (hg : MemLp g 2 (B0579.cellMeasure c m)) :
    (eLpNorm g 2 (B0579.cellMeasure c m)).toReal ^ 2 = cylEnergy c m g := by
  have h1 := hg.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  have h3 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h3] at h1
  have h2 : 0 ≤ ∫ x, ‖g x‖ ^ (2 : ℝ) ∂(B0579.cellMeasure c m) :=
    integral_nonneg fun x => by positivity
  rw [h1, ENNReal.toReal_ofReal (Real.rpow_nonneg h2 _), ← Real.rpow_natCast,
    ← Real.rpow_mul h2]
  have h4 : ((2 : ℝ)⁻¹ * ((2 : ℕ) : ℝ)) = 1 := by norm_num
  rw [h4, Real.rpow_one, B0579.integral_cellMeasure]
  unfold cylEnergy
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Real.rpow_two, sq_abs, Real.norm_eq_abs]
  rw [mul_comm]
  rfl

/-- The pointwise bound `|∇ jb^m| ≤ m jb^m` (componentwise), for `m ≥ 0`. -/
theorem t22_pd_jb_le {m : ℝ} (hm : 0 ≤ m) (x : B0579.Plane) :
    |B0579.pd 0 (fun y => B0579.jb y ^ m) x| ≤ m * B0579.jb x ^ m ∧
      |B0579.pd 1 (fun y => B0579.jb y ^ m) x| ≤ m * B0579.jb x ^ m := by
  have hj : 0 < B0579.jb x := B0579.jb_pos x
  have hJ : 0 ≤ B0579.jb x ^ (m - 1) := Real.rpow_nonneg hj.le _
  have hpow : B0579.jb x ^ m = B0579.jb x ^ (m - 1) * B0579.jb x := by
    rw [← Real.rpow_add_one hj.ne']
    ring_nf
  have hq : |2 * x.1| ≤ B0579.jb x := by
    unfold B0579.jb
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (x.1 - 1), sq_nonneg (x.1 + 1), sq_nonneg x.2]
  have hη : |2 * x.2| ≤ B0579.jb x := by
    unfold B0579.jb
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (x.2 - 1), sq_nonneg (x.2 + 1), sq_nonneg x.1]
  constructor
  · rw [B0579.pd_zero_jb_rpow, show 2 * x.1 * m * B0579.jb x ^ (m - 1)
      = (2 * x.1) * (m * B0579.jb x ^ (m - 1)) by ring, abs_mul, abs_of_nonneg (mul_nonneg hm hJ), hpow]
    calc |2 * x.1| * (m * B0579.jb x ^ (m - 1)) ≤ B0579.jb x * (m * B0579.jb x ^ (m - 1)) :=
          mul_le_mul_of_nonneg_right hq (mul_nonneg hm hJ)
      _ = m * (B0579.jb x ^ (m - 1) * B0579.jb x) := by ring
  · rw [B0579.pd_one_jb_rpow, show 2 * x.2 * m * B0579.jb x ^ (m - 1)
      = (2 * x.2) * (m * B0579.jb x ^ (m - 1)) by ring, abs_mul, abs_of_nonneg (mul_nonneg hm hJ), hpow]
    calc |2 * x.2| * (m * B0579.jb x ^ (m - 1)) ≤ B0579.jb x * (m * B0579.jb x ^ (m - 1)) :=
          mul_le_mul_of_nonneg_right hη (mul_nonneg hm hJ)
      _ = m * (B0579.jb x ^ (m - 1) * B0579.jb x) := by ring

/-- The central Gaussian vortex is orthogonal to `∇ jb^m` (T21 `weight_logderiv_isoVelocity`). -/
theorem t22_rotation (m nu s : ℝ) (x : B0579.Plane) :
    (UnforcedLeray.B0146.isoVelocity nu s x).1 * B0579.pd 0 (fun y => B0579.jb y ^ m) x
      + (UnforcedLeray.B0146.isoVelocity nu s x).2 * B0579.pd 1 (fun y => B0579.jb y ^ m) x
      = 0 := by
  obtain ⟨q, η⟩ := x
  rw [UnforcedLeray.B0146.isoVelocity_eq, B0579.pd_zero_jb_rpow, B0579.pd_one_jb_rpow]
  simp only [UnforcedLeray.B0113.vExp]
  ring


/-! ## The dissipation inequality (diffusion + transport + train gap) -/

/-- **Dissipation inequality at one age.** Given the leaf bounds for a function `g`
(integrability, the diffusion bound `2∫gΔg w ≤ C_d E` and the transport identity
`-2∫ g (v·∇g) w = ∫ g² (v·∇w)`), a velocity `v` that differs from a field `iso` orthogonal to
`∇w` by at most `U` on the cell gives
`2∫ g (νΔg - v·∇g) w ≤ (C_d ν + m U) E`. -/
theorem t22_dissipation {ν c m Cd U : ℝ} (hν : 0 < ν) (hm : 0 ≤ m)
    (v : B0579.Plane → UnforcedLeray.Train.Vec) (iso : B0579.Plane → B0579.Plane)
    (hiso : ∀ x, (iso x).1 * B0579.pd 0 (fun y => B0579.jb y ^ m) x +
      (iso x).2 * B0579.pd 1 (fun y => B0579.jb y ^ m) x = 0)
    (hu : ∀ x ∈ B0579.cell c, |v x 0 - (iso x).1| + |v x 1 - (iso x).2| ≤ U)
    (g : B0579.Plane → ℝ)
    (hE : IntegrableOn (fun x => g x ^ 2 * (B0579.density m x : ℝ)) (B0579.cell c))
    (hI1 : IntegrableOn (fun x => g x * lapP g x * (B0579.density m x : ℝ)) (B0579.cell c))
    (hD : 2 * ∫ x in B0579.cell c, g x * lapP g x * (B0579.density m x : ℝ)
      ≤ Cd * cylEnergy c m g)
    (hT1 : IntegrableOn (fun x => g x * (v x 0 * B0579.pd 0 g x + v x 1 * B0579.pd 1 g x) *
      (B0579.density m x : ℝ)) (B0579.cell c))
    (hT2 : IntegrableOn (fun x => g x ^ 2 * (v x 0 * B0579.pd 0 (fun y => B0579.jb y ^ m) x +
      v x 1 * B0579.pd 1 (fun y => B0579.jb y ^ m) x)) (B0579.cell c))
    (hT : -2 * ∫ x in B0579.cell c, g x * (v x 0 * B0579.pd 0 g x + v x 1 * B0579.pd 1 g x) *
        (B0579.density m x : ℝ)
      = ∫ x in B0579.cell c, g x ^ 2 * (v x 0 * B0579.pd 0 (fun y => B0579.jb y ^ m) x +
        v x 1 * B0579.pd 1 (fun y => B0579.jb y ^ m) x)) :
    2 * ∫ x in B0579.cell c, g x * (ν * lapP g x -
        (v x 0 * B0579.pd 0 g x + v x 1 * B0579.pd 1 g x)) * (B0579.density m x : ℝ)
      ≤ (Cd * ν + m * U) * cylEnergy c m g := by
  -- split the integral
  have hsplit : (∫ x in B0579.cell c, g x * (ν * lapP g x -
        (v x 0 * B0579.pd 0 g x + v x 1 * B0579.pd 1 g x)) * (B0579.density m x : ℝ))
      = ν * (∫ x in B0579.cell c, g x * lapP g x * (B0579.density m x : ℝ))
        - (∫ x in B0579.cell c, g x * (v x 0 * B0579.pd 0 g x + v x 1 * B0579.pd 1 g x) *
          (B0579.density m x : ℝ)) := by
    have h1 : (fun x => g x * (ν * lapP g x -
        (v x 0 * B0579.pd 0 g x + v x 1 * B0579.pd 1 g x)) * (B0579.density m x : ℝ))
        = fun x => ν * (g x * lapP g x * (B0579.density m x : ℝ)) -
          g x * (v x 0 * B0579.pd 0 g x + v x 1 * B0579.pd 1 g x) * (B0579.density m x : ℝ) := by
      funext x
      ring
    rw [h1, integral_sub (hI1.const_mul ν) hT1, integral_const_mul]
  -- the transport term
  have hJ : (∫ x in B0579.cell c, g x ^ 2 * (v x 0 * B0579.pd 0 (fun y => B0579.jb y ^ m) x +
        v x 1 * B0579.pd 1 (fun y => B0579.jb y ^ m) x)) ≤ m * U * cylEnergy c m g := by
    have hint : IntegrableOn (fun x => m * U * (g x ^ 2 * (B0579.density m x : ℝ)))
        (B0579.cell c) := hE.const_mul (m * U)
    have hle : (∫ x in B0579.cell c, g x ^ 2 * (v x 0 * B0579.pd 0 (fun y => B0579.jb y ^ m) x +
          v x 1 * B0579.pd 1 (fun y => B0579.jb y ^ m) x))
        ≤ ∫ x in B0579.cell c, m * U * (g x ^ 2 * (B0579.density m x : ℝ)) := by
      refine setIntegral_mono_on hT2 hint (B0579.measurableSet_cell c) fun x hx => ?_
      have hb := t22_pd_jb_le hm x
      have hd : (B0579.density m x : ℝ) = B0579.jb x ^ m := B0579.coe_density m x
      have hW : 0 ≤ B0579.jb x ^ m := Real.rpow_nonneg (B0579.jb_pos x).le _
      have hrot := hiso x
      have hux := hu x hx
      have heq : v x 0 * B0579.pd 0 (fun y => B0579.jb y ^ m) x +
          v x 1 * B0579.pd 1 (fun y => B0579.jb y ^ m) x
          = (v x 0 - (iso x).1) * B0579.pd 0 (fun y => B0579.jb y ^ m) x +
            (v x 1 - (iso x).2) * B0579.pd 1 (fun y => B0579.jb y ^ m) x := by
        linarith
      have hbound : v x 0 * B0579.pd 0 (fun y => B0579.jb y ^ m) x +
          v x 1 * B0579.pd 1 (fun y => B0579.jb y ^ m) x ≤ m * U * (B0579.jb x ^ m) := by
        rw [heq]
        have h1 : (v x 0 - (iso x).1) * B0579.pd 0 (fun y => B0579.jb y ^ m) x
            ≤ |v x 0 - (iso x).1| * (m * B0579.jb x ^ m) :=
          (le_abs_self _).trans (by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left hb.1 (abs_nonneg _))
        have h2 : (v x 1 - (iso x).2) * B0579.pd 1 (fun y => B0579.jb y ^ m) x
            ≤ |v x 1 - (iso x).2| * (m * B0579.jb x ^ m) :=
          (le_abs_self _).trans (by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left hb.2 (abs_nonneg _))
        have hmW : 0 ≤ m * B0579.jb x ^ m := mul_nonneg hm hW
        have h3 : (|v x 0 - (iso x).1| + |v x 1 - (iso x).2|) * (m * B0579.jb x ^ m)
            ≤ U * (m * B0579.jb x ^ m) := mul_le_mul_of_nonneg_right hux hmW
        nlinarith
      rw [hd]
      have hg2 : 0 ≤ g x ^ 2 := sq_nonneg _
      calc g x ^ 2 * (v x 0 * B0579.pd 0 (fun y => B0579.jb y ^ m) x +
            v x 1 * B0579.pd 1 (fun y => B0579.jb y ^ m) x)
          ≤ g x ^ 2 * (m * U * B0579.jb x ^ m) := mul_le_mul_of_nonneg_left hbound hg2
        _ = m * U * (g x ^ 2 * B0579.jb x ^ m) := by ring
    refine hle.trans (le_of_eq ?_)
    rw [integral_const_mul]
    rfl
  rw [hsplit]
  have hνD : ν * (2 * ∫ x in B0579.cell c, g x * lapP g x * (B0579.density m x : ℝ))
      ≤ ν * (Cd * cylEnergy c m g) := mul_le_mul_of_nonneg_left hD hν.le
  linarith [hνD, hJ, hT]


/-! ## The glue -/

/-- **`PartII-b:T22`, conditional form.** The free cylinder energy estimate `FreeCylEnergy` follows
from the six leaves: a regular solution with the datum exists (1) and agrees with every weak
solution (2); the energy of a regular solution is differentiable (3); the diffusion (4) and
transport (5) terms are bounded using the train gap (6). -/
theorem free_cyl_energy_of (hEx : CylClassicalExists) (hUq : CylWeakEqClassical)
    (hDer : RegularEnergyDeriv) (hDiff : CylDiffusionBound) (hIBP : CylTransportIBP)
    (hGap : CylTrainGap) : FreeCylEnergy := by
  intro m hm Sg hSg
  have hm0 : 0 < m := by linarith
  obtain ⟨Cd, hCd⟩ := hDiff m hm0
  obtain ⟨Ct, bt, hCt, hbt, hG⟩ := hGap Sg hSg
  refine ⟨|Cd| + 1, m * Ct, bt, by positivity, mul_pos hm0 hCt, hbt, ?_⟩
  intro p hc1 δ hδ hclose s hs f hf ω hω
  have hν : 0 < p.ν := p.ν_pos
  have hcpos : 0 < p.c := p.c_pos
  by_cases hsT : s ≤ Sg / p.ν
  swap
  · have hsT' : Sg / p.ν < s := not_le.1 hsT
    refine ⟨⟨fun _ => 0, fun τ hτ => absurd (hτ.1.trans_lt hτ.2) (not_lt.2 hsT'.le)⟩,
      fun t hst htT => absurd (hst.trans htT) (not_le.2 hsT')⟩
  -- a regular representative of the weak solution
  obtain ⟨ω', hreg, hω's⟩ := hEx Sg hSg p.ν p.c δ hν hc1 hδ p.train hclose s hs hsT f hf
  have hae := hUq m hm Sg hSg p.ν p.c δ hν hcpos hδ p.train hclose s hs f hf ω' hreg hω's ω hω
  have hEeq : ∀ σ ∈ Icc s (Sg / p.ν), cylEnergy p.c m (ω σ) = cylEnergy p.c m (ω' σ) :=
    fun σ hσ => (t22_energy_congr (hae σ hσ)).symm
  -- the train gap
  have hσ0 : ∀ σ ∈ Icc s (Sg / p.ν), σ ∈ Icc (0 : ℝ) (Sg / p.ν) :=
    fun σ hσ => ⟨hs.trans hσ.1, hσ.2⟩
  have hGg := fun σ (hσ : σ ∈ Icc s (Sg / p.ν)) =>
    hG p.ν p.c δ hν hc1 hδ p.train hclose σ (hσ0 σ hσ)
  obtain ⟨hcont, hderiv⟩ := hDer p.c p.ν m s (Sg / p.ν) p.train.v ω' hcpos hreg
    ⟨Ct * (δ + 1), fun σ hσ => (hGg σ hσ).1⟩
  -- the dissipation bound at each age
  have hdiss : ∀ τ ∈ Ico s (Sg / p.ν),
      2 * ∫ x in B0579.cell p.c, ω' τ x * (p.ν * lapP (ω' τ) x -
          (p.train.v τ x 0 * B0579.pd 0 (ω' τ) x + p.train.v τ x 1 * B0579.pd 1 (ω' τ) x)) *
            (B0579.density m x : ℝ)
        ≤ 2 * ((|Cd| + 1) * p.ν + m * Ct * δ + m * Ct * Real.exp (-bt * p.c ^ 2)) *
            cylEnergy p.c m (ω' τ) := by
    intro τ hτ
    have hτI : τ ∈ Icc s (Sg / p.ν) := ⟨hτ.1, hτ.2.le⟩
    have hsd := hreg.slice τ hτI
    obtain ⟨hE, hI1, hD⟩ := hCd p.c hcpos (ω' τ) hsd
    obtain ⟨hv1, hv2⟩ := hGg τ hτI
    obtain ⟨hT1, hT2, hT⟩ := hIBP p.ν p.c p.train τ (hs.trans hτ.1) hcpos
      ⟨Ct * (δ + 1), hv1⟩ m (ω' τ) hsd
    have key := t22_dissipation (c := p.c) (m := m) (Cd := Cd)
      (U := Ct * (δ + Real.exp (-bt * p.c ^ 2))) hν hm0.le (p.train.v τ)
      (UnforcedLeray.B0146.isoVelocity p.ν τ) (fun x => t22_rotation m p.ν τ x) hv2 (ω' τ)
      hE hI1 hD hT1 hT2 hT
    have hEnn := t22_energy_nonneg p.c m (ω' τ)
    have hexp : 0 ≤ Real.exp (-bt * p.c ^ 2) := (Real.exp_pos _).le
    have hmCt : 0 ≤ m * Ct := (mul_pos hm0 hCt).le
    have h1 : Cd * p.ν ≤ 2 * ((|Cd| + 1) * p.ν) := by
      nlinarith [le_abs_self Cd, abs_nonneg Cd, hν]
    have h2 : m * (Ct * (δ + Real.exp (-bt * p.c ^ 2))) ≤
        2 * (m * Ct * δ + m * Ct * Real.exp (-bt * p.c ^ 2)) := by
      have : 0 ≤ m * Ct * δ + m * Ct * Real.exp (-bt * p.c ^ 2) :=
        add_nonneg (mul_nonneg hmCt hδ) (mul_nonneg hmCt hexp)
      nlinarith
    calc _ ≤ (Cd * p.ν + m * (Ct * (δ + Real.exp (-bt * p.c ^ 2)))) * cylEnergy p.c m (ω' τ) :=
          key
      _ ≤ 2 * ((|Cd| + 1) * p.ν + m * Ct * δ + m * Ct * Real.exp (-bt * p.c ^ 2)) *
            cylEnergy p.c m (ω' τ) := by
          apply mul_le_mul_of_nonneg_right _ hEnn
          linarith
  -- the rate for the regular representative and for the weak solution
  have hrate' : CylEnergyRate p.c m ((|Cd| + 1) * p.ν + m * Ct * δ +
      m * Ct * Real.exp (-bt * p.c ^ 2)) (Ico s (Sg / p.ν)) ω' :=
    ⟨fun τ => 2 * ∫ x in B0579.cell p.c, ω' τ x * (p.ν * lapP (ω' τ) x -
        (p.train.v τ x 0 * B0579.pd 0 (ω' τ) x + p.train.v τ x 1 * B0579.pd 1 (ω' τ) x)) *
          (B0579.density m x : ℝ), fun τ hτ => ⟨(hderiv τ hτ), hdiss τ hτ⟩⟩
  have hrate : CylEnergyRate p.c m ((|Cd| + 1) * p.ν + m * Ct * δ +
      m * Ct * Real.exp (-bt * p.c ^ 2)) (Ico s (Sg / p.ν)) ω := by
    refine ⟨fun τ => 2 * ∫ x in B0579.cell p.c, ω' τ x * (p.ν * lapP (ω' τ) x -
        (p.train.v τ x 0 * B0579.pd 0 (ω' τ) x + p.train.v τ x 1 * B0579.pd 1 (ω' τ) x)) *
          (B0579.density m x : ℝ), fun τ hτ => ⟨?_, ?_⟩⟩
    · refine (hderiv τ hτ).congr_of_eventuallyEq ?_ (hEeq τ ⟨hτ.1, hτ.2.le⟩)
      filter_upwards [Icc_mem_nhdsGE hτ.2] with σ hσ using hEeq σ ⟨hτ.1.trans hσ.1, hσ.2⟩
    · rw [hEeq τ ⟨hτ.1, hτ.2.le⟩]
      exact hdiss τ hτ
  refine ⟨hrate, fun t hst htT => ?_⟩
  -- Gronwall for the regular representative
  have hgr : cylEnergy p.c m (ω' t) ≤
      Real.exp (2 * ((|Cd| + 1) * p.ν + m * Ct * δ + m * Ct * Real.exp (-bt * p.c ^ 2)) *
        (t - s)) * cylEnergy p.c m (ω' s) := by
    refine cyl_gronwall_of_rate (hcont.mono (Icc_subset_Icc le_rfl htT)) ?_ hst
    obtain ⟨E', hE'⟩ := hrate'
    exact ⟨E', fun τ hτ => hE' τ ⟨hτ.1, lt_of_lt_of_le hτ.2 htT⟩⟩
  have htI : t ∈ Icc s (Sg / p.ν) := ⟨hst, htT⟩
  have hsI : s ∈ Icc s (Sg / p.ν) := ⟨le_rfl, hsT⟩
  have hωt : MemLp (ω t) 2 (B0579.cellMeasure p.c m) := hω.memX t hst
  have hfm : MemLp f 2 (B0579.cellMeasure p.c m) := hf.memLp m
  have hEs : cylEnergy p.c m (ω s) = cylEnergy p.c m f := t22_energy_congr hω.initial
  have hsq : (eLpNorm (ω t) 2 (B0579.cellMeasure p.c m)).toReal ^ 2 ≤
      Real.exp (2 * ((|Cd| + 1) * p.ν + m * Ct * δ + m * Ct * Real.exp (-bt * p.c ^ 2)) *
        (t - s)) * (eLpNorm f 2 (B0579.cellMeasure p.c m)).toReal ^ 2 := by
    rw [t22_energy_eq_sq_eLpNorm hωt, t22_energy_eq_sq_eLpNorm hfm, hEeq t htI, ← hEs, hEeq s hsI]
    exact hgr
  set K : ℝ := (|Cd| + 1) * p.ν + m * Ct * δ + m * Ct * Real.exp (-bt * p.c ^ 2) with hK
  have hexp2 : Real.exp (2 * K * (t - s)) = Real.exp (K * (t - s)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hreal : (eLpNorm (ω t) 2 (B0579.cellMeasure p.c m)).toReal ≤
      Real.exp (K * (t - s)) * (eLpNorm f 2 (B0579.cellMeasure p.c m)).toReal := by
    have hnn : 0 ≤ Real.exp (K * (t - s)) * (eLpNorm f 2 (B0579.cellMeasure p.c m)).toReal :=
      mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg
    refine (pow_le_pow_iff_left₀ ENNReal.toReal_nonneg hnn (two_ne_zero)).1 ?_
    rw [mul_pow, ← hexp2]
    exact hsq
  have hft : eLpNorm f 2 (B0579.cellMeasure p.c m) ≠ ⊤ := hfm.eLpNorm_lt_top.ne
  have hwt : eLpNorm (ω t) 2 (B0579.cellMeasure p.c m) ≠ ⊤ := hωt.eLpNorm_lt_top.ne
  calc eLpNorm (ω t) 2 (B0579.cellMeasure p.c m)
      = ENNReal.ofReal (eLpNorm (ω t) 2 (B0579.cellMeasure p.c m)).toReal :=
        (ENNReal.ofReal_toReal hwt).symm
    _ ≤ ENNReal.ofReal (Real.exp (K * (t - s)) *
          (eLpNorm f 2 (B0579.cellMeasure p.c m)).toReal) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (Real.exp (K * (t - s))) * eLpNorm f 2 (B0579.cellMeasure p.c m) := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal hft]

end UnforcedLeray.Short.IIb
