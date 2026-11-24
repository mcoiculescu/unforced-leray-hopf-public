import UnforcedLeray.Units.B0140
import UnforcedLeray.Units.B0238
import UnforcedLeray.Units.B0579
import UnforcedLeray.Lib.AxisymmetricB.Lift
import UnforcedLeray.Blueprint.Construction.Planar

/-!
# Part III-a: shared definitions (stress spaces, full clock, canonical transfer, flat causal inverse)

Source of record: `the November 2 reference manuscript` (SP), lines 2664-3860.

Conventions.
* Cylinder fields live on the plane `ℝ × ℝ = (q, η)`; integrals are over the centered cell
  `B0579.cell c = [-c/2, c/2) × ℝ` and are UNNORMALIZED unless a `dq/c` is stated
  (`Axi.ageμ c a` carries the normalized cell measure, as in `lintegral_Nv_rpow`).
* Planar vorticities are complex valued (the Gaussian seed is a complex angular-two mode); the
  real physical space is the real subspace, and norms of a complex field are the Hermitian norms
  with the same operator constants (`‖f‖² = ‖Re f‖² + ‖Im f‖²`). Weighted spaces are
  `X_{m,c} = L²(cell c, ⟨x⟩^{2m}dx)` via `B0579.cellMeasure c m` (density `(1+q²+η²)^m`).
* The actual train is `B0140.TrainSol ν c` (SP 241-330); its vorticity is `B0238.Ec`.
* The full (linearised) evolution `U(s,t)` is characterised by weak solutions of the linearised
  vorticity equation `ω_s + v·∇ω + (K_cω)·∇E = νΔω` around the actual train (`IsLinearisedFlow`),
  with the zero-circulation Biot-Savart velocity characterised by `IsBiotSavart`; no operator is
  assumed, and `K_c ω` is the unique `L²` solution of `div u = 0`, `curl u = ω`.
* Coordinates of the stress-space chart are `(s, (q, η)) ∈ ℝ × (ℝ × ℝ)` as in `Axi.ageμ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-! ## Clocks and scalings (SP 2832-2850, 3110-3120) -/

/-- `a(s) = 1 + νs`. -/
def clockA (ν s : ℝ) : ℝ := 1 + ν * s

/-- `θ(s) = (ν a(s))⁻¹` (SP 3109, 3116). -/
def clockTheta (ν s : ℝ) : ℝ := (ν * clockA ν s)⁻¹

/-- The age at heat clock `θ`: `s = (1 - νθ)/(ν²θ)` (SP 3303). -/
def clockAge (ν θ : ℝ) : ℝ := (1 - ν * θ) / (ν ^ 2 * θ)

/-- The cell length `d = c/√a` at age with `a = clockA` (SP 3110). -/
def cellLen (c a : ℝ) : ℝ := c / Real.sqrt a

/-- The gain `g(s) = exp(γ s/(1+νs))` (SP 2825). -/
def gainG (γ ν s : ℝ) : ℝ := Real.exp (γ * s / (1 + ν * s))

/-- `J_a W(x) = a^{-2} W(x/√a)` (SP 2983). -/
def Jscale (a : ℝ) (W : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  ((a ^ (-2 : ℝ) : ℝ) : ℂ) * W (x.1 / Real.sqrt a, x.2 / Real.sqrt a)

/-- `J_a⁻¹ f(y) = a² f(√a y)`. -/
def JscaleInv (a : ℝ) (f : ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ :=
  ((a ^ 2 : ℝ) : ℂ) * f (Real.sqrt a * y.1, Real.sqrt a * y.2)

/-! ## Weighted spaces on the cylinder (SP 2823-2827) -/

/-- `‖f‖_{X_{m,c}}`, the norm of `L²(C_c, ⟨x⟩^{2m}dx)` (complex valued). -/
def xNorm (c m : ℝ) (f : ℝ × ℝ → ℂ) : ℝ≥0∞ := eLpNorm f 2 (B0579.cellMeasure c m)

/-- Zero circulation: integrable on the cell with vanishing integral. -/
def HasZeroCirculation (c : ℝ) (f : ℝ × ℝ → ℂ) : Prop :=
  IntegrableOn f (B0579.cell c) ∧ ∫ x in B0579.cell c, f x = 0

/-- Distributional derivative on the cylinder for complex fields, tested against real
cylinder tests (both pairings converge). -/
def HasWeakCellDerivC (c : ℝ) (j : Fin 2) (φ g : ℝ × ℝ → ℂ) : Prop :=
  (∀ ψ, B0579.IsCylTest c ψ →
    IntegrableOn (fun x => φ x * (B0579.pd j ψ x : ℂ)) (B0579.cell c) ∧
      IntegrableOn (fun x => g x * (ψ x : ℂ)) (B0579.cell c)) ∧
  ∀ ψ, B0579.IsCylTest c ψ →
    ∫ x in B0579.cell c, φ x * (B0579.pd j ψ x : ℂ) = -∫ x in B0579.cell c, g x * (ψ x : ℂ)

/-- The `H^1_{-m,c}` norm of `φ` with weak gradient `g`: `‖⟨x⟩^{-m}(φ, ∇φ)‖_{L²}`. -/
def h1Norm (c m : ℝ) (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ) : ℝ≥0∞ :=
  (xNorm c (-m) φ ^ 2 + ∑ j, xNorm c (-m) (g j) ^ 2) ^ (1 / 2 : ℝ)

/-- The weak-source norm `‖f‖_{Z^{-1}_{m,c}} = ‖f‖_{(H^1_{-m,c})^*}` for `f ∈ X_{m,c}` with the
unweighted pairing `⟨f, φ⟩ = ∫_cell f φ` (SP 2823-2826). -/
def negNorm (c m : ℝ) (f : ℝ × ℝ → ℂ) : ℝ≥0∞ :=
  ⨆ (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ) (_ : ∀ j, HasWeakCellDerivC c j φ (g j))
    (_ : h1Norm c m φ g ≤ 1), ENNReal.ofReal ‖∫ x in B0579.cell c, f x * φ x‖

/-! ## The Biot-Savart velocity and the linearised flow (SP 2819-2830, 3108-3125) -/

/-- `u = K_c ω`: `u ∈ L²(cell)`, `div u = 0`, `curl u = ∂_q u_η - ∂_η u_q = ω` in distributions
on the cylinder (components `(q, η)`). -/
def IsBiotSavart (c : ℝ) (ω : ℝ × ℝ → ℂ) (u : ℝ × ℝ → Fin 2 → ℂ) : Prop :=
  (∀ j, MemLp (fun x => u x j) 2 (volume.restrict (B0579.cell c))) ∧
  (∀ ψ, B0579.IsCylTest c ψ → ∫ x in B0579.cell c,
      (u x 0 * (B0579.pd 0 ψ x : ℂ) + u x 1 * (B0579.pd 1 ψ x : ℂ)) = 0) ∧
  (∀ ψ, B0579.IsCylTest c ψ → ∫ x in B0579.cell c, ω x * (ψ x : ℂ) =
      ∫ x in B0579.cell c, (u x 0 * (B0579.pd 1 ψ x : ℂ) - u x 1 * (B0579.pd 0 ψ x : ℂ)))

/-- The planar Laplacian of a real test function. -/
def lapP (φ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  B0579.pd 0 (B0579.pd 0 φ) x + B0579.pd 1 (B0579.pd 1 φ) x

/-- The tested right-hand side of the linearised vorticity equation at age `r`:
`ω(νΔφ + v·∇φ) - (u·∇E)φ`, where `(v, E)` is the actual train velocity and vorticity. -/
def flowIntegrand {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (ω : ℝ × ℝ → ℂ)
    (u : ℝ × ℝ → Fin 2 → ℂ) (r : ℝ) (φ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℂ :=
  ω x * ((ν * lapP φ x + (tr.v r x 0 * B0579.pd 0 φ x + tr.v r x 1 * B0579.pd 1 φ x) : ℝ) : ℂ) -
    (u x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x : ℂ) +
      u x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℂ)) * (φ x : ℂ)

/-- `ω` (with velocities `u`) is a weak solution on `[t, ∞)` in `X_{m,c}` of
`ω_s + v·∇ω + (K_cω)·∇E = νΔω` with datum `f` at age `t`, `(v, E)` the actual train. -/
structure IsLinearisedFlow (ν c m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t : ℝ)
    (f : ℝ × ℝ → ℂ) (ω : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ) : Prop where
  initial : ω t =ᵐ[volume.restrict (B0579.cell c)] f
  memX : ∀ s, t ≤ s → MemLp (ω s) 2 (B0579.cellMeasure c m)
  strongCont : ∀ s, t ≤ s →
    Tendsto (fun s' => xNorm c m (ω s' - ω s)) (𝓝[Ici t] s) (𝓝 0)
  biotSavart : ∀ s, t ≤ s → IsBiotSavart c (ω s) (u s)
  integrable : ∀ φ, B0579.IsCylTest c φ → ∀ r, t ≤ r →
    IntegrableOn (flowIntegrand tr (ω r) (u r) r φ) (B0579.cell c)
  timeIntegrable : ∀ φ, B0579.IsCylTest c φ → ∀ s, t ≤ s →
    IntervalIntegrable (fun r => ∫ x in B0579.cell c, flowIntegrand tr (ω r) (u r) r φ x)
      volume t s
  weak : ∀ φ, B0579.IsCylTest c φ → ∀ s, t ≤ s →
    ∫ x in B0579.cell c, ω s x * (φ x : ℂ) =
      (∫ x in B0579.cell c, f x * (φ x : ℂ)) +
        ∫ r in t..s, (∫ x in B0579.cell c, flowIntegrand tr (ω r) (u r) r φ x)

/-- The strip `0 < Re μ < 1/4` and its compact subsets `K`. -/
def IsAdmissibleK (K : Set ℂ) : Prop :=
  IsCompact K ∧ ∀ μ ∈ K, 0 < μ.re ∧ μ.re < 1 / 4

end UnforcedLeray.Short.IIIa
