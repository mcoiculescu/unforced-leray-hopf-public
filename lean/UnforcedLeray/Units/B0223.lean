import UnforcedLeray.Units.B0223.VecInvariance

/-!
# B0223: the outer semigroup `S_ε(t)`, its `L²` bound `e^{-t/4}`, the resolvent bound `γ⁻¹`

Blueprint unit B0223 (label `eq:st18-t00116`), `paper/main.tex` lines 3341–3368
(§`sec:st18-2325`), depending on B0220 (`eq:st18-t00113`, the lift and `J_ε`), B0221
(`eq:st18-t00114`, `A_ε`) and B0222 (`eq:st18-t00115`, `A_ε^vec`).

The manuscript states (tex lines 3343–3368): the outer operator `νε²Δ_x + x·∇/2 + 1/2 - ∂_τ`
has the time-periodic semigroup
`S_ε(t)F(x, τ) = e^{t/2} [e^{νε²(e^t - 1)Δ} F(·, τ - t)](e^{t/2} x)`, of `L²` norm at most
`e^{-t/4}`; the phase translation is unitary; for `γ = Re μ + 1/4 > 0` the exact free inverse
`R_ε(μ) = (μ - A_ε)^{-1}`, conjugated to `H` by `J_ε`, satisfies `‖R_ε(μ)‖_{H→H} ≤ γ⁻¹`
uniformly in `ε, c, ν`; the same holds for `A_ε^vec`; the families are holomorphic in `μ` on
the half-plane.

## Formalization map

| Manuscript | Lean |
|---|---|
| `τ`-periodic `L²(dx dτ)`, period `P = 2εc` | `X E P = L²(ℝ³ × ℝ/Pℤ; E)` (`B0223/Group.lean`), `E` a complex Hilbert space: `ℂ` (scalar), `SpaceC = ℂ³` (vector, Cartesian components) |
| `S_ε(t)` | `Sop (ν * ε ^ 2) t`; formula `S_formula`; package `outerSemigroup` (`Infra.ExpSemigroup`, `M = 1`, `ω = -1/4`) |
| `‖S_ε(t)‖ ≤ e^{-t/4}` | `norm_S_le` |
| phase translation unitary | `transEquiv t : X E P ≃ₗᵢ[ℂ] X E P`, `phase_translation_unitary` |
| `R(μ) = (μ - G)^{-1}` on `L²(dx dτ)` | `physRes = (outerSemigroup _ _).laplace` (bypass BP4: Laplace transform), `physRes_left`, `physRes_right` (two-sided inverse on the generator graph `IsGenPair`) |
| `J_ε` (complexified) | `liftSc` (scalar), `liftVec` (meridional, `ℂ² → ℂ³` frame) (`B0223/Lift.lean`) |
| `R_ε(μ)`, `R_ε^vec(μ)` on `H` | `Reps`, `RepsVec` `= J_ε† R(μ) J_ε` |
| `‖R_ε(μ)‖_{H→H} ≤ γ⁻¹`, uniformly in `ε, c, ν` | `norm_Reps_le`, `norm_RepsVec_le` |
| holomorphy on `{Re μ > -1/4}` | `differentiableOn_Reps`, `differentiableOn_RepsVec` (operator-norm holomorphy) |
| `R_ε(μ) = ∫_0^∞ e^{-μt} S_ε(t) dt` (proof outline) | `Reps_apply`, `RepsVec_apply` |
| `R_ε(μ) = (μ - A_ε)^{-1}` | `Reps_left` (left inverse on the conjugated generator graph), `Reps_right` (right inverse), `J_Reps` (`J_ε R_ε(μ) = R(μ) J_ε`); same for `RepsVec` |
| `S_ε(t)` preserves the axisymmetric (meridional) lifts | `liftInvariant_sc` (`B0223/Invariance.lean`), `liftInvariant_vec` (`B0223/VecInvariance.lean`) |
| the whole unit | `B0223_statement` (scalar), `B0223_vec_statement` (vector) |

## Conventions and scope

* Complex coefficients: `μ` is complex, so all operators act on complex-valued fields
  (`X ℂ P`, `HSpace c ℂ`, `HSpace c MeridC`). B0220–B0222 work with real fields; `liftSc`,
  `liftVec` are the complexifications of B0220's `J` (same formulas,
  `coeFn_liftSc`, `coeFn_liftVec`).
* The vector semigroup is `Sop` with `E = ℂ³`: the heat operator acts componentwise in
  Cartesian components (blueprint proof outline).
* The generator is not constructed (bypass BP4). "`(μ - A_ε)^{-1}`" is expressed through the
  graph `IsGenPair S x y` (`d/dt S(t)x = S(t)y`, `t > 0`), which for a strongly continuous
  semigroup is the graph of its generator; on `H`, the graph of `A_ε` is the conjugate
  `{(b, c) : IsGenPair S (J b) (J c)}`, the definition of B0221 (`AepsOp`) and B0222
  (`AepsVecOp`) with `G` the generator of `S_ε`.
* The conjugation is exact: `S_ε(t)` maps lifts to lifts (`LiftInvariant`, proved for the
  scalar lift by rotation invariance of the Gaussian, `liftInvariant_sc`, and for the
  meridional lift by equivariance under the reflections fixing `e₃`, `liftInvariant_vec`), so
  `J_ε R_ε(μ) = R(μ) J_ε` and `R_ε(μ)` is a two-sided inverse of `μ - A_ε`.
* Hypotheses: `ν > 0`, `ε > 0`, `c > 0` (tex line 3281), `γ = Re μ + 1/4 > 0` (tex line 3357).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace UnforcedLeray.B0223

open UnforcedLeray.Infra UnforcedLeray.B0220

variable {P : ℝ} [Fact (0 < P)]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {ν ε c : ℝ}

/-! ### The outer semigroup (tex lines 3346–3354) -/

/-- **The time-periodic outer semigroup** `S_ε(t)` of `νε²Δ_x + x·∇/2 + 1/2 - ∂_τ`
(tex lines 3346–3352) on the `τ`-periodic `L²(dx dτ; E)`, as an exponentially bounded strongly
continuous semigroup with `M = 1`, `ω = -1/4`. -/
def outerS (hν : 0 < ν) (ε : ℝ) : ExpSemigroup (X E P) :=
  outerSemigroup (ν * ε ^ 2) (by positivity)

theorem outerS_T (hν : 0 < ν) (ε t : ℝ) :
    (outerS (E := E) (P := P) hν ε).T t = Sop (ν * ε ^ 2) t := rfl

/-- **The formula** (tex lines 3350–3352):
`S_ε(t)F(x, τ) = e^{t/2} [e^{νε²(e^t - 1)Δ} F(·, τ - t)](e^{t/2} x)` for `t > 0`, a.e. -/
theorem S_formula (hν : 0 < ν) (hε : 0 < ε) {t : ℝ} (ht : 0 < t) (F : X E P) :
    ((outerS hν ε).T t F : PSpace P → E) =ᵐ[volume] fun z => Real.exp (t / 2) •
      Heat.heatConv (ιx P) (ν * ε ^ 2 * (Real.exp t - 1))
        (fun w => F (w.1, w.2 - (t : AddCircle P))) (Real.exp (t / 2) • z.1, z.2) :=
  Sop_rep (by positivity) ht F

/-- **`‖S_ε(t)‖_{L²(dx dτ)} ≤ e^{-t/4}`** (tex line 3353). -/
theorem norm_S_le (hν : 0 < ν) (ε t : ℝ) :
    ‖(outerS (E := E) (P := P) hν ε).T t‖ ≤ Real.exp (-t / 4) :=
  norm_Sop_le _ t

/-- **The phase translation is unitary** (tex line 3354): `F ↦ F(·, · - t)` is a linear
isometric equivalence of `L²(dx dτ)` onto itself. -/
theorem phase_translation_unitary (t : ℝ) (F : X E P) :
    transEquiv t F = transC t F ∧ ‖transEquiv t F‖ = ‖F‖ :=
  ⟨rfl, (transEquiv t).norm_map F⟩

/-! ### The physical resolvent (tex lines 3355–3361) -/

/-- **The free inverse on `L²(dx dτ)`**: `R(μ) = ∫_0^∞ e^{-μt} S_ε(t) dt` (bypass BP4). -/
def physRes (hν : 0 < ν) (ε : ℝ) (μ : ℂ) : X E P →L[ℂ] X E P :=
  (outerS hν ε).laplace μ

theorem omega_lt {μ : ℂ} (hγ : 0 < μ.re + 1 / 4) (hν : 0 < ν) (ε : ℝ) :
    (outerS (E := E) (P := P) hν ε).ω < μ.re := by
  simp only [outerS, outerSemigroup_ω]
  linarith

theorem bound_eq {μ : ℂ} (hν : 0 < ν) (ε : ℝ) :
    (outerS (E := E) (P := P) hν ε).M / (μ.re - (outerS (E := E) (P := P) hν ε).ω) =
      (μ.re + 1 / 4)⁻¹ := by
  simp only [outerS, outerSemigroup_ω, outerSemigroup_M]
  rw [one_div]
  ring_nf

theorem norm_physRes_le (hν : 0 < ν) (ε : ℝ) {μ : ℂ} (hγ : 0 < μ.re + 1 / 4) :
    ‖(physRes (E := E) (P := P) hν ε μ)‖ ≤ (μ.re + 1 / 4)⁻¹ := by
  rw [← bound_eq (E := E) (P := P) (μ := μ) hν ε]
  exact (outerS hν ε).norm_laplace_le (omega_lt hγ hν ε)

/-- `R(μ)(μF - GF) = F` on the generator graph of `S_ε`. -/
theorem physRes_left (hν : 0 < ν) (ε : ℝ) {μ : ℂ} (hγ : 0 < μ.re + 1 / 4) {F G : X E P}
    (h : IsGenPair (outerS hν ε) F G) : physRes hν ε μ (μ • F - G) = F :=
  laplace_left _ (omega_lt hγ hν ε) h

/-- `R(μ)Z` lies in the generator graph with image `μ R(μ)Z - Z`. -/
theorem physRes_right (hν : 0 < ν) (ε : ℝ) {μ : ℂ} (hγ : 0 < μ.re + 1 / 4) (Z : X E P) :
    IsGenPair (outerS hν ε) (physRes hν ε μ Z) (μ • physRes hν ε μ Z - Z) :=
  laplace_right _ (omega_lt hγ hν ε) Z

/-! ### The scalar resolvent on `H` (tex lines 3355–3366) -/

/-- **The exact free inverse `R_ε(μ)` conjugated to `H` by `J_ε`** (tex lines 3355–3363):
`J_ε† R(μ) J_ε` with the complex scalar lift `liftSc`, `P = 2εc`. -/
def Reps (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) (μ : ℂ) :
    HSpace c E →L[ℂ] HSpace c E :=
  compress (liftSc hε hc hP) (physRes (E := E) (P := P) hν ε μ)

/-- **`‖R_ε(μ)‖_{H→H} ≤ γ⁻¹`, `γ = Re μ + 1/4 > 0`, uniformly in `ε, c, ν`**
(display `eq:st18-t00116`, tex lines 3361–3366). -/
theorem norm_Reps_le (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) {μ : ℂ}
    (hγ : 0 < μ.re + 1 / 4) : ‖Reps (E := E) hν hε hc hP μ‖ ≤ (μ.re + 1 / 4)⁻¹ :=
  (norm_compress_le _ _).trans (norm_physRes_le hν ε hγ)

/-- **Holomorphy** of `μ ↦ R_ε(μ)` on `{Re μ > -1/4}` (tex lines 3367–3368), in operator norm. -/
theorem differentiableOn_Reps (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) :
    DifferentiableOn ℂ (Reps (E := E) hν hε hc hP) {μ : ℂ | 0 < μ.re + 1 / 4} := by
  refine differentiableOn_compress _ ((outerS hν ε).differentiableOn_laplace.mono ?_)
  intro μ hμ
  exact omega_lt hμ hν ε

/-- **The Laplace formula** `R_ε(μ)b = ∫_0^∞ e^{-μt} J_ε† S_ε(t) J_ε b dt` (blueprint proof
outline). -/
theorem Reps_apply (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) {μ : ℂ}
    (hγ : 0 < μ.re + 1 / 4) (b : HSpace c E) :
    Reps hν hε hc hP μ b = ∫ t in Ioi (0 : ℝ), Complex.exp (-(μ * t)) •
      ContinuousLinearMap.adjoint (liftSc hε hc hP).toContinuousLinearMap
        ((outerS hν ε).T t (liftSc hε hc hP b)) :=
  compress_laplace_apply _ _ (omega_lt hγ hν ε) b

/-- **`R_ε(μ)` is a left inverse of `μ - A_ε`** on the graph of `A_ε` (the conjugate of the
generator of `S_ε` by `J_ε`, tex lines 3340–3347): `R_ε(μ)(μ b - A_ε b) = b`. -/
theorem Reps_left (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) {μ : ℂ}
    (hγ : 0 < μ.re + 1 / 4) {b Ab : HSpace c E}
    (h : IsGenPair (outerS hν ε) (liftSc hε hc hP b) (liftSc hε hc hP Ab)) :
    Reps hν hε hc hP μ (μ • b - Ab) = b :=
  compress_left _ _ (omega_lt hγ hν ε) h

/-- The outer semigroup maps scalar lifts to scalar lifts (axisymmetry, tex lines 3341–3347). -/
theorem liftInvariant_outerS (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) :
    LiftInvariant (outerS hν ε) (liftSc (E := E) hε hc hP) :=
  liftInvariant_sc (by positivity) hε hc hP

/-- **Conjugation identity** `J_ε R_ε(μ) = R(μ) J_ε` (tex lines 3341–3347, 3363). -/
theorem J_Reps (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) {μ : ℂ}
    (hγ : 0 < μ.re + 1 / 4) (b : HSpace c E) :
    liftSc hε hc hP (Reps hν hε hc hP μ b) = physRes hν ε μ (liftSc hε hc hP b) :=
  lift_compress_laplace _ _ (liftInvariant_outerS hν hε hc hP) (omega_lt hγ hν ε) b

/-- **`R_ε(μ)` is a right inverse of `μ - A_ε`**: `R_ε(μ)z` lies in the graph of `A_ε` with
`A_ε R_ε(μ)z = μ R_ε(μ)z - z`. -/
theorem Reps_right (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) {μ : ℂ}
    (hγ : 0 < μ.re + 1 / 4) (z : HSpace c E) :
    IsGenPair (outerS hν ε) (liftSc hε hc hP (Reps hν hε hc hP μ z))
      (liftSc hε hc hP (μ • Reps hν hε hc hP μ z - z)) :=
  compress_right _ _ (liftInvariant_outerS hν hε hc hP) (omega_lt hγ hν ε) z

/-! ### The vector resolvent on `H` (tex lines 3364–3368, `eq:st18-t00115`) -/

/-- **The meridional free inverse `R_ε^vec(μ)`** conjugated to `H = L²(s^{-3/2}; ℂ²)` by the
meridional lift; the semigroup acts on `ℂ³`-valued fields in Cartesian components. -/
def RepsVec (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) (μ : ℂ) :
    HSpace c MeridC →L[ℂ] HSpace c MeridC :=
  compress (liftVec hε hc hP) (physRes (E := SpaceC) (P := P) hν ε μ)

theorem norm_RepsVec_le (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) {μ : ℂ}
    (hγ : 0 < μ.re + 1 / 4) : ‖RepsVec hν hε hc hP μ‖ ≤ (μ.re + 1 / 4)⁻¹ :=
  (norm_compress_le _ _).trans (norm_physRes_le hν ε hγ)

theorem differentiableOn_RepsVec (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c)
    (hP : P = 2 * ε * c) :
    DifferentiableOn ℂ (RepsVec hν hε hc hP) {μ : ℂ | 0 < μ.re + 1 / 4} := by
  refine differentiableOn_compress _ ((outerS hν ε).differentiableOn_laplace.mono ?_)
  intro μ hμ
  exact omega_lt hμ hν ε

theorem RepsVec_apply (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) {μ : ℂ}
    (hγ : 0 < μ.re + 1 / 4) (b : HSpace c MeridC) :
    RepsVec hν hε hc hP μ b = ∫ t in Ioi (0 : ℝ), Complex.exp (-(μ * t)) •
      ContinuousLinearMap.adjoint (liftVec hε hc hP).toContinuousLinearMap
        ((outerS hν ε).T t (liftVec hε hc hP b)) :=
  compress_laplace_apply _ _ (omega_lt hγ hν ε) b

theorem RepsVec_left (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) {μ : ℂ}
    (hγ : 0 < μ.re + 1 / 4) {b Ab : HSpace c MeridC}
    (h : IsGenPair (outerS hν ε) (liftVec hε hc hP b) (liftVec hε hc hP Ab)) :
    RepsVec hν hε hc hP μ (μ • b - Ab) = b :=
  compress_left _ _ (omega_lt hγ hν ε) h

/-- The outer semigroup maps meridional lifts to meridional lifts (the meridional subspace is
invariant, blueprint proof outline). -/
theorem liftInvariant_outerS_vec (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) :
    LiftInvariant (outerS hν ε) (liftVec hε hc hP) :=
  liftInvariant_vec (by positivity) hε hc hP

/-- `J_ε R_ε^vec(μ) = R(μ) J_ε`. -/
theorem J_RepsVec (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) {μ : ℂ}
    (hγ : 0 < μ.re + 1 / 4) (b : HSpace c MeridC) :
    liftVec hε hc hP (RepsVec hν hε hc hP μ b) = physRes hν ε μ (liftVec hε hc hP b) :=
  lift_compress_laplace _ _ (liftInvariant_outerS_vec hν hε hc hP) (omega_lt hγ hν ε) b

theorem RepsVec_right (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) {μ : ℂ}
    (hγ : 0 < μ.re + 1 / 4) (z : HSpace c MeridC) :
    IsGenPair (outerS hν ε) (liftVec hε hc hP (RepsVec hν hε hc hP μ z))
      (liftVec hε hc hP (μ • RepsVec hν hε hc hP μ z - z)) :=
  compress_right _ _ (liftInvariant_outerS_vec hν hε hc hP) (omega_lt hγ hν ε) z

/-! ### The whole unit -/

/-- **Unit B0223, scalar part** (tex lines 3341–3368), with the manuscript's hypotheses
`ν, ε, c > 0`, `P = 2εc`: the semigroup formula and law, `‖S_ε(t)‖ ≤ e^{-t/4}`, unitary phase
translation, and for `γ = Re μ + 1/4 > 0` the bound `‖R_ε(μ)‖_{H→H} ≤ γ⁻¹`, the Laplace
formula, the conjugation identity `J_ε R_ε(μ) = R(μ) J_ε`, `R_ε(μ) = (μ - A_ε)^{-1}` (left and
right inverse on the graph of `A_ε`), and holomorphy on the half-plane. -/
theorem B0223_statement (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) :
    (∀ t : ℝ, 0 < t → ∀ F : X E P, ((outerS hν ε).T t F : PSpace P → E) =ᵐ[volume]
      fun z => Real.exp (t / 2) • Heat.heatConv (ιx P) (ν * ε ^ 2 * (Real.exp t - 1))
        (fun w => F (w.1, w.2 - (t : AddCircle P))) (Real.exp (t / 2) • z.1, z.2)) ∧
    (outerS (E := E) (P := P) hν ε).T 0 = 1 ∧
    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      (outerS (E := E) (P := P) hν ε).T (s + t) = (outerS hν ε).T s ∘L (outerS hν ε).T t) ∧
    (∀ t : ℝ, 0 ≤ t → ‖(outerS (E := E) (P := P) hν ε).T t‖ ≤ Real.exp (-t / 4)) ∧
    (∀ (t : ℝ) (F : X E P), ‖transEquiv t F‖ = ‖F‖) ∧
    (∀ μ : ℂ, 0 < μ.re + 1 / 4 → ‖Reps (E := E) hν hε hc hP μ‖ ≤ (μ.re + 1 / 4)⁻¹) ∧
    (∀ μ : ℂ, 0 < μ.re + 1 / 4 → ∀ b : HSpace c E,
      Reps hν hε hc hP μ b = ∫ t in Ioi (0 : ℝ), Complex.exp (-(μ * t)) •
        ContinuousLinearMap.adjoint (liftSc hε hc hP).toContinuousLinearMap
          ((outerS hν ε).T t (liftSc hε hc hP b))) ∧
    (∀ μ : ℂ, 0 < μ.re + 1 / 4 → ∀ b : HSpace c E,
      liftSc hε hc hP (Reps hν hε hc hP μ b) = physRes hν ε μ (liftSc hε hc hP b)) ∧
    (∀ μ : ℂ, 0 < μ.re + 1 / 4 → ∀ b Ab : HSpace c E,
      IsGenPair (outerS hν ε) (liftSc hε hc hP b) (liftSc hε hc hP Ab) →
        Reps hν hε hc hP μ (μ • b - Ab) = b) ∧
    (∀ μ : ℂ, 0 < μ.re + 1 / 4 → ∀ z : HSpace c E,
      IsGenPair (outerS hν ε) (liftSc hε hc hP (Reps hν hε hc hP μ z))
        (liftSc hε hc hP (μ • Reps hν hε hc hP μ z - z))) ∧
    DifferentiableOn ℂ (Reps (E := E) hν hε hc hP) {μ : ℂ | 0 < μ.re + 1 / 4} :=
  ⟨fun _ ht F => S_formula hν hε ht F, Sop_zero _, fun _ _ hs ht => Sop_add (by positivity) hs ht,
    fun t _ => norm_S_le hν ε t, fun t F => (transEquiv t).norm_map F,
    fun _ hγ => norm_Reps_le hν hε hc hP hγ, fun _ hγ b => Reps_apply hν hε hc hP hγ b,
    fun _ hγ b => J_Reps hν hε hc hP hγ b, fun _ hγ _ _ h => Reps_left hν hε hc hP hγ h,
    fun _ hγ z => Reps_right hν hε hc hP hγ z, differentiableOn_Reps hν hε hc hP⟩

/-- **Unit B0223, vector part** (tex lines 3364–3368): the same bound, Laplace formula,
conjugation identity, two-sided inverse property and holomorphy for the meridional generator
`A_ε^vec` of
`eq:st18-t00115`, the semigroup acting on `ℂ³`-valued fields in Cartesian components. -/
theorem B0223_vec_statement (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) :
    (∀ t : ℝ, 0 ≤ t → ‖(outerS (E := SpaceC) (P := P) hν ε).T t‖ ≤ Real.exp (-t / 4)) ∧
    (∀ μ : ℂ, 0 < μ.re + 1 / 4 → ‖RepsVec hν hε hc hP μ‖ ≤ (μ.re + 1 / 4)⁻¹) ∧
    (∀ μ : ℂ, 0 < μ.re + 1 / 4 → ∀ b : HSpace c MeridC,
      RepsVec hν hε hc hP μ b = ∫ t in Ioi (0 : ℝ), Complex.exp (-(μ * t)) •
        ContinuousLinearMap.adjoint (liftVec hε hc hP).toContinuousLinearMap
          ((outerS hν ε).T t (liftVec hε hc hP b))) ∧
    (∀ μ : ℂ, 0 < μ.re + 1 / 4 → ∀ b : HSpace c MeridC,
      liftVec hε hc hP (RepsVec hν hε hc hP μ b) = physRes hν ε μ (liftVec hε hc hP b)) ∧
    (∀ μ : ℂ, 0 < μ.re + 1 / 4 → ∀ b Ab : HSpace c MeridC,
      IsGenPair (outerS hν ε) (liftVec hε hc hP b) (liftVec hε hc hP Ab) →
        RepsVec hν hε hc hP μ (μ • b - Ab) = b) ∧
    (∀ μ : ℂ, 0 < μ.re + 1 / 4 → ∀ z : HSpace c MeridC,
      IsGenPair (outerS hν ε) (liftVec hε hc hP (RepsVec hν hε hc hP μ z))
        (liftVec hε hc hP (μ • RepsVec hν hε hc hP μ z - z))) ∧
    DifferentiableOn ℂ (RepsVec hν hε hc hP) {μ : ℂ | 0 < μ.re + 1 / 4} :=
  ⟨fun t _ => norm_S_le hν ε t, fun _ hγ => norm_RepsVec_le hν hε hc hP hγ,
    fun _ hγ b => RepsVec_apply hν hε hc hP hγ b, fun _ hγ b => J_RepsVec hν hε hc hP hγ b,
    fun _ hγ _ _ h => RepsVec_left hν hε hc hP hγ h,
    fun _ hγ z => RepsVec_right hν hε hc hP hγ z, differentiableOn_RepsVec hν hε hc hP⟩

end UnforcedLeray.B0223
