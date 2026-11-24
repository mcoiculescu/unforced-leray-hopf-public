import UnforcedLeray.Blueprint.Package
import UnforcedLeray.Blueprint.Construction.Planar
import UnforcedLeray.MatrixCrossing

/-!
# The cylinder problem of the construction: inlet column, observation, reduced matrix

`paper/main.tex`:
* the ring chart and the natural lift `𝒩_v b = √s(b_re_r + b_ze_z)` (`eq:m3-ring-lift`,
  lines 2069–2080; `eq:st18-t00770`, lines 13693–13701);
* the prepared vorticity `φ_{ν,c} = P_cq_{1/ν}` (`eq:m2-prepared-actual`, line 6039) with
  `q_R = e^{λR}R^κV_can(R)` (`eq:st18-t00014`), its real inlet basis `(2Reφ, -2Imφ)` expressed
  through stream functions (lines 9145–9148), the modulated inlet `a` (`eq:stress-setup:3.22`)
  and the free inlet column `J^phys_μ = e^{νΔ}a` (`eq:m4-affine-residual`,
  `eq:stress-setup:3.18`, lines 9139–9232);
* the zero-entrance and inlet solutions of the full cylinder problem, i.e. the pencil
  `A_μ` of `eq:m2-augmented-coordinates` written through its reconstruction
  `b = J_μα - 𝒮_μM`, `M = 𝓜_Ub` (`eq:st18-t00631`–`t00632`, lines 10872–10900), in physical
  variables (`𝒮_μ = 𝒩_v⁻¹𝓡^phys_μ div 𝒩_T`, line 8858);
* the averaged terminal observation `C_Hb = ∫χ_w(s)Λ_Hb(s)ds` with compact static tests
  (`prepared:p4.2`–`p4.3`, `eq:st18-t00551`, `eq:st18-t00749`);
* the full reduced matrix `B_full`, the lower-right block of `A_μ⁻¹`
  (`eq:m4-inverse-blocks`, line 9747; Section `sec:st18-15415`).

Blueprint units: B1004 (exact correspondence), B1005, B0773 (weak-to-body), B1006, with
B0992–B1000 for the reduced matrix.

Everything here is a definition or a characterizing predicate; nothing is asserted. The
encoding works in physical similarity variables: the unknown is a meridional cylinder field
`b(s,ξ,η)`, and every equation is imposed on its lift `w = 𝒩_v b`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Matrix Complex
open scoped ContDiff Topology

namespace UnforcedLeray.Blueprint

open MatrixCrossing Planar

/-! ## The ring chart and the natural lift (`eq:m3-ring-lift`, `eq:st18-t00770`) -/

/-- A meridional cylinder field `(s, ξ, η) ↦ (b_r, b_z)` (`eq:m3-ring-lift`). -/
abbrev CylinderField := ℝ × ℝ × ℝ → ℝ × ℝ

/-- The unit radial vector `e_r` at `y` off the axis. -/
def radialUnit (y : Space) : Space :=
  (Real.sqrt (y 0 ^ 2 + y 1 ^ 2))⁻¹ • WithLp.toLp 2 ![y 0, y 1, 0]

/-- The similarity chart `s = R²/ϱ²`, `ξ = Rτ/2 - (R/2)log s`, `η = √s y₃`
(`eq:m3-ring-lift`, `eq:st18-t00770`). On the axis `ϱ = 0`, a null set, it takes Lean's
values. -/
def ringChart (R τ : ℝ) (y : Space) : ℝ × ℝ × ℝ :=
  (R ^ 2 / (y 0 ^ 2 + y 1 ^ 2),
    R * τ / 2 - (R / 2) * Real.log (R ^ 2 / (y 0 ^ 2 + y 1 ^ 2)),
    Real.sqrt (R ^ 2 / (y 0 ^ 2 + y 1 ^ 2)) * y 2)

/-- The natural physical lift `𝒩_v b = √s(b_re_r + b_ze_z)` in the chart `ringChart`
(`eq:st18-t00770`, lines 13693–13701). -/
def cylinderLift (R : ℝ) (b : CylinderField) (τ : ℝ) (y : Space) : Space :=
  Real.sqrt (ringChart R τ y).1 •
    ((b (ringChart R τ y)).1 • radialUnit y + (b (ringChart R τ y)).2 • coordinateVector 2)

/-! ## The free inlet column (`eq:m4-affine-residual`, `eq:stress-setup:3.22`) -/

/-- `e^{2iϑ} = (x₁ + ix₂)²/|x|²` on the plane `x = (q, η)`. -/
def angularTwo (x : ℝ × ℝ) : ℂ :=
  ((x.1 : ℂ) + (x.2 : ℂ) * I) ^ 2 / ((x.1 ^ 2 + x.2 ^ 2 : ℝ) : ℂ)

/-- The planar stream `Δ⁻¹(f₂(r)e^{2iϑ}) = (Rf₂)(r)e^{2iϑ}` of an angular-two vorticity
(`eq:st18-t00007`; `u = ∇^⊥ψ`, `curl u = Δψ`, line 637). -/
def planarStream (f : Profile) (x : ℝ × ℝ) : ℂ :=
  greenInverse f (Real.sqrt (x.1 ^ 2 + x.2 ^ 2)) * angularTwo x

/-- The `c`-periodized stream `P_c`, summed over the cells `q + kc` (line 2054). The planar
stream decays like `r⁻²`, so the series converges absolutely. -/
def periodicStream (f : Profile) (c : ℝ) (x : ℝ × ℝ) : ℂ :=
  ∑' k : ℤ, planarStream f (x.1 + k * c, x.2)

/-- `∂_qψ` of a plane stream. -/
def partialXi (ψ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ := fderiv ℝ ψ x (1, 0)

/-- `∂_ηψ` of a plane stream. -/
def partialEta (ψ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ := fderiv ℝ ψ x (0, 1)

/-- The modulated inlet `a` of `eq:stress-setup:3.22` (lines 9215–9222), in the chart
variables (`r = ϱ/R = s^{-1/2}`, `q = ξ`, `η = √s y₃`, `ε = R⁻¹`):
`a = s^{1/2-μ}[(-ψ_η)e_r + (ψ_q + ε((1+2μ)ψ - ηψ_η))e_z]`. It is `𝒩_v` of the uncut
entrance `e_ε` of `eq:stress-setup:3.17`. -/
def inletField (R μ : ℝ) (ψ : ℝ × ℝ → ℝ) (τ : ℝ) (y : Space) : Space :=
  ((ringChart R τ y).1 ^ (1 / 2 - μ) *
      -partialEta ψ ((ringChart R τ y).2.1, (ringChart R τ y).2.2)) • radialUnit y +
    ((ringChart R τ y).1 ^ (1 / 2 - μ) *
      (partialXi ψ ((ringChart R τ y).2.1, (ringChart R τ y).2.2) +
        R⁻¹ * ((1 + 2 * μ) * ψ ((ringChart R τ y).2.1, (ringChart R τ y).2.2) -
          (ringChart R τ y).2.2 *
            partialEta ψ ((ringChart R τ y).2.1, (ringChart R τ y).2.2)))) •
      coordinateVector 2

/-- The free inlet column `J^phys_μα = e^{νΔ}a_α` (`eq:stress-setup:3.18`, line 9182: "the
actual free heat evolution of the modulated inlet"; line 9232: it solves the free equation),
linear in the inlet coordinates `α` with respect to the two streams `ψ₀, ψ₁` of the real
inlet basis. -/
def inletColumn (ν R μ : ℝ) (ψ : Fin 2 → ℝ × ℝ → ℝ) (α : Vector2) : ℝ → SpatialField :=
  fun τ => Heat.average ν
    (fun y => α 0 • inletField R μ (ψ 0) τ y + α 1 • inletField R μ (ψ 1) τ y)

/-- The zero inlet has the zero column. -/
theorem inletColumn_zero (ν R μ : ℝ) (ψ : Fin 2 → ℝ × ℝ → ℝ) :
    inletColumn ν R μ ψ 0 = fun _ _ => 0 := by
  funext τ y
  simp [inletColumn, Heat.average]

/-! ## The full cylinder problem in physical variables -/

/-- The `L²` representative of `𝔓∂_jφ`. -/
def projectedPartial (φ : Space → Space) (j : Fin 3) : SpatialField :=
  ⇑(Leray.projection (toL2 (testPartial φ j)))

/-- `⟨𝕋_{·j}(y), (𝔓∂_jφ)(y)⟩`. -/
def lerayDivIntegrand (col : Fin 3 → SpatialField) (φ : Space → Space) (j : Fin 3)
    (y : Space) : ℝ :=
  inner ℝ (col j y) (projectedPartial φ j y)

/-- `⟨𝔓 div 𝕋, φ⟩ = -∑_j ∫⟨𝕋_{·j}, 𝔓∂_jφ⟩` as Lebesgue integrals against the `L²`
representative of `𝔓∂_jφ`. On `L²` columns it is the package's literal pairing
`lerayDivPairing` (`lerayDivIntegral_eq_lerayDivPairing`), and each integrand is integrable
by Cauchy–Schwarz (`lerayDivIntegrand_integrable`). The coupling stresses of the cylinder
problem, the inlet part `𝓜_UJ_μα` included, have `L²` columns at almost every phase: they
lie in the stress space `Z = Z₁ ⊕ ρ_b^{-1/2}H_T` of `eq:stress-setup:3.2` (line 8738), and
`Z₁ = L²(s^{-1/2}W²dς) ⊂ H_T = L²(s^{-1/2}dς)` since `W ≥ 1` (lines 7279, 8736; also
`eq:st18-t00576`), while `‖𝒩_TT‖_{Y₂} = √πR‖T‖_{H_T}` (`eq:stress-setup:3.1`). The integral
form is a choice of encoding; it is not needed for non-`L²` stresses. Consumers require each
integral to converge. -/
def lerayDivIntegral (col : Fin 3 → SpatialField) (φ : Space → Space) : ℝ :=
  -∑ j : Fin 3, ∫ y, lerayDivIntegrand col φ j y

/-- On `L²` columns each integrand of `lerayDivIntegral` is integrable (Cauchy–Schwarz). -/
theorem lerayDivIntegrand_integrable {col : Fin 3 → SpatialField} (hcol : ColumnsL2 col)
    (φ : Space → Space) (j : Fin 3) : Integrable (lerayDivIntegrand col φ j) := by
  refine (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) ((hcol j).toLp (col j))
    (Leray.projection (toL2 (testPartial φ j)))).congr ?_
  filter_upwards [(hcol j).coeFn_toLp] with y hy
  simp only [lerayDivIntegrand, projectedPartial, hy]

/-- On `L²` columns the Lebesgue form is the package's literal pairing. -/
theorem lerayDivIntegral_eq_lerayDivPairing {col : Fin 3 → SpatialField} (hcol : ColumnsL2 col)
    (φ : Space → Space) : lerayDivIntegral col φ = lerayDivPairing col φ := by
  unfold lerayDivIntegral lerayDivPairing
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [toL2_of_memLp (hcol j), MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(hcol j).coeFn_toLp] with y hy
  simp only [lerayDivIntegrand, projectedPartial, hy]

/-- `⟨𝔓 div(U⊗w + w⊗U)(τ), ψ(τ)⟩`. -/
def weakCoupling (U w : ℝ → SpatialField) (ψ : SpaceTime → Space) (τ : ℝ) : ℝ :=
  lerayDivIntegral (symTensorColumns (U τ) (w τ)) (slice ψ τ)

/-- The linear part of `σw + 𝒯₀w - hΔw - ½w` tested against `ψ`, with every derivative on
the test (`⟨𝒯₀w,ψ⟩ = driftAdjointTerm`, `⟨Δw,ψ⟩ = ⟨w,Δψ⟩`). -/
def weakModeIntegrand (h σ : ℝ) (w : ℝ → SpatialField) (ψ : SpaceTime → Space)
    (z : SpaceTime) : ℝ :=
  (σ - 1 / 2) * pairTerm w ψ z + driftAdjointTerm w ψ z - h * diffusionTerm w ψ z

/-- The mode equation `σw + 𝒯₀w - hΔw - ½w + 𝔓div(U⊗w + w⊗U) = 0` (`eq:st18-t00633` with
`B = 𝒯₀`; `loc:eq:mode`) in distributions on `ℝ × ℝ³`, with no regularity of `Δw` or
`𝒯₀w`: the stress form solved by every reconstruction `w = 𝒩_v(J_μα - 𝒮_μ𝓜_Ub)`. Every
pairing converges. -/
structure IsWeakModeSolution (h σ : ℝ) (U w : ℝ → SpatialField) : Prop where
  value_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (pairTerm w ψ)
  temporal_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (temporalTerm w ψ)
  dilation_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (dilationTerm w ψ)
  diffusion_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (diffusionTerm w ψ)
  coupling_integrable : ∀ ψ, IsSimilarityTest ψ → ∀ᵐ τ, ∀ j : Fin 3,
    Integrable (lerayDivIntegrand (symTensorColumns (U τ) (w τ)) (slice ψ τ) j)
  coupling_time_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (weakCoupling U w ψ)
  identity : ∀ ψ, IsSimilarityTest ψ →
    (∫ z, weakModeIntegrand h σ w ψ z) + (∫ τ, weakCoupling U w ψ τ) = 0

/-- The periodic `H¹` class `w, ∇w ∈ 𝒴₂` (the range of `𝒩_v𝒮_μ`, `eq:stress-setup:3.5`):
`w ∈ 𝒴_{2,div}`, with three weak first derivatives square integrable on one period. -/
structure IsH1Periodic (period : ℝ) (f : ℝ → SpatialField) : Prop where
  value : IsY2Div period f
  gradient : ∃ G : Fin 3 → ℝ → SpatialField, ∀ i : Fin 3,
    AEStronglyMeasurable (fun z : SpaceTime => G i z.1 z.2) volume ∧
    MemLp (fun z : SpaceTime => G i z.1 z.2) 2 (volume.restrict (periodSlab period)) ∧
    ∀ᵐ τ, HasWeakSpatialDerivative i (f τ) (G i τ)

/-- A solution of the full cylinder problem with inlet column `J` (the reconstruction
`b = J_μα - 𝒮_μM`, `M = 𝓜_Ub` of `eq:st18-t00631`, line 10875): the lift solves the weak mode
equation, and its difference from the inlet column is in the periodic `H¹` class. With
`J = 0` this is a zero-entrance mode. -/
structure IsInletSolution (h period σ : ℝ) (U J w : ℝ → SpatialField) : Prop where
  equation : IsWeakModeSolution h σ U w
  remainder : IsH1Periodic period (fun τ y => w τ y - J τ y)

/-! ## The averaged terminal observation (`prepared:p4.2`–`p4.3`) -/

/-- The fixed observation: the terminal age `H = Σ/ν`, the width `w`, the age cutoff `χ_w`
and the two compact static velocity tests `φ_i` on the `(q, η)` plane. -/
structure ObservationData where
  /-- `H = Σ/ν`. -/
  age : ℝ
  /-- The width `w` (line 9555). -/
  width : ℝ
  /-- `χ_w ∈ C_c^∞((H-w,H))`, nonnegative, `∫χ_w = 1`. -/
  cutoff : ℝ → ℝ
  /-- The tests `φ_i`, valued in the meridional components `(q, η) ↔ (r, z)`. -/
  tests : Fin 2 → ℝ × ℝ → ℝ × ℝ

/-- The structural clauses of `prepared:p4.2`–`p4.3` (lines 9542–9562) for cell length `c`:
`0 < w < H`, `χ_w ∈ C_c^∞((H-w,H))` nonnegative of mass one, and smooth compactly supported
tests inside one centered cell. The specific frozen tests (biorthogonal to the frozen pair)
are not pinned; see the module docstring of `Construction/Steps.lean`. -/
structure IsAdmissibleObservation (c : ℝ) (O : ObservationData) : Prop where
  width_pos : 0 < O.width
  width_lt : O.width < O.age
  cutoff_smooth : ContDiff ℝ ∞ O.cutoff
  cutoff_compact : HasCompactSupport O.cutoff
  cutoff_support : tsupport O.cutoff ⊆ Ioo (O.age - O.width) O.age
  cutoff_nonneg : ∀ s, 0 ≤ O.cutoff s
  cutoff_mass : ∫ s, O.cutoff s = 1
  tests_smooth : ∀ i, ContDiff ℝ ∞ (O.tests i)
  tests_compact : ∀ i, HasCompactSupport (O.tests i)
  tests_support : ∀ i, tsupport (O.tests i) ⊆ Ioo (-(c / 2)) (c / 2) ×ˢ univ

/-- `C_Hb = ∫χ_w(s)(∫φ_i·b(s,·))ds` (`prepared:p4.3`): the unnormalized one-cell spatial
integral, written over the whole plane since the tests live in one cell. -/
def ObservationData.observe (O : ObservationData) (b : CylinderField) : Vector2 :=
  fun i => ∫ x : ℝ × ℝ × ℝ, O.cutoff x.1 *
    ((O.tests i (x.2.1, x.2.2)).1 * (b x).1 + (O.tests i (x.2.1, x.2.2)).2 * (b x).2)

/-! ## The full reduced matrix (`eq:m4-inverse-blocks`, `eq:st18-t00632`) -/

/-- `B` is the full reduced matrix `B_full(σ)` of the pencil
`A_σ(M,α) = (M - 𝓜_Ub, C_Hb)`, `b = J_σα - 𝒮_σM` (`eq:m2-augmented-coordinates`), at
viscosity `h`, ring radius `R`, period `P`, background `U`, inlet streams `ψ` and
observation `O`:
* `solution`: for every observation `β` there is a solution of the full problem with inlet
  `Bβ` and observation `β` (the second column of `A_σ⁻¹`: `A_σ(E₊β, Bβ) = (0, β)`), nonzero
  when `β ≠ 0` (t00632: "if `b = 0` ... `β = 0`; therefore `b ≠ 0`");
* `injective`: `A_σ` is injective (the manuscript's invertibility of `A_σ` on the window).
Together they determine `B` uniquely: two such matrices differ by the inlet of a solution
with zero observation (by linearity of the problem in `(b, α)`, granted the convergence of
the heat and observation integrals, which holds for the manuscript's inlet column). This
uniqueness is a mathematical remark; it is not proved in Lean and no composition uses it. -/
structure IsReducedMatrix (h R period σ : ℝ) (U : ℝ → SpatialField)
    (ψ : Fin 2 → ℝ × ℝ → ℝ) (O : ObservationData) (B : Matrix2) : Prop where
  solution : ∀ β : Vector2, ∃ b : CylinderField,
    IsInletSolution h period σ U (inletColumn h R σ ψ (B *ᵥ β)) (cylinderLift R b) ∧
      O.observe b = β ∧
      (β ≠ 0 → ¬ ((fun z : SpaceTime => cylinderLift R b z.1 z.2) =ᵐ[volume.restrict
        (periodSlab period)] 0))
  injective : ∀ (α : Vector2) (b : CylinderField),
    IsInletSolution h period σ U (inletColumn h R σ ψ α) (cylinderLift R b) →
      O.observe b = 0 →
        α = 0 ∧ (fun z : SpaceTime => cylinderLift R b z.1 z.2) =ᵐ[volume.restrict
          (periodSlab period)] 0

/-- The exact correspondence `eq:st18-t00632` in the direction used at line 13681: a nonzero
kernel vector of the reduced matrix gives a nonzero zero-entrance mode with observation
`β`. -/
theorem IsReducedMatrix.zeroEntrance {h R period σ : ℝ} {U : ℝ → SpatialField}
    {ψ : Fin 2 → ℝ × ℝ → ℝ} {O : ObservationData} {B : Matrix2}
    (hB : IsReducedMatrix h R period σ U ψ O B) {β : Vector2} (hβ : β ≠ 0) (hBβ : B *ᵥ β = 0) :
    ∃ b : CylinderField,
      IsInletSolution h period σ U (fun _ _ => 0) (cylinderLift R b) ∧ O.observe b = β ∧
        ¬ ((fun z : SpaceTime => cylinderLift R b z.1 z.2) =ᵐ[volume.restrict
          (periodSlab period)] 0) := by
  obtain ⟨b, hsol, hobs, hnz⟩ := hB.solution β
  rw [hBβ, inletColumn_zero] at hsol
  exact ⟨b, hsol, hobs, hnz hβ⟩

end UnforcedLeray.Blueprint
