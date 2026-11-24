import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps.ChiOStrApply
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1

/-!
# The Ward fields as bounded linear maps: definitions, leaves, representative lemmas
(source 4161-4303)

Source of record: `the November 2 reference manuscript` (73 pages).

Task `ORG:return-concrete/instance-3/ward`.  `Concrete/ReturnInst.lean` defines
`wardOps = Classical.epsilon (IsWardTriple …)`, and the Ward pin of the concrete base holds as
soon as a triple with `IsWardTriple` exists (`concreteBase_isWardPinned`).  This file and
`Ward/Assembly.lean` reduce that existence to the leaves below.

## The construction

For a stress `T` the canonical old source is `G_T = strSum (χ_oT)`, the sum of the canonical `Lp`
representatives of the two components of `χ_oT` (source 4171-4179: the tensor
`χ_oT = χ_oM_Vw + χ_oM_{r_b}w` is identical in both resolvents, the full repair stress enters
before inversion).  `wardYCoef`, `wardHCoef`, `wardECoef` are the right sides of the three clauses
of `IsWardTriple` at `g₁ + g₂ = G_T`: the coefficients of `Y = D_{μ+1}X`, `h = [U, X]`
(4171-4174, `X = 𝒞_y(W_μ - W_{μ+1})`, `W_μ = -S_μ(χ_oT)` in its separated-kernel realization
`IIIa.sepW`, 3611-3626) and the full unprojected residual `Ẽ_μ` (4271-4280).  They are
`IsL2Family`s (`ReturnInst/AffineFields.lean`) for the gained body measure (`Y, h`) and the
ungained one (`Ẽ_μ`), so `IsL2Family.toCLM` gives the three operators (`Ward/Assembly.lean`).

## Old `L²` data

`IsOldL2 c ν g`: `g` is measurable, in `L²(s^{-1/2}dς)` (the class `H_T`, whose lift is the
`Y₂ = L²_τL²` class of the old source, 2684-2687, 4155-4156; for every `T ∈ Z` only this moment is
available, see `Sub/IIIb-D2_3_1_1.lean`) and vanishes a.e. where `νs ≤ 6/5` (`χ_o = 0`,
4163-4166).  Canonical old sources are old `L²` data (`wo_isOldL2_rep`); the class is closed under
sums and real multiples.

## Proved here

* `wo_wardX0_congr`, `wo_wardX_congr`, `wo_wardY_congr`, `wo_wardH_congr`, `wo_wardE_congr`:
  the Ward fields depend only on the `ageμ c (-1/2)`-class of the old data (from the queued leaves
  `ChartOfNullPullback`, `SepWCongrAE` of `Sub/IIIb-D2_3_1_1_1.lean`); with `wo_rep_ae` this is the
  independence of the representatives `g₁, g₂` over which the pin quantifies;
* `wo_rep_ae`, `wo_rep_add`, `wo_rep_smul`: representatives, sums and multiples of stresses, a.e.
  for `ageμ c (-1/2)` (`ρ_b > 0`: otherwise the `H_T` measure vanishes and `g₂` is arbitrary);
* `wo_isOldL2_rep`: the canonical old sources are old `L²` data (from `WardOldNormLe`);
* `wo_coefOf_add`, `wo_coefOf_smul`, `wo_coefOf_congr_offAxis`: the chart coefficient is linear
  and reads its field only off the axis.

## Leaves (tasks)

* `WardXAdd`, `WardXDiff`: additivity and off-axis regularity of `X = 𝒞_y(W_μ - W_{μ+1})` on old
  `L²` data (separated kernels 3603-3713, outward primitive 4181-4196, shifted resolvent
  4198-4201); `WardYHAdd`, `WardEAdd`: additivity of `Y, h` and of `Ẽ_μ` (pointwise calculus from
  the two);
* `WardSmul`: homogeneity of the three fields (unconditional);
* `WardOldNormLe`: the gain norm controls the old source (2694-2700, from `GainMeasureLower`);
* `WardYMeas`, `WardHMeas`, `WardEMeas`: measurability of the three coefficients;
* `WardYBound`, `WardHBound`, `WardEBound`: the `L²` bounds (4187-4196, 4291-4294, 3631-3713,
  5198-5260; young support 4306-4311), with `WardBgBound` for the background (4155, 4194-4195).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ## 1. Old `L²` data -/

/-- **Old `L²` data** (source 4155-4166, 4171, 2684-2687): a measurable chart tensor field, square
integrable for `s^{-1/2}dς` (the class `H_T`; its lift has finite `Y₂ = L²_τL²` moment, 4155-4156),
vanishing a.e. where `νs ≤ 6/5` (`χ_o = 0` for `s ≤ 1.2/ν`, 4163-4166), so that its physical
source `oldPhys R c g` lives in the old disk `ϱ ≤ R√(5ν/6)`. -/
structure IsOldL2 (c ν : ℝ) (g : Chart → Ten3) : Prop where
  measurable : Measurable g
  memLp : MemLp g 2 (ageμ c (-1 / 2))
  old : ∀ᵐ p ∂(ageμ c (-1 / 2)), ν * p.1 ≤ 6 / 5 → g p = 0

theorem IsOldL2.add {c ν : ℝ} {g g' : Chart → Ten3} (h : IsOldL2 c ν g)
    (h' : IsOldL2 c ν g') : IsOldL2 c ν (g + g') where
  measurable := h.measurable.add h'.measurable
  memLp := h.memLp.add h'.memLp
  old := by
    filter_upwards [h.old, h'.old] with p hp hp' hs
    rw [Pi.add_apply, hp hs, hp' hs, add_zero]

theorem IsOldL2.smul {c ν : ℝ} {g : Chart → Ten3} (h : IsOldL2 c ν g) (r : ℝ) :
    IsOldL2 c ν (r • g) where
  measurable := h.measurable.const_smul r
  memLp := h.memLp.const_smul r
  old := by
    filter_upwards [h.old] with p hp hs
    rw [Pi.smul_apply, hp hs, smul_zero]

/-! ## 2. The coefficient families -/

section Coef

variable (c mZ ρb γ ν ε μ : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (χy : ℝ → ℝ)

/-- The coefficient of `Y[T] = D_{μ+1}𝒞_y(W_μ - W_{μ+1})` (source 4171-4174) for the canonical
old source `G_T = strSum (χ_oT)`, radius `R = ε⁻¹`: the right side of the `Y`-clause of
`IsWardTriple` at `g₁ + g₂ = G_T`. -/
def wardYCoef (T : StrG c mZ ρb γ ν) : Chart → Merid :=
  coefOf ε⁻¹ (wardY ν μ ε⁻¹ c χy (strSum (chiOStr c mZ ρb γ ν hχo T)))

/-- The coefficient of `h[T] = [U, X]` (source 4171-4174) for the canonical old source. -/
def wardHCoef (U : ℝ → SpatialField) (T : StrG c mZ ρb γ ν) : Chart → Merid :=
  coefOf ε⁻¹ (wardH ν μ ε⁻¹ c χy U (strSum (chiOStr c mZ ρb γ ν hχo T)))

/-- The coefficient of the full unprojected residual `Ẽ_μ[T]` (source 4271-4280) for the
canonical old source. -/
def wardECoef (U : ℝ → SpatialField) (p : ℝ → Space → ℝ) (T : StrG c mZ ρb γ ν) :
    Chart → Merid :=
  coefOf ε⁻¹ (wardE ν μ ε⁻¹ c χy U p (strSum (chiOStr c mZ ρb γ ν hχo T)))

end Coef

/-! ## 3. The background on the young support -/

/-- **Bounds of the exact background on the young support of the Ward fields** (source 4155
"Since `U` is bounded", 4194-4195 "since `U, DU` are bounded, `h ∈ Y₂`", 4291-4294 and 5225-5260
for the residual): on `ϱ ≥ R√ν` (`χ_y(νR²/ϱ²)` vanishes for `ϱ ≤ R√ν`, 4167, so the fields vanish
off this set away from the axis, 4306-4311) the background `U`, its first and second partials and
the pressure gradient are bounded by `M`. -/
def WardBgBound (R ν : ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ) (M : ℝ) : Prop :=
  ∀ (τ : ℝ) (y : Space), R * Real.sqrt ν ≤ ϱ y →
    ‖U τ y‖ ≤ M ∧ (∀ j : Fin 3, ‖physPd (U τ) j y‖ ≤ M) ∧
      (∀ j l : Fin 3, ‖physPd2 (U τ) j l y‖ ≤ M) ∧ ‖physGrad (p τ) y‖ ≤ M

/-! ## 4. Leaves -/

/-- **Additivity of the Ward displacement on old `L²` data** (source 4171-4186; `sep:resolvent`
3621-3629; outward primitive 4181-4191): for old `L²` data `g, g'`, at every point off the axis,
`X = 𝒞_y(W_μ - W_{μ+1})` of `g + g'` is the sum of the two displacements.  Where `ϱ ≤ R√ν` all
three vanish (`χ_y = χ_y' = 0` on `[1, ∞)`, `IsYoungCutoff`); where `ϱ > R√ν` the
separated-kernel integrals `IIIa.sepW` and the primitive `outPrim` converge absolutely (kernel
bound `sep:kernel` 3603-3611 across the radial gap `ϱ - R√(5ν/6)`, Cauchy-Schwarz against the
finite `L²_τL²` moment of the lift, `Re μ > -1/4`), so `integral_add` applies. -/
def WardXAdd : Prop :=
  ∀ (ν μ R c : ℝ) (χy : ℝ → ℝ), IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
    ∀ g g' : Chart → Ten3, IsOldL2 c ν g → IsOldL2 c ν g' →
      ∀ (τ : ℝ) (y : Space), y ∉ axis →
        wardX ν μ R c χy (g + g') τ y = wardX ν μ R c χy g τ y + wardX ν μ R c χy g' τ y

/-- **Regularity of the Ward displacement off the axis** (source 4187-4201, 3631-3713): for old
`L²` data, `X(τ, ·)` is `C³` on the complement of the axis, `X(·, y)` is differentiable in the
phase at every off-axis `y`, and the phase derivative is differentiable in `y` off the axis.
Near points with `ϱ < R√ν` the field vanishes; on `ϱ > R√(5ν/6)` the spatial derivatives come from
differentiating `sep:resolvent` under the integral (`sep:kernel`), and the phase derivative exists
because `X₀ = W_μ - W_{μ+1}` inserts the factor `1 - λ²` in `sep:resolvent` (3708-3709, "It costs
no inverse"), which removes the boundary term at `λ = 1` (`X₀ = R_{μ+1}W_μ`, `D_{μ+1}X₀ = W_μ`,
`ward:shifted-resolvent` 4198-4201); `Re μ > -1/4` bounds the dilated source term. -/
def WardXDiff : Prop :=
  ∀ (ν μ R c : ℝ) (χy : ℝ → ℝ), IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
    ∀ g : Chart → Ten3, IsOldL2 c ν g → ∀ τ : ℝ,
      ContDiffOn ℝ 3 (wardX ν μ R c χy g τ) axisᶜ ∧
        (∀ y : Space, y ∉ axis → DifferentiableAt ℝ (fun t => wardX ν μ R c χy g t y) τ) ∧
        DifferentiableOn ℝ (fun y => deriv (fun t => wardX ν μ R c χy g t y) τ) axisᶜ

/-- **Additivity of `Y` and `h`** (source 4171-4174): for old `L²` data, off the axis,
`Y = D_{μ+1}X` and `h = [U, X]` of `g + g'` are the sums (pointwise calculus from `WardXAdd` and
`WardXDiff`: on the open set `axisᶜ` the displacements add, and `fderiv`, `deriv` and the second
partials of differentiable summands add). -/
def WardYHAdd : Prop :=
  ∀ (ν μ R c : ℝ) (χy : ℝ → ℝ) (U : ℝ → SpatialField), IsYoungCutoff χy → 0 < ν → 0 < R →
    0 < c → -(1 / 4) < μ →
    ∀ g g' : Chart → Ten3, IsOldL2 c ν g → IsOldL2 c ν g' →
      ∀ (τ : ℝ) (y : Space), y ∉ axis →
        wardY ν μ R c χy (g + g') τ y = wardY ν μ R c χy g τ y + wardY ν μ R c χy g' τ y ∧
          wardH ν μ R c χy U (g + g') τ y =
            wardH ν μ R c χy U g τ y + wardH ν μ R c χy U g' τ y

/-- **Additivity of the residual `Ẽ_μ`** (source 4271-4280): for old `L²` data, off the axis, the
four-term residual of `g + g'` is the sum (pointwise calculus from `WardXAdd`, `WardXDiff` and
`WardYHAdd`). -/
def WardEAdd : Prop :=
  ∀ (ν μ R c : ℝ) (χy : ℝ → ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ),
    IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
    ∀ g g' : Chart → Ten3, IsOldL2 c ν g → IsOldL2 c ν g' →
      ∀ (τ : ℝ) (y : Space), y ∉ axis →
        wardE ν μ R c χy U p (g + g') τ y =
          wardE ν μ R c χy U p g τ y + wardE ν μ R c χy U p g' τ y

/-- **Homogeneity of the Ward fields** (source 4171: the fields are linear in `χ_oT`): for every
chart tensor field `g` and real `r`, `Y`, `h` and `Ẽ_μ` of `r • g` are `r` times those of `g`.
No integrability is needed: `∫ r • f = r • ∫ f`, `fderiv (r • f) = r • fderiv f` and
`deriv (r • f) = r • deriv f` hold unconditionally over `ℝ`. -/
def WardSmul : Prop :=
  ∀ (ν μ R c : ℝ) (χy : ℝ → ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ) (r : ℝ)
    (g : Chart → Ten3),
    wardY ν μ R c χy (r • g) = r • wardY ν μ R c χy g ∧
      wardH ν μ R c χy U (r • g) = r • wardH ν μ R c χy U g ∧
      wardE ν μ R c χy U p (r • g) = r • wardE ν μ R c χy U p g

/-- **The gain norm controls the old source** (source 2694-2700, 4155-4156, 5609): for `ρ_b > 0`,
`m_Z ≥ 0`, `ν > 0` the canonical old source satisfies `‖G_T‖_{L²(s^{-1/2}dς)} ≤ C‖T‖`
(`|χ̂_o| ≤ 1` and the gain measures dominate `κ s^{-1/2}dς`, `GainMeasureLower`). -/
def WardOldNormLe : Prop :=
  ∀ (c mZ ρb γ ν : ℝ), 0 < ρb → 0 ≤ mZ → 0 < ν →
    ∀ (χo : ℝ → ℝ) (hχo : IsOutwardCutoff χo), ∃ C : ℝ, ∀ T : StrG c mZ ρb γ ν,
      eLpNorm (strSum (chiOStr c mZ ρb γ ν hχo T)) 2 (ageμ c (-1 / 2)) ≤
        ENNReal.ofReal (C * ‖T‖)

/-- **Measurability of the coefficient of `Y`** (source 4171-4174, 3611-3626: `W_μ` is a
measurable parametric integral of a measurable source; `X`, `∂_τX` and their spatial derivatives
are jointly continuous off the axis, where `coefOf` reads them). -/
def WardYMeas : Prop :=
  ∀ (ν μ R c γ : ℝ) (χy : ℝ → ℝ), IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
    ∀ g : Chart → Ten3, IsOldL2 c ν g →
      AEStronglyMeasurable (coefOf R (wardY ν μ R c χy g)) (bodyMeasure c γ ν)

/-- **Measurability of the coefficient of `h`** (source 4171-4174; the background is smooth,
`IsExactProfile`, 4139-4141). -/
def WardHMeas : Prop :=
  ∀ (ν μ R c γ P : ℝ) (χy : ℝ → ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ),
    IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ → IsExactProfile ν P U p →
    ∀ g : Chart → Ten3, IsOldL2 c ν g →
      AEStronglyMeasurable (coefOf R (wardH ν μ R c χy U g)) (bodyMeasure c γ ν)

/-- **Measurability of the coefficient of `Ẽ_μ`** (source 4271-4280; ungained measure). -/
def WardEMeas : Prop :=
  ∀ (ν μ R c P : ℝ) (χy : ℝ → ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ),
    IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ → IsExactProfile ν P U p →
    ∀ g : Chart → Ten3, IsOldL2 c ν g →
      AEStronglyMeasurable (coefOf R (wardE ν μ R c χy U p g)) (srcMeasure c)

/-- **`L²` bound of `Y`** in the gained body norm (source 4194-4196 "`X, DX, Y ∈ Y₂` … fixed-parameter
bounds"; `ward:cutoff-source` 4202-4216: `Y = 𝒞_yW_μ + [D_{μ+1}, 𝒞_y]X₀`; `sep:young` 3633-3648
with `p = q = 2`; the cutoff majorant 3679-3700; young support 4306-4311): the coefficient of `Y`
is bounded in `L²(bodyMeasure)` by `C‖g‖_{L²(s^{-1/2}dς)}`. -/
def WardYBound : Prop :=
  ∀ (ν μ R c γ : ℝ) (χy : ℝ → ℝ), IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
    ∃ C : ℝ, ∀ g : Chart → Ten3, IsOldL2 c ν g →
      eLpNorm (coefOf R (wardY ν μ R c χy g)) 2 (bodyMeasure c γ ν) ≤
        ENNReal.ofReal C * eLpNorm g 2 (ageμ c (-1 / 2))

/-- **`L²` bound of `h = [U, X]`** in the gained body norm (source 4194-4195: "since `U, DU` are
bounded, `h ∈ Y₂`"; young support 4306-4311), for a background bounded on the young support. -/
def WardHBound : Prop :=
  ∀ (ν μ R c γ M : ℝ) (χy : ℝ → ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ),
    IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ → WardBgBound R ν U p M →
    ∃ C : ℝ, ∀ g : Chart → Ten3, IsOldL2 c ν g →
      eLpNorm (coefOf R (wardH ν μ R c χy U g)) 2 (bodyMeasure c γ ν) ≤
        ENNReal.ofReal C * eLpNorm g 2 (ageμ c (-1 / 2))

/-- **`L²` bound of the residual `Ẽ_μ`** in the ungained body norm (source 4291-4294 "the
actual-range body estimates below show `Ẽ_μ ∈ Y₂`", 5198-5260; every term contains a derivative of
`X` or `Y`, 5296-5297, so `Ẽ_μ` has young support), for a background bounded on the young
support. -/
def WardEBound : Prop :=
  ∀ (ν μ R c M : ℝ) (χy : ℝ → ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ),
    IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ → WardBgBound R ν U p M →
    ∃ C : ℝ, ∀ g : Chart → Ten3, IsOldL2 c ν g →
      eLpNorm (coefOf R (wardE ν μ R c χy U p g)) 2 (srcMeasure c) ≤
        ENNReal.ofReal C * eLpNorm g 2 (ageμ c (-1 / 2))

/-! ## 5. The chart coefficient -/

theorem wo_coefOf_add (R : ℝ) (F G : ℝ → Space → Space) :
    coefOf R (fun τ y => F τ y + G τ y) = coefOf R F + coefOf R G := by
  funext p
  ext i
  fin_cases i <;> simp [coefOf] <;> ring

theorem wo_coefOf_smul (R r : ℝ) (F : ℝ → Space → Space) :
    coefOf R (r • F) = r • coefOf R F := by
  funext p
  ext i
  fin_cases i <;> simp [coefOf] <;> ring

theorem wo_chartY_not_mem_axis {R : ℝ} (hR : R ≠ 0) {p : Chart} (hp : 0 < p.1) :
    NearInst.chartY R p ∉ axis := by
  intro h
  have h0 : NearInst.chartY R p 0 = 0 := h.1
  have hs : Real.sqrt p.1 ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  have h1 : NearInst.chartY R p 0 = R / Real.sqrt p.1 := by
    simp [NearInst.chartY]
  rw [h1, div_eq_zero_iff] at h0
  rcases h0 with h0 | h0
  · exact hR h0
  · exact hs h0

/-- `coefOf R F` reads `F` only off the axis (`R ≠ 0`). -/
theorem wo_coefOf_congr_offAxis {R : ℝ} (hR : R ≠ 0) {F G : ℝ → Space → Space}
    (h : ∀ τ y, y ∉ axis → F τ y = G τ y) : coefOf R F = coefOf R G := by
  funext p
  unfold coefOf
  by_cases hp : 0 < p.1
  · rw [h _ _ (wo_chartY_not_mem_axis hR hp)]
  · have h0 : Real.sqrt p.1 = 0 := Real.sqrt_eq_zero'.2 (not_lt.1 hp)
    simp [h0]

/-! ## 6. The Ward fields depend only on the a.e. class of the old data -/

section Congr

variable {ν μ R c : ℝ} {g g' : Chart → Ten3}

/-- `X₀ = W_μ - W_{μ+1}` depends only on the `ageμ c (-1/2)`-class of the old data (source
3611-3626): chart-null sets pull back to null sets of `(τ, z)` (`ChartOfNullPullback`), and
`sepW` sees only the a.e. class of its source (`SepWCongrAE`). -/
theorem wo_wardX0_congr (hN : ChartOfNullPullback) (hS : SepWCongrAE) (hR : 0 < R)
    (hc : 0 < c) (h : g =ᵐ[ageμ c (-1 / 2)] g') : wardX0 ν μ R c g = wardX0 ν μ R c g' := by
  have hpull := hN R c hR hc _ (ae_iff.1 h)
  have hagree : ∀ᵐ x : ℝ × Space ∂volume, oldPhys R c g x.1 x.2 = oldPhys R c g' x.1 x.2 := by
    filter_upwards [hpull] with x hx
    simp only [not_not] at hx
    simp only [oldPhys, NearInst.cartLift, hx]
  funext τ y
  unfold wardX0
  rw [hS ν (μ : ℂ) (oldPhys R c g) (oldPhys R c g') hagree y τ,
    hS ν ((μ : ℂ) + 1) (oldPhys R c g) (oldPhys R c g') hagree y τ]

theorem wo_wardX_congr (hN : ChartOfNullPullback) (hS : SepWCongrAE) (hR : 0 < R) (hc : 0 < c)
    (χy : ℝ → ℝ) (h : g =ᵐ[ageμ c (-1 / 2)] g') :
    wardX ν μ R c χy g = wardX ν μ R c χy g' := by
  unfold wardX
  rw [wo_wardX0_congr hN hS hR hc h]

/-- `Y` depends only on the a.e. class of the old data. -/
theorem wo_wardY_congr (hN : ChartOfNullPullback) (hS : SepWCongrAE) (hR : 0 < R) (hc : 0 < c)
    (χy : ℝ → ℝ) (h : g =ᵐ[ageμ c (-1 / 2)] g') :
    wardY ν μ R c χy g = wardY ν μ R c χy g' := by
  unfold wardY
  rw [wo_wardX_congr hN hS hR hc χy h]

/-- `h = [U, X]` depends only on the a.e. class of the old data. -/
theorem wo_wardH_congr (hN : ChartOfNullPullback) (hS : SepWCongrAE) (hR : 0 < R) (hc : 0 < c)
    (χy : ℝ → ℝ) (U : ℝ → SpatialField) (h : g =ᵐ[ageμ c (-1 / 2)] g') :
    wardH ν μ R c χy U g = wardH ν μ R c χy U g' := by
  funext τ y
  unfold wardH
  rw [wo_wardX_congr hN hS hR hc χy h]

/-- `Ẽ_μ` depends only on the a.e. class of the old data. -/
theorem wo_wardE_congr (hN : ChartOfNullPullback) (hS : SepWCongrAE) (hR : 0 < R) (hc : 0 < c)
    (χy : ℝ → ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ) (h : g =ᵐ[ageμ c (-1 / 2)] g') :
    wardE ν μ R c χy U p g = wardE ν μ R c χy U p g' := by
  funext τ y
  unfold wardE
  rw [wo_wardY_congr hN hS hR hc χy h, wo_wardX_congr hN hS hR hc χy h]

end Congr

/-! ## 7. Representatives of the old source -/

section Rep

variable {c mZ ρb γ ν : ℝ} {χo : ℝ → ℝ}

/-- Any representatives `g₁, g₂` of the two components of `χ_oT` (the quantifier of the pin) sum to
the canonical old source a.e. for `ageμ c (-1/2)` (`ρ_b > 0`). -/
theorem wo_rep_ae (hρ : 0 < ρb) (hχo : IsOutwardCutoff χo) (T : StrG c mZ ρb γ ν)
    {g₁ g₂ : Chart → Ten3}
    (h1 : ((chiOStr c mZ ρb γ ν hχo T).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν] g₁)
    (h2 : ((chiOStr c mZ ρb γ ν hχo T).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν] g₂) :
    g₁ + g₂ =ᵐ[ageμ c (-1 / 2)] strSum (chiOStr c mZ ρb γ ν hχo T) := by
  rw [NearInst.ae_gainZ1Measure, NearInst.ae_z1Measure] at h1
  rw [NearInst.ae_gainHTMeasure, NearInst.ae_htRhoMeasure hρ] at h2
  filter_upwards [h1, h2] with p e1 e2
  simp only [Pi.add_apply, strSum, e1, e2]

/-- The canonical old source is additive a.e. (`χ_o` is linear). -/
theorem wo_rep_add (hρ : 0 < ρb) (hχo : IsOutwardCutoff χo) (T T' : StrG c mZ ρb γ ν) :
    strSum (chiOStr c mZ ρb γ ν hχo (T + T')) =ᵐ[ageμ c (-1 / 2)]
      strSum (chiOStr c mZ ρb γ ν hχo T) + strSum (chiOStr c mZ ρb γ ν hχo T') := by
  have e1 : ((chiOStr c mZ ρb γ ν hχo (T + T')).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν]
      ((chiOStr c mZ ρb γ ν hχo T).fst : Chart → Ten3) +
        ((chiOStr c mZ ρb γ ν hχo T').fst : Chart → Ten3) := by
    rw [map_add, WithLp.add_fst]
    exact Lp.coeFn_add _ _
  have e2 : ((chiOStr c mZ ρb γ ν hχo (T + T')).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν]
      ((chiOStr c mZ ρb γ ν hχo T).snd : Chart → Ten3) +
        ((chiOStr c mZ ρb γ ν hχo T').snd : Chart → Ten3) := by
    rw [map_add, WithLp.add_snd]
    exact Lp.coeFn_add _ _
  rw [NearInst.ae_gainZ1Measure, NearInst.ae_z1Measure] at e1
  rw [NearInst.ae_gainHTMeasure, NearInst.ae_htRhoMeasure hρ] at e2
  filter_upwards [e1, e2] with p h1 h2
  simp only [strSum, Pi.add_apply, h1, h2]
  abel

/-- The canonical old source is homogeneous a.e. -/
theorem wo_rep_smul (hρ : 0 < ρb) (hχo : IsOutwardCutoff χo) (r : ℝ) (T : StrG c mZ ρb γ ν) :
    strSum (chiOStr c mZ ρb γ ν hχo (r • T)) =ᵐ[ageμ c (-1 / 2)]
      r • strSum (chiOStr c mZ ρb γ ν hχo T) := by
  have e1 : ((chiOStr c mZ ρb γ ν hχo (r • T)).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν]
      r • ((chiOStr c mZ ρb γ ν hχo T).fst : Chart → Ten3) := by
    rw [map_smul, WithLp.smul_fst]
    exact Lp.coeFn_smul _ _
  have e2 : ((chiOStr c mZ ρb γ ν hχo (r • T)).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν]
      r • ((chiOStr c mZ ρb γ ν hχo T).snd : Chart → Ten3) := by
    rw [map_smul, WithLp.smul_snd]
    exact Lp.coeFn_smul _ _
  rw [NearInst.ae_gainZ1Measure, NearInst.ae_z1Measure] at e1
  rw [NearInst.ae_gainHTMeasure, NearInst.ae_htRhoMeasure hρ] at e2
  filter_upwards [e1, e2] with p h1 h2
  simp only [strSum, Pi.smul_apply, h1, h2, smul_add]

/-- **The canonical old sources are old `L²` data** (source 4155-4166, 2694-2700): measurable
(canonical `Lp` representatives), square integrable (`WardOldNormLe`), and vanishing a.e. where
`νs ≤ 6/5` (`chiOStrApply`, `χ̂_o = 0` on `(-∞, 6/5]`). -/
theorem wo_isOldL2_rep (hcmp : WardOldNormLe) (hρ : 0 < ρb) (hm : 0 ≤ mZ) (hν : 0 < ν)
    (hχo : IsOutwardCutoff χo) (T : StrG c mZ ρb γ ν) :
    IsOldL2 c ν (strSum (chiOStr c mZ ρb γ ν hχo T)) := by
  have hmeas : Measurable (strSum (chiOStr c mZ ρb γ ν hχo T)) :=
    (Lp.stronglyMeasurable (chiOStr c mZ ρb γ ν hχo T).fst).measurable.add
      (Lp.stronglyMeasurable (chiOStr c mZ ρb γ ν hχo T).snd).measurable
  obtain ⟨C, hC⟩ := hcmp c mZ ρb γ ν hρ hm hν χo hχo
  refine ⟨hmeas, ⟨hmeas.aestronglyMeasurable, lt_of_le_of_lt (hC T) ENNReal.ofReal_lt_top⟩, ?_⟩
  obtain ⟨a1, a2⟩ := chiOStrApply c mZ ρb γ ν χo hχo T
  rw [NearInst.ae_gainZ1Measure, NearInst.ae_z1Measure] at a1
  rw [NearInst.ae_gainHTMeasure, NearInst.ae_htRhoMeasure hρ] at a2
  filter_upwards [a1, a2] with p e1 e2 hp
  have h0 : cutFun χo ν p = 0 := hχo.zero _ hp
  simp only [strSum, e1, e2, h0, zero_smul, add_zero]

end Rep

end UnforcedLeray.Short.PartIIIb.Concrete
