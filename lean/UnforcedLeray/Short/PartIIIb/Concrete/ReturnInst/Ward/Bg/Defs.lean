import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Defs
import UnforcedLeray.Short.PartIIb.ExactSplit
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.Defs

/-!
# The background of the Ward fields on the young support (source 4155, 4194-4195, 4291-4294,
2505-2562, 2607-2612, 2641-2642, 2706-2711, 5225-5260)

Source of record: `the November 2 reference manuscript` (73 pages).

Task `ORG:return-concrete/instance-3/ward/bg`.  `WardBgBound` (`Ward/Defs.lean` §3) asked for a
pointwise bound of the pressure gradient `∇p` on the young support.  The source never bounds `∇p`
pointwise: it controls the pressure in integral norms (`∇p_V = -(I-𝐏)(V·∇V)`,
`‖∇p_V‖₂ ≤ C‖V‖_∞‖DV‖₂`, and `∇(p - p_V)` in `Y_{11/4}`, 5245-5260; globally
`p_U = Σ R_iR_j(U_iU_j)` with `U⊗U ∈ C_per H²`, 2612, 2641-2642) and pairs it with the ordinary
`L^∞_τL^∞_y` bound of the returned first derivatives: "no product of two merely phase-`L²`
factors is used for the global pressure term" (5238-5244).  Its sup bounds are those of the
velocity: "Since `U` is bounded" (4155), "since `U, DU` are bounded" (4194-4195), `short-bg:strong`
(2538-2541) and all spatial orders (2552-2559, "all factors through order `k` are bounded";
2607-2609, "their uniform supremum bounds").

## Definitions

* `WardBgBoundL R ν c U p M`: on the young support `ϱ ≥ R√ν`, `|U|, |∂_jU|, |∂_j∂_lU| ≤ M`, and the
  chart coefficient of `∇p` restricted to the young chart region `νs ≤ 1` has `L²(srcMeasure c)`
  norm `≤ M` (by the lift identity 2684-2687 this is `R⁻¹‖1_{young}∇p‖_{Y₂}`, the norm of the
  source's `‖∇p_V‖₂`, 5247);
* `WardHBoundL`, `WardEBoundL`: `WardHBound`, `WardEBound` with `WardBgBoundL` in place of
  `WardBgBound` (re-emitted `PartIII-b:C/ward/10`, `/11`);
* `BgYoungW2` (here) and `BgPresY2B` (`Bg/PresY2/Defs.lean`): the two background facts, from which
  `WardBgBoundL` follows at a level (`wardBgBoundL_of_level`).  `BgYoungW2` is stated at the levels
  of the regime for every exact split (`IIb.ExactSplitII`); `BgPresY2B` at the levels of the
  contraction-ball background (`AtBallLevels`: the quantifiers of `BgAxiLevels`, `IIb.BgRegime`,
  `IsBallSplit`, `IsExactProfile`, slow age `p.ageCut = Σ`, growing eigenpair `p.mode = q`,
  `0 < m`, `2m < 3d₋/11`, `C₁ > 0`).

## Why the pressure fact needs the ball and the `W^{2,∞}` fact does not
(task `PartIII-b:C/ward/ball/org`)

The pressure fact reads `∇p` on the half-plane `φ = 0` only, which is `R⁻¹‖1_{young}∇p‖_{Y₂}` only
for axisymmetric `U` (2688-2689), and its `L²` bound comes from `D^jU ∈ C_per L⁴` (2607-2612) and
`p_U = Σ R_iR_j(U_iU_j)` (2641-2642).  The symmetry is a property of *the* background of
`short-bg:result`, the fixed point of the contraction on the ball `‖z‖_Z ≤ 𝒫_νe^{m/ν}ε^{3/11}` with
`2m < 3d₋/11` (2505-2524: "no-swirl symmetry ... preserved at each iteration"), whose bound `ρ_b`
the return fixes (2706-2711); `IIb.ExactSplitII` bounds only `|αᵢ|` and the `11/4 + ∞` energy of
`r_b`, not `‖z‖_Z` (`Background/Ball.lean`).  So the pressure fact is stated at the ball levels
(`BgPresY2B`, finding of `PartIII-b:C/ward/13/org`; its earlier `ExactSplitII` form is retired)
and the actual levels supply the ball datum (`SeqData.IsActualLevel.ball`).  The `W^{2,∞}` bound
uses no symmetry: the qualitative bootstrap of 2525-2562 ("all factors through order `k` are
bounded", "This proves all spatial orders") uses only `w ∈ X_p` (`z ∈ p.Z`), `w ∈ L^∞` (the energy
of `ExactSplitII`) and the projected equation, not the smallness of the ball (decomposition of
`PartIII-b:C/ward/12/org`, `Bg/YoungW2/Defs.lean`), so `BgYoungW2` keeps its `ExactSplitII` form
and the actual levels supply it through `IsActualLevel.split`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (Params)

/-! ## 1. The background bound on the young support -/

/-- **The background of the Ward fields on the young support** (source 4155 "Since `U` is
bounded", 4194-4195 "since `U, DU` are bounded, `h ∈ Y₂`", 2525-2562 and 2607-2609 for the second
derivatives; 5245-5260 and 2612, 2641-2642 for the pressure): on `ϱ ≥ R√ν` (`χ_y(νR²/ϱ²)` vanishes
for `ϱ ≤ R√ν`, 4167, so the Ward fields vanish off this set away from the axis, 4306-4311) the
background `U` and its first and second partials are bounded by `M`; and the chart coefficient
`s^{-1/2}∇p` of the full pressure gradient, read at `(chartTau R q, chartY R q)` and restricted to
the young chart region `νs ≤ 1`, has `L²(srcMeasure c)` norm at most `M` (lift identity
2684-2687: `R⁻¹‖1_{young}∇p‖_{Y₂}`).  The pressure is paired with the `L^∞_τL^∞_y` bound of the
returned first derivatives (5238-5244). -/
def WardBgBoundL (R ν c : ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ) (M : ℝ) : Prop :=
  (∀ (τ : ℝ) (y : Space), R * Real.sqrt ν ≤ ϱ y →
    ‖U τ y‖ ≤ M ∧ (∀ j : Fin 3, ‖physPd (U τ) j y‖ ≤ M) ∧
      ∀ j l : Fin 3, ‖physPd2 (U τ) j l y‖ ≤ M) ∧
  eLpNorm ({q : Chart | ν * q.1 ≤ 1}.indicator fun q : Chart =>
      (Real.sqrt q.1)⁻¹ • physGrad (p (NearInst.chartTau R q)) (NearInst.chartY R q))
    2 (srcMeasure c) ≤ ENNReal.ofReal M

/-- **`L²` bound of `h = [U, X]`** in the gained body norm (source 4194-4195: "since `U, DU` are
bounded, `h ∈ Y₂`"; young support 4306-4311), for a background with `WardBgBoundL` (only its sup
clause enters). -/
def WardHBoundL : Prop :=
  ∀ (ν μ R c γ M : ℝ) (χy : ℝ → ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ),
    IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ → WardBgBoundL R ν c U p M →
    ∃ C : ℝ, ∀ g : Chart → Ten3, IsOldL2 c ν g →
      eLpNorm (coefOf R (wardH ν μ R c χy U g)) 2 (bodyMeasure c γ ν) ≤
        ENNReal.ofReal C * eLpNorm g 2 (ageμ c (-1 / 2))

/-- **`L²` bound of the residual `Ẽ_μ`** in the ungained body norm (source 4291-4294 "the
actual-range body estimates below show `Ẽ_μ ∈ Y₂`", 5196-5297; every term contains a derivative of
`X` or `Y`, 5296-5297, so `Ẽ_μ` has young support), for a background with `WardBgBoundL`: the
terms `2U·∇Y`, `C_diff`, `(U⊗U):D²X` use the sup clause; the pressure term `(DX + DXᵀ)∇p` pairs
the `Y₂` clause of `∇p` with the `L^∞_τL^∞_y` bound of `DX` on the young support (5238-5244). -/
def WardEBoundL : Prop :=
  ∀ (ν μ R c M : ℝ) (χy : ℝ → ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ),
    IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ → WardBgBoundL R ν c U p M →
    ∃ C : ℝ, ∀ g : Chart → Ten3, IsOldL2 c ν g →
      eLpNorm (coefOf R (wardE ν μ R c χy U p g)) 2 (srcMeasure c) ≤
        ENNReal.ofReal C * eLpNorm g 2 (ageμ c (-1 / 2))

/-! ## 2. The background facts -/

/-- **The exact background is bounded in `W^{2,∞}` on the young support** (source 2525-2562:
`short-bg:strong` gives `‖w‖_{W^{1,∞}} + ‖E_εα‖_{W^{1,∞}}` bounded, 2538-2541, and "This proves all
spatial orders", "all factors through order `k` are bounded", 2552-2559; 2607-2609: the derivatives
of `w` have "uniform supremum bounds", those of `V` follow from the inverse-distance bounds and the
all-age expansion; 4155, 4194-4195): for the growing eigenpair `q = p.mode` and a window
`[d₋, d₊]` there is `ν₀ > 0` such that at every level of the regime with `ν ≤ ν₀`, every exact split
`U = V + r_b` (`V = U_raw + E_εα`, `r_b = w`, `IIb.ExactSplitII`) whose sum is an exact profile with
some pressure (`IsExactProfile`, 4139-4141) has `U`, `∂_jU`, `∂_j∂_lU` bounded on the young support
`ϱ ≥ R√ν` (`s ≤ 1/ν`), at every phase.  No ball datum is needed: the bootstrap is qualitative
and uses only `z ∈ p.Z`, `r_b ∈ L^∞` and the projected equation (`Ward/Bg/YoungW2/Defs.lean`). -/
def BgYoungW2 : Prop :=
  ∀ (lam : ℂ) (q : UnforcedLeray.Blueprint.Planar.Profile),
    UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d ρb S_in : ℝ) (V rb : ℝ → SpatialField) (pres : ℝ → Space → ℝ),
      UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ → p.mode = q →
      UnforcedLeray.Short.IIb.ExactSplitII p ρb S_in V rb →
      IsExactProfile p.ν p.period (fun τ y => V τ y + rb τ y) pres →
      ∃ M : ℝ, ∀ (τ : ℝ) (y : Space), p.R * Real.sqrt p.ν ≤ ϱ y →
        ‖V τ y + rb τ y‖ ≤ M ∧
          (∀ j : Fin 3, ‖physPd (fun y' => V τ y' + rb τ y') j y‖ ≤ M) ∧
          ∀ j l : Fin 3, ‖physPd2 (fun y' => V τ y' + rb τ y') j l y‖ ≤ M

/-! The pressure fact is `BgPresY2B` (`Bg/PresY2/Defs.lean`, source 2505-2524, 2607-2612,
2641-2642, 2684-2689, 5245-5260), at the levels of the contraction-ball background; its
`ExactSplitII` form (the earlier `BgPresY2`) was retired by `PartIII-b:C/ward/ball/org`. -/

/-- **`WardBgBoundL` at a level** from the two background facts: the sup clause of `BgYoungW2`
and the `Y₂` clause of `BgPresY2B`, with `M` the larger of the two bounds. -/
theorem wardBgBoundL_of_level {R ν c M₁ : ℝ} {U : ℝ → SpatialField} {p : ℝ → Space → ℝ}
    (h1 : ∀ (τ : ℝ) (y : Space), R * Real.sqrt ν ≤ ϱ y →
      ‖U τ y‖ ≤ M₁ ∧ (∀ j : Fin 3, ‖physPd (U τ) j y‖ ≤ M₁) ∧
        ∀ j l : Fin 3, ‖physPd2 (U τ) j l y‖ ≤ M₁)
    (h2 : eLpNorm ({q : Chart | ν * q.1 ≤ 1}.indicator fun q : Chart =>
        (Real.sqrt q.1)⁻¹ • physGrad (p (NearInst.chartTau R q)) (NearInst.chartY R q))
      2 (srcMeasure c) < ⊤) :
    ∃ M : ℝ, WardBgBoundL R ν c U p M := by
  set E := eLpNorm ({q : Chart | ν * q.1 ≤ 1}.indicator fun q : Chart =>
      (Real.sqrt q.1)⁻¹ • physGrad (p (NearInst.chartTau R q)) (NearInst.chartY R q))
    2 (srcMeasure c) with hE
  refine ⟨max M₁ E.toReal, fun τ y hy => ?_, ?_⟩
  · obtain ⟨a, b, d⟩ := h1 τ y hy
    exact ⟨a.trans (le_max_left _ _), fun j => (b j).trans (le_max_left _ _),
      fun j l => (d j l).trans (le_max_left _ _)⟩
  · rw [← hE]
    calc E = ENNReal.ofReal E.toReal := (ENNReal.ofReal_toReal h2.ne).symm
      _ ≤ ENNReal.ofReal (max M₁ E.toReal) := ENNReal.ofReal_le_ofReal (le_max_right _ _)

end UnforcedLeray.Short.PartIIIb.Concrete
