import UnforcedLeray.Short.PartIIb.StatementsNonlinear
import UnforcedLeray.Lib.HeatR3.FTC
import UnforcedLeray.Analysis.LerayProjection.Basic

/-!
# `PartII-b:B3`: the heat remainder of the contraction-ball background (SP 2584-2633)

Source of record: `the November 2 reference manuscript` (73 pages).

Subsection "The datum, heat remainder, and pressure" (SP 2563-2643), for the background
`U = V₀ + E_εα + w = bgField p z` of a state `z` of the contraction ball of `short-bg:result`
(SP 2505-2524), its datum `a = p.datum (p.coord z)` (SP 2565-2583, `PartII-b:B2`) and the heat
profile `H_a(τ) = e^{νΔ}a_τ`, `a_τ(y) = e^{τ/2}a(e^{τ/2}y)` (SP 2584-2585,
`Blueprint.heatProfile`).  The statement `BallHeatRemainder` has three parts:

* `B3Stmt.UL4` (SP 2607-2610): "The inverse-distance bounds and the all-age expansion give
  `D^jV ∈ C_per L⁴`.  For `w`, interpolation between its `C_per L^p` derivatives and their
  uniform supremum bounds gives `D^jw ∈ C_per L⁴`.  Therefore `D^jU ∈ C_per L⁴` for `j ≤ 2`",
  as bounds of `U, DU, D²U` in `L⁴(ℝ³)` uniform in the phase;
* `B3Stmt.Core` (SP 2610-2628, "`Q = U − H_a ∈ X_p` ... Thus `Q ∈ C_per H²`"): `Q` together with
  the clauses of Theorem B3 that do not involve the pressure (`Blueprint.IsB3Core`): the datum
  clauses (SP 2563-2583), the periodicity, solenoidality, symmetry and bounds of `U`
  (`short-bg:strong`, SP 2519-2562), and `Q(τ) = U(τ) − H_a(τ)` a.e., `Q` continuous and periodic;
* `B3Stmt.Evol` (SP 2610-2632: "`𝕋 = U ⊗ U ∈ C_per H²`", "`Q` solves `A₀Q = −𝐏 div 𝕋`",
  "`(∂_τ − y·∇/2)Q = νΔQ + Q/2 − 𝐏 div 𝕋 ∈ C_per L²`"): for the smooth representative `U − H_a` of
  `Q`, at every phase, `U·∇U ∈ L²` and `(∂_τ − ½y·∇ − νΔ − ½)(U − H_a) = −𝐏(U·∇U)` a.e., `𝐏` the
  `L²` Leray projection; `div 𝕋 = U·∇U` since `div U = 0` (`(div T)_i = ∂_jT_ij`, SP 117).

The quantifiers are those of `StrongRegularity` (`B3Stmt.AtBallStates`): the slow data `Σ, (λ, q)`
and the ball constants are fixed before `ν₀`, and the statement holds for every state `z` solving
the projected equation with `‖z‖_Z ≤ C₁ν^{-k₁}e^{m/ν}ε^{3/11}`, `2m < 3d₋/11` (SP 2507-2512).

Not exported: the raw-heat comparison `V − H_a ∈ C_per H^k ∩ X_p` (`short-bg:raw-heat`,
SP 2586-2603) is the first step of the proof of `Q ∈ X_p` (`Q = (V − H_a) + w`) and is cited by
no later line; the `t^{1/4}` rate, the local `L²` convergence of `u_ν` and the pressure `p_U`
(SP 2633-2643) are not part of this statement (the pressure belongs to `PartII-b:B4`).

`B3Stmt.ballHeatRemainder_of` assembles the statement from the three parts.  Consumers: the ward
bridges `bgUL4_of_ballHeatRemainder`, `bgBallRemainder_of_ballHeatRemainder`,
`bgRemainderEvol_of_ballHeatRemainder` (`Short/PartIII-b/Sub/PartIII-b_C_ward_13_8_1/B3Bridge.lean`)
and `PartII-b:B4`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

namespace B3Stmt

/-- **A property of every state of the contraction ball** (SP 2505-2524, the quantifiers of
`StrongRegularity`): for the slow age `Σ > 0`, the growing eigenpair `(λ, q)`, `0 < m` with
`2m < 3d₋/11` and the ball constants `C₁ > 0, k₁`, there is `ν₀ > 0` such that at every level of
the regime with `ν ≤ ν₀`, `p.ageCut = Σ`, `p.mode = q`, every solution `z` of the projected
equation with `‖z‖_Z ≤ C₁ν^{-k₁}e^{m/ν}ε^{3/11}` has `Φ p z`. -/
def AtBallStates (Φ : (p : Params) → p.Z → Prop) : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → 2 * m < 3 * dm / 11 → ∀ (C₁ : ℝ) (k₁ : ℕ), 0 < C₁ →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ z : p.Z, ProjectedEquation p z →
      ‖z‖ ≤ C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) → Φ p z

/-- **`D^jU ∈ C_per L⁴` for `j ≤ 2`** (SP 2607-2610): `U(τ) = bgField p z τ`, `DU(τ)` and
`D²U(τ)` are bounded in `L⁴(ℝ³)` uniformly in the phase. -/
def UL4 (p : Params) (z : p.Z) : Prop :=
  ∃ C : ℝ, ∀ τ : ℝ,
    eLpNorm (bgField p z τ) 4 volume ≤ ENNReal.ofReal C ∧
    eLpNorm (fun y => fderiv ℝ (bgField p z τ) y) 4 volume ≤ ENNReal.ofReal C ∧
    eLpNorm (fun y => iteratedFDeriv ℝ 2 (bgField p z τ) y) 4 volume ≤ ENNReal.ofReal C

/-- **The heat remainder `Q = U − H_a ∈ C_per H²` with the clauses of Theorem B3** (SP 2563-2628;
the datum `a = p.datum (p.coord z)`, SP 2565-2583; `U = bgField p z`, SP 2519-2562): there is
`Q : ℝ → H²` with `Blueprint.IsB3Core ν P a U Q`, `P = p.period`. -/
def Core (p : Params) (z : p.Z) : Prop :=
  ∃ Q : ℝ → UnforcedLeray.SobolevGraph.H2,
    UnforcedLeray.Blueprint.IsB3Core p.ν p.period (p.datum (p.coord z)) (bgField p z) Q

/-- **The evolution of the heat remainder** (SP 2610-2632): at every phase `τ`, `U·∇U ∈ L²` and
the smooth representative `W = U − H_a` of `Q` satisfies
`∂_τW − ½ y·∇W − νΔW − ½W = −𝐏(U·∇U)` a.e. (`= −𝐏 div 𝕋`, `𝕋 = U ⊗ U`, `div U = 0`), with
`y·∇W = DW(y)[y]`, `Δ = Heat.vlap`, `𝐏` the `L²` Leray projection. -/
def Evol (p : Params) (z : p.Z) : Prop :=
  ∀ τ : ℝ, MemLp (fun y => fderiv ℝ (bgField p z τ) y (bgField p z τ y)) 2 volume ∧
    (fun y => deriv (fun t => bgField p z t y -
          UnforcedLeray.Blueprint.heatProfile p.ν (p.datum (p.coord z)) t y) τ -
        (1 / 2 : ℝ) • fderiv ℝ (fun y' => bgField p z τ y' -
          UnforcedLeray.Blueprint.heatProfile p.ν (p.datum (p.coord z)) τ y') y y -
        p.ν • UnforcedLeray.Heat.vlap (fun y' => bgField p z τ y' -
          UnforcedLeray.Blueprint.heatProfile p.ν (p.datum (p.coord z)) τ y') y -
        (1 / 2 : ℝ) • (bgField p z τ y -
          UnforcedLeray.Blueprint.heatProfile p.ν (p.datum (p.coord z)) τ y))
      =ᵐ[volume] ⇑(-(UnforcedLeray.Leray.projection (UnforcedLeray.toL2
          (fun y => fderiv ℝ (bgField p z τ) y (bgField p z τ y)))))

theorem AtBallStates.and {Φ Ψ : (p : Params) → p.Z → Prop} (h1 : AtBallStates Φ)
    (h2 : AtBallStates Ψ) : AtBallStates fun p z => Φ p z ∧ Ψ p z := by
  intro Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₁, hν₁, H1⟩ := h1 Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₂, hν₂, H2⟩ := h2 Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, fun p d hreg hν hS hq' z hz hzn => ⟨?_, ?_⟩⟩
  · exact H1 p d hreg (hν.trans (min_le_left _ _)) hS hq' z hz hzn
  · exact H2 p d hreg (hν.trans (min_le_right _ _)) hS hq' z hz hzn

end B3Stmt

open B3Stmt in
/-- **`PartII-b:B3`: the heat remainder of the contraction-ball background** (SP 2584-2633, with
the datum of SP 2563-2583 and the ball of SP 2505-2524): at every state `z` of the contraction
ball, the background `U = bgField p z` has `D^jU ∈ C_per L⁴` for `j ≤ 2` (`UL4`), the heat
remainder `Q = U − H_a ∈ C_per H²` with the clauses of Theorem B3 for the datum
`a = p.datum (p.coord z)` (`Core`), and `(∂_τ − y·∇/2)Q = νΔQ + Q/2 − 𝐏 div 𝕋` (`Evol`). -/
def BallHeatRemainder : Prop :=
  AtBallStates fun p z => UL4 p z ∧ Core p z ∧ Evol p z

/-- Assembly of `BallHeatRemainder` from its three parts. -/
theorem B3Stmt.ballHeatRemainder_of (h1 : B3Stmt.AtBallStates B3Stmt.UL4)
    (h2 : B3Stmt.AtBallStates B3Stmt.Core) (h3 : B3Stmt.AtBallStates B3Stmt.Evol) :
    BallHeatRemainder :=
  h1.and (h2.and h3)

end UnforcedLeray.Short.IIb
