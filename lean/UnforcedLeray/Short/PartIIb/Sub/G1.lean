import UnforcedLeray.Short.PartIIb.Defs

/-!
# Part II-b, task `PartII-b:G1`: the strong late coefficient bound (conditional)

Source of record: `the November 2 reference manuscript`, lines 2412-2431, display
`short-bg:strong-late-coeff` (SP 2417):

`sup_{s>S} (|V_0| + |DV_0|) ≤ 𝒫_ν (S^{-1/2} + ε)`,

for the Cartesian raw field `V_0 = U_raw` (`Params.raw`), including the frame term `ε s v_1`.



* `s` is the *age coordinate* `Axi.age R y = R²/ϱ(y)²` of the point `y ∈ ℝ³`, not the phase time
  `τ`. The region `s > S` is the tube `ϱ < R/√S` around the axis, *including the axis itself*
  (where Lean's `age` is the junk value `0`); so the statement is over `y ∈ axis ∨ S < age R y`
  and contains the claim that `U_raw(τ)` is differentiable there.
* `S ≥ 1`: this is the late-age regime; the manuscript's `S` is large, and below `S = 1` the bound
  needs the early-age train bounds (`RingEarlyBound`), which are not part of this display.
* Constants `(C, k, ν₀)` depend only on `d_±` (the regime `BgRegime`); `p.raw` depends only on
  `ν, c = ν⁻², ε = e^{-d/ν}` and the actual train, not on `p.mode`, `p.ageCut`.
* The actual train is the BUC train of Part I (SP 270-288, 2040): `BgRegime` carries
  `train_buc : PartI.IsBUCTrain p.train` (`Defs.lean`), which is the hypothesis `IsBUCTrain tr` of
  the Part I estimates `TrainMeanExpansion`, `TrainFluctuationDecay`, `TrainMeanEquations`
  (`Short/PartI/StatementsTrain.lean`) used by `RawProfileLate`.

## Decomposition

The Cartesian bound is a calculus statement (`NvFderivBound`, `BoundThroughAxis`) about the
profile `b_raw = (v_1, v_2 + εH)` (`RawProfileLate`, the Part I mean-expansion input) and the smooth
extension through the axis (`RawContDiff`). With `ε = R⁻¹` and `s = age R y` the exact chart
computation gives

`DV[w] = s (e_r·w) frame(Q_ε b) + s w_3 frame(∂_η b) + √s b_r De_r[w]`, `Q_ε = ∂_q - ε(K+1)`,
`K = 2s∂_s + η∂_η`, `|De_r[w]| ≤ |w|/ϱ`, `√s/ϱ = ε s`,

so `‖DV‖ ≤ s(‖∂_η b‖ + ‖Q_ε b‖ + ε|b_r|)` (the three derivative types of SP 2422-2423) and
`‖V‖ = √s ‖b‖`.

Proved here: `strongLateCoeff_of` (no sorry). Leaves: `RawProfileLate` (`PartII-b:G1/1`),
`NvFderivBound` (`PartII-b:G1/2`), `BoundThroughAxis` (`PartII-b:G1/3`), `RawContDiff`
(`PartII-b:G1/4`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

/-- The gradient quantity of a profile at a chart point `x = (s, (q, η))`:
`s(‖∂_η b‖ + ‖Q_ε b‖ + ε|b_r|)` with `Q_ε b = ∂_q b - ε(2s∂_s b + η∂_η b + b)` (SP 2422-2423:
`s∂_η b`, `s[∂_q - ε(K+1)]b`, and the frame term `ε s v_1`). -/
def gradProfileQuantity (ε : ℝ) (b : ℝ × (ℝ × ℝ) → Axi.Merid) (x : ℝ × (ℝ × ℝ)) : ℝ :=
  x.1 * (‖Axi.dEta b x‖ +
    ‖Axi.dQ b x - ε • ((2 * x.1) • Axi.dS b x + x.2.2 • Axi.dEta b x + b x)‖ +
    ε * |b x 0|)

/-- The full late quantity `√s‖b‖ + s(‖∂_η b‖ + ‖Q_ε b‖ + ε|b_r|)`: it bounds `|V_0| + |DV_0|`. -/
def lateProfileQuantity (ε : ℝ) (b : ℝ × (ℝ × ℝ) → Axi.Merid) (x : ℝ × (ℝ × ℝ)) : ℝ :=
  Real.sqrt x.1 * ‖b x‖ + gradProfileQuantity ε b x

/-- **`short-bg:strong-late-coeff`** (SP 2412-2431, display at 2417). -/
def StrongLateCoeff : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → ∀ S : ℝ, 1 ≤ S →
      ∀ (τ : ℝ) (y : Space), (y ∈ Axi.axis ∨ S < Axi.age p.R y) →
        DifferentiableAt ℝ (p.raw τ) y ∧
        ‖p.raw τ y‖ + ‖fderiv ℝ (p.raw τ) y‖ ≤ C * (p.ν ^ k)⁻¹ * (S ^ (-(1 / 2 : ℝ)) + p.ε)

/-- **Profile level** (SP 2424-2431; Part I input `TrainMeanExpansion`, `TrainFluctuationDecay`,
`TrainMeanEquations`): for the raw profile `b_raw = (v_1, v_2 + εH)` of the actual train, at
every chart point with `s > S ≥ 1`, `b_raw` is differentiable and
`√s‖b‖ + s(‖∂_η b‖ + ‖Q_ε b‖ + ε|b_r|) ≤ 𝒫_ν (S^{-1/2} + ε)`. The mean stream is
`S_0 = a_0 G_{νs} + a_2 ∂_η² G_{νs} + O_weighted(𝒫_ν s^{-5/2})`, `v_1 = -∂_η S_0`,
`H = 2a_0 G_{νs} + 4a_2 ∂_η² G_{νs} + ⋯`, and `(K+1) G_{νs} = 0` cancels the radial derivative:
`(K+1)H = -8 a_2 ∂_η² G_{νs} + O_weighted(𝒫_ν s^{-5/2})`; every fluctuation derivative is
exponentially small; the axial mean velocity has the genuine `O(ε)` floor. -/
def RawProfileLate : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → ∀ S : ℝ, 1 ≤ S →
      ∀ x : ℝ × (ℝ × ℝ), S < x.1 →
        DifferentiableAt ℝ (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) x ∧
        lateProfileQuantity p.ε (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) x ≤
          C * (p.ν ^ k)⁻¹ * (S ^ (-(1 / 2 : ℝ)) + p.ε)

/-- **Cartesian gradient of the ring lift** (pure calculus, SP 2422-2423): for a profile `b`
differentiable at the chart point of `y ∉ axis`, the lift `N_v b(τ, ·)` is differentiable at `y`
and `‖D N_v b(τ, y)‖ ≤ s(‖∂_η b‖ + ‖Q_ε b‖ + ε|b_r|)` at the chart point, `s = age R y`,
`ε = R⁻¹`. -/
def NvFderivBound : Prop :=
  ∀ (R τ : ℝ) (b : ℝ × (ℝ × ℝ) → Axi.Merid) (y : Space), 0 < R → y ∉ Axi.axis →
    DifferentiableAt ℝ b (Axi.chart R τ y) →
      DifferentiableAt ℝ (Axi.Nv R b τ) y ∧
      ‖fderiv ℝ (Axi.Nv R b τ) y‖ ≤ gradProfileQuantity R⁻¹ b (Axi.chart R τ y)

/-- **A bound through the axis** (continuity): a `C¹` field satisfying the bound at all off-axis
points of age `> S` satisfies it on the axis (axis points are limits of off-axis points of
arbitrarily large age). -/
def BoundThroughAxis : Prop :=
  ∀ (R S M : ℝ) (F : Space → Space), 0 < R → ContDiff ℝ 1 F →
    (∀ y : Space, y ∉ Axi.axis → S < Axi.age R y → ‖F y‖ + ‖fderiv ℝ F y‖ ≤ M) →
    ∀ y₀ ∈ Axi.axis, ‖F y₀‖ + ‖fderiv ℝ F y₀‖ ≤ M

/-- **Smoothness of `U_raw` through the axis** (SP 1214-ff `sct:lift`, `RingAxisSmooth`,
`RingBoundedDerivs`; Part II-a `PartII-a:R06`): in the regime and for small `ν`, every phase
slice `p.raw τ` is `C^∞` on all of `ℝ³`. -/
def RawContDiff : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → ∀ τ : ℝ, ContDiff ℝ ∞ (p.raw τ)

/-- **`PartII-b:G1`, conditional form.** -/
theorem strongLateCoeff_of (h1 : RawProfileLate) (h2 : NvFderivBound) (h3 : BoundThroughAxis)
    (h4 : RawContDiff) : StrongLateCoeff := by
  intro dm dp hdm
  obtain ⟨C, k, ν₀, hC, hν₀, H1⟩ := h1 dm dp hdm
  obtain ⟨ν₁, hν₁, H4⟩ := h4 dm dp hdm
  refine ⟨C, k, min ν₀ ν₁, hC, lt_min hν₀ hν₁, ?_⟩
  intro p d hreg hν S hS τ y hy
  have hνa : p.ν ≤ ν₀ := hν.trans (min_le_left _ _)
  have hνb : p.ν ≤ ν₁ := hν.trans (min_le_right _ _)
  have hsm : ContDiff ℝ ∞ (p.raw τ) := H4 p d hreg hνb τ
  have hR : 0 < p.R := p.R_pos
  have hRinv : p.R⁻¹ = p.ε := by
    show (p.ε⁻¹)⁻¹ = p.ε
    exact inv_inv _
  -- the bound at off-axis points
  have off : ∀ y : Space, y ∉ Axi.axis → S < Axi.age p.R y →
      ‖p.raw τ y‖ + ‖fderiv ℝ (p.raw τ) y‖ ≤ C * (p.ν ^ k)⁻¹ * (S ^ (-(1 / 2 : ℝ)) + p.ε) := by
    intro y hax hSy
    set b := UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ with hb
    have hx : S < (Axi.chart p.R τ y).1 := hSy
    obtain ⟨hdiff, hq⟩ := H1 p d hreg hνa S hS _ hx
    obtain ⟨_, hgrad⟩ := h2 p.R τ b y hR hax hdiff
    rw [hRinv] at hgrad
    have hev : p.raw τ =ᶠ[𝓝 y] Axi.Nv p.R b τ := by
      filter_upwards [Axi.isOpen_compl_axis.mem_nhds hax] with z hz
      exact p.raw_eq_off_axis τ z hz
    have hnorm : ‖p.raw τ y‖ = Real.sqrt (Axi.age p.R y) * ‖b (Axi.chart p.R τ y)‖ := by
      rw [p.raw_eq_off_axis τ y hax]
      exact Axi.norm_Nv p.R b τ hax
    rw [hnorm, hev.fderiv_eq]
    refine le_trans ?_ hq
    unfold lateProfileQuantity
    have : Real.sqrt (Axi.age p.R y) = Real.sqrt (Axi.chart p.R τ y).1 := rfl
    rw [this]
    linarith
  rcases hy with hy | hy
  · exact ⟨(hsm.differentiable (by simp)).differentiableAt,
      h3 p.R S _ (p.raw τ) hR (hsm.of_le (by simp)) off y hy⟩
  · by_cases hax : y ∈ Axi.axis
    · exact ⟨(hsm.differentiable (by simp)).differentiableAt,
        h3 p.R S _ (p.raw τ) hR (hsm.of_le (by simp)) off y hax⟩
    · exact ⟨(hsm.differentiable (by simp)).differentiableAt, off y hax hy⟩

end UnforcedLeray.Short.IIb
