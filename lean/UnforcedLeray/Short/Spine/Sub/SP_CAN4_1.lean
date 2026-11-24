import UnforcedLeray.Short.Spine.Sub.SP_CAN4

/-!
# Spine: `MildSpatialSmoothing` cut into its leaf statements (task `Spine:SP-CAN/4/1`)

Target (`Short/Spine/Sub/SP_CAN4.lean`): `MildSpatialSmoothing`, i.e. under `GreenAll`, a mild
solution `V` (`V θ = S θ θ' (V θ')`, `0 < θ ≤ θ'`) takes values in every `X_{G,j}` for `θ > 0` and
is continuous into each `X_{G,j}` (`IsXGjContinuous V`).

Source of record: `the November 2 reference manuscript`, line 1086 ("bounded in
`X_G` as `θ ↓ 0` and smooth for positive `θ`") and lines 1134-1145 (`L : X_{G,j} → X_{G,j}`
bounded; one-derivative heat gain `‖e^{aD}‖_{X_{G,j}→X_{G,j+1}} ≤ C_j a^{-1/2}` for `0 < a ≤ 1`;
"Duhamel therefore gains one derivative ... its integral kernel is integrable"); old manuscript
`paper/main.tex` 1867-1888 (read only).

## The cut


source describes, which needs only the Duhamel identity already proved (`Cons.G3b.S_mild`,
`CanonicalMild.S_mild_interval`) and no bound of `S` on `X_{G,j}`:

`MildLevel V j` says: `V θ ∈ X_{G,j}` for every `θ > 0`, and `θ ↦ ‖V θ‖_{X_{G,j}}` is bounded on
every compact `[α, β] ⊂ (0, ∞)`.

* `MildBase`: `MildLevel V 0` (`X_{G,0} = X_G`, `‖V s‖ ≤ e^{β‖L₀‖}‖V β‖` on `[α, β]`).
* `MildLevelStep`: `MildLevel V j → MildLevel V (j+1)`. With `θ' = e θ`,
  `V θ = e^{D} V θ' + ∫_θ^{eθ} e^{log(v/θ) D} L₀ V(v) dv`; the first term gains one derivative by
  `B0123.expD_smoothing`, the integrand lies in `X_{G,j+1}` with norm
  `≤ C_L K (log(v/θ))^{-1/2}` (`B0122.L0_mem_XGj_norm`, `B0123.expD_smoothing`), and the integral
  stays in `X_{G,j+1}` by `XGjIntervalIntegralMem` and `LogKernelIntegral`.
* `MildContinuous`: `V` is continuous into `X_G` on `(0, ∞)` (`continuousOn_S_left`).
* `XGjContinuousOfBounds`: continuity into `X_G` plus `MildLevel V (j+1)` gives continuity of
  `θ ↦ (I - D)^{j/2} V θ` into `X_G` (interpolation `‖f‖_j² ≤ ‖f‖_0^{2/(j+1)} ‖f‖_{j+1}^{2j/(j+1)}`).

`mildSpatialSmoothing_of` is the assembly (induction on `j`).

Status: nothing of the PDE regularity is proved here; `MildSpatialSmoothing` stays OPEN until the
leaf statements are proved. No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b

/-- **Level-`j` regularity of a curve** (the induction hypothesis of the smoothing argument,
shorter proof lines 1141-1145): `V θ ∈ X_{G,j}` for all `θ > 0`, and the graph norm
`‖V θ‖_{X_{G,j}}` is bounded on every compact interval `[α, β] ⊂ (0, ∞)`. -/
def MildLevel (V : ℝ → XG) (j : ℕ) : Prop :=
  (∀ s : ℝ, 0 < s → V s ∈ B0123.XGj j) ∧
  ∀ α β : ℝ, 0 < α → α ≤ β → ∃ K : ℝ, ∀ s ∈ Icc α β, ∀ h : V s ∈ B0123.XGj j,
    B0123.xgjNorm j ⟨V s, h⟩ ≤ K

/-- **Leaf 1, closure of `X_{G,j}` under interval integrals** (a Bochner integral of an
`X_G`-valued function with values in `X_{G,j}` and a majorant of the `X_{G,j}` graph norm stays in
`X_{G,j}`, with the integral bound). Proof: apply the bounded linear maps
`T_N f = (√(1 + (1+n)^j) ⟪e_n, f⟫)_{n ≤ N}` (finite-dimensional range) to `∫ F`, commute with the
integral (`ContinuousLinearMap.integral_comp_comm`), use `intervalIntegral.norm_integral_le_of_norm_le`
and let `N → ∞` (`B0123.mem_XGj_iff`, `B0123.hasSum_xgjNorm_sq`). No measurability of
`u ↦ ‖F u‖_{X_{G,j}}` is needed. -/
def XGjIntervalIntegralMem : Prop :=
  ∀ (j : ℕ) (F : ℝ → XG) (G : ℝ → ℝ) (a b : ℝ), a ≤ b →
    IntervalIntegrable F volume a b → IntervalIntegrable G volume a b →
    (∀ᵐ u ∂volume, u ∈ Ioc a b → ∃ h : F u ∈ B0123.XGj j, B0123.xgjNorm j ⟨F u, h⟩ ≤ G u) →
    ∃ h : (∫ u in a..b, F u) ∈ B0123.XGj j,
      B0123.xgjNorm j ⟨∫ u in a..b, F u, h⟩ ≤ ∫ u in a..b, G u

/-- **Leaf 2, the Duhamel kernel is integrable** (shorter proof lines 1144-1145: "its integral
kernel is integrable"): on the unit turnover interval `[θ, eθ]` the heat-gain kernel
`(log(v/θ))^{-1/2}` is interval integrable with integral at most `5 θ` (the exact value is
`θ ∫₀¹ e^w w^{-1/2} dw ≈ 2.93 θ`). Proof: `log x ≥ (x - 1)/x ≥ (x - 1)/e` for `x = v/θ ∈ [1, e]`,
so the kernel is at most `(eθ)^{1/2} (v - θ)^{-1/2}`, whose integral is `2 (eθ)^{1/2} ((e-1)θ)^{1/2}
≤ 5θ` (`intervalIntegral.integral_rpow`, `intervalIntegral.intervalIntegrable_rpow'`). -/
def LogKernelIntegral : Prop :=
  ∀ θ : ℝ, 0 < θ →
    IntervalIntegrable (fun v : ℝ => (Real.log v - Real.log θ) ^ (-(1 / 2 : ℝ))) volume θ
      (Real.exp 1 * θ) ∧
    ∫ v in θ..(Real.exp 1 * θ), (Real.log v - Real.log θ) ^ (-(1 / 2 : ℝ)) ≤ 5 * θ

/-- **Leaf 3, level 0** (shorter proof lines 1086, 1127-1131): a mild solution is bounded in `X_G`
on compact subintervals of `(0, ∞)`. `X_{G,0} = ⊤` (`B0123.XGj_zero`), `xgjNorm 0 f = √2 ‖f‖`,
and `‖V s‖ = ‖S s β (V β)‖ ≤ e^{‖L₀‖(β - s)} ‖V β‖` (`Cons.G3b.norm_S_le`). -/
def MildBase : Prop :=
  ∀ V : ℝ → XG, IsMildOnPos V → MildLevel V 0

/-- **Leaf 4, strong continuity in `X_G`** (`Cons.G3b.continuousOn_S_left`): a mild solution is
continuous into `X_G` on `(0, ∞)`, since `V = S · θ' (V θ')` on `[ε, θ']`. -/
def MildContinuous : Prop :=
  ∀ V : ℝ → XG, IsMildOnPos V → ContinuousOn V (Ioi 0)

/-- **Leaf 5, continuity into `X_{G,j}` from continuity into `X_G` and bounds in `X_{G,j+1}`**
(interpolation). If `V` is continuous into `X_G` on `(0, ∞)` and `MildLevel V (j+1)`, then
`V θ ∈ X_{G,j}` and `θ ↦ (I - D)^{j/2} V θ` is continuous on `(0, ∞)` into `X_G`. Proof: for `f`
in `X_{G,j+1}`, `‖f‖²_{X_{G,j}} ≤ (1+N)^j · 2‖f‖² + (1+N)^{-1} ‖f‖²_{X_{G,j+1}}` for every `N`
(split the series `B0123.hasSum_xgjNorm_sq` at `N`); apply to `f = V θ - V θ₀` with the local
bound of `MildLevel V (j+1)` on `[θ₀/2, 2θ₀]` and `‖V θ - V θ₀‖ → 0`; finally
`‖(I-D)^{j/2} f‖ ≤ xgjNorm j f` and `(I-D)^{j/2}` is linear on its domain. -/
def XGjContinuousOfBounds : Prop :=
  ∀ (V : ℝ → XG) (j : ℕ), ContinuousOn V (Ioi 0) → MildLevel V (j + 1) →
    ∃ U : ℝ → XG,
      (∀ θ : ℝ, 0 < θ → ∃ h : V θ ∈ B0123.XGj j, B0123.IDpow ((j : ℝ) / 2) ⟨V θ, h⟩ = U θ) ∧
      ContinuousOn U (Ioi 0)

/-- **Leaf 6, the one-derivative gain** (shorter proof lines 1141-1145; old manuscript 1867-1888):
under `GreenAll`, a mild solution with `MildLevel V j` has `MildLevel V (j+1)`.

Proof. Fix `θ > 0`, `θ' = e θ`. By mildness and `CanonicalMild.S_mild_interval`,
`V θ = e^{D} V θ' + ∫ v in θ..θ', e^{(log v - log θ) D} (L₀ V v)`. The first term lies in
`X_{G,j+1}` with `‖.‖_{j+1} ≤ ‖V θ'‖_j` (`B0123.expD_smoothing`, `a = 1`). For the integrand, on
`(θ, θ')` put `a = log v - log θ ∈ (0, 1)`: `L₀ V v ∈ X_{G,j}` with
`‖L₀ V v‖_j ≤ C_L ‖V v‖_j` (`B0122.L0_mem_XGj_norm j (hE j)`, `B0123.xgjNorm_sq_eq_graphNormSq`;
`BootOps.L0_bound` in `Regularity/Bootstrap/Ops.lean` is this conversion), hence by
`B0123.expD_smoothing` the integrand is in `X_{G,j+1}` with norm `≤ C_L K a^{-1/2}`, `K` the
`MildLevel V j` bound on `[α, eβ]`. It is `X_G`-continuous on `[θ, θ']`
(`CanonicalMild.intervalIntegrable_expD_log`, `continuousOn_S_left`), so `XGjIntervalIntegralMem`
with majorant `C_L K (log v - log θ)^{-1/2}` and `LogKernelIntegral` put the integral in
`X_{G,j+1}` with norm `≤ 5 θ C_L K`. Finally the triangle inequality for `xgjNorm` (prove it if it
is not in the library: Minkowski for the weighted `ℓ²` sums `B0123.hasSum_xgjNorm_sq`) gives the
local bound `K + 5 β C_L K` on `[α, β]`. -/
def MildLevelStep : Prop :=
  GreenAll → ∀ V : ℝ → XG, IsMildOnPos V → ∀ j : ℕ, MildLevel V j → MildLevel V (j + 1)

/-- `MildLevel` at every `j` from the base and the step (induction on `j`). -/
theorem mildLevel_all {V : ℝ → XG} (hbase : MildLevel V 0)
    (hstep : ∀ j : ℕ, MildLevel V j → MildLevel V (j + 1)) : ∀ j : ℕ, MildLevel V j := by
  intro j
  induction j with
  | zero => exact hbase
  | succ j ih => exact hstep j ih

/-- **`MildSpatialSmoothing` from the four leaf statements** `MildBase`, `MildLevelStep`,
`MildContinuous`, `XGjContinuousOfBounds` (the step is itself reduced to `XGjIntervalIntegralMem`
and `LogKernelIntegral` by task `Spine:SP-CAN/4/1/6`). -/
theorem mildSpatialSmoothing_of (hBase : MildBase) (hStep : MildLevelStep)
    (hCont : MildContinuous) (hU : XGjContinuousOfBounds) : MildSpatialSmoothing := by
  intro hE V hV j
  have hall : ∀ k : ℕ, MildLevel V k :=
    mildLevel_all (hBase V hV) (fun k hk => hStep hE V hV k hk)
  exact hU V j (hCont V hV) (hall (j + 1))

end UnforcedLeray.Short.Spine
