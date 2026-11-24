import UnforcedLeray.Short.PartIIa.Sub.F03
import UnforcedLeray.Units.B0424.Calc
import UnforcedLeray.Units.B0424.Tests
import UnforcedLeray.Units.B0424.Chart

/-!
# Part II-a, task `PartII-a:F03/1`: the transformed equation `WindowEquation` (conditional)

Source of record: `the November 2 reference manuscript`, lines 1431-1434
("`v(t,x) = e^{-t/2} w(τ₀+t, e^{-t/2}x)`; `v_t - ν e^t Δ_x v` is the same pull-back of `f - μw`";
cutoff `χ`, `θ = e^t`: `(∂_θ - νΔ_x)u = θ^{-1}(χ g + χ' v)`). Old manuscript: `paper/main.tex`
lines 7479-7510 (blueprint unit B0424), whose chart/calculus infrastructure is in
`Units/B0424/{Calc,Tests,Chart}.lean` (compiled).

## Route

The equation `(μ + L₀)w = f` is a statement about phase tests (`HasPhaseOp`). Step 1 turns it into
a *local* weak identity on `ℝ × ℝ³` (`LocalIdentity`): for every smooth compactly supported
`ℂ³`-valued `Ψ`, `∫ (μΨ + L₀ᵗΨ)·W = ∫ Ψ·Fr` (periodize `Ψ`; `PeriodizedPairing`,
`RepLocInt`, `LocalIdentityOfPhaseOp`). Step 2 inserts the test `Ψ = phaseTest τ₀ Ξ e_c` with
`Ξ(t,x) = χ(t) φ(e^t, x)` (`WindowTestIdentity`, calculus of `Units/B0424/{Calc,Tests}.lean`:
`L0T_phaseTest`, `tD_timeTest`, `sLap_timeTest`, `isSTTest_timeTest`) and Step 3 changes variables
`θ = e^t`, `x = e^{t/2} y` on the two sides (`WindowChartU`, `WindowChartF`: `integral_expChart`,
`integral_dilChart` of `Units/B0424/Chart.lean`), which turns the identity into
`∫ u (-φ_θ - νΔφ) = ∫ F φ`.

Sign check: `L₀ = T₀ - νΔ - ½` (`B0411.L0T`), `(μ + L₀)w = f` gives `L₀w = f - μw`; with
`Ξ = χ(t) φ(e^t, x)`: `μΞ - Ξ_t - νe^tΔ_xΞ = (μχ - χ')φ̃ - χ e^t (φ_θ + νΔφ)~` (tilde: evaluated at
`(e^t, e^{t/2}y)`), so the local identity reads
`∫ e^{2t}χ W_c (-φ_θ - νΔφ)~ = ∫ e^t [(χ' - μχ) W_c + χ Fr_c] φ̃`, and the weights
`e^{3t/2} (dilation) · e^t (θ = e^t) · e^{-t/2}` resp. `e^{-3t/2}` turn the two sides into
`∫ u (-φ_θ - νΔφ)` and `∫ F φ` with `F = θ^{-3/2}[(χ' - μχ)W + χ f]`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.B0411 UnforcedLeray.Parabolic
  UnforcedLeray.Short.PartIIa.Rep

/-- **Representatives are locally integrable** (task `PartII-a:F03/1/1`): a jointly measurable
representative `W` of `w ∈ Y_r` (`1 ≤ r < ∞`) is locally integrable on `ℝ × ℝ³`, and its dot
product with every continuous compactly supported `ℂ³`-valued field is integrable.
Proof: `Sub/F03Rep.lean` (`lintegral_rep` with `m = 1_{[a,b]}`, `lintegral_window_lt_top`) gives
`∫⁻_{[a,b] × ℝ³} ‖W‖ₑ^r < ∞`; on the finite-measure set `[a,b] × B_R` the `L^r` norm dominates the
`L^1` norm (`eLpNorm_le_eLpNorm_mul_rpow_measure_univ` or `MemLp.mono_exponent`). -/
def RepLocInt : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → ∀ (P : ℝ) [Fact (0 < P)] (w : Yq P r)
    (W : ℝ × Space → CVec3), IsRep w W →
      LocallyIntegrable W volume ∧
        ∀ G : ℝ × Space → CVec3, Continuous G → HasCompactSupport G →
          Integrable (fun p => dotL (G p) (W p)) volume

/-- **Unfolding the pairing with a periodized test** (task `PartII-a:F03/1/2`): for a smooth test
`G` with bounded spatial support and `G(τ, ·) = 0` outside a bounded phase interval `[A, B]`,
whose dot product with the representative `W` is integrable on `ℝ × ℝ³`,
`⟨perT P G, w⟩ = P⁻¹ ∫_{ℝ × ℝ³} G · W`. Proof: `phasePair_eq_periodIntegral`
(`Lib/PhaseSpace/Pairing.lean`) for the phase test `perT P G` (`isPhaseTest_perT`,
`Lib/PhaseTrace/Periodize.lean`) gives `P⁻¹ ∫_{(0,P]} ∫ Σ_k G(t + kP, y)·w(t)(y)`; by `IsRep.slice`
and `P`-periodicity of `τ ↦ w(τ mod P)`, `w(t) = W(t + kP, ·)` a.e. for every `k`
(`AddCircle` coercion `(t + kP : AddCircle P) = (t : AddCircle P)`), and the sum over `k` together
with the integral over `(0, P]` is the integral over `ℝ` (`MeasureTheory.integral_comp_Ioc_add_...`,
`hasSum_integral_of_summable_norm`, or `lintegral_Ioc_nat_period`-style unfolding). -/
def PeriodizedPairing : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → ∀ (P : ℝ) [Fact (0 < P)] (w : Yq P r)
    (W : ℝ × Space → CVec3), IsRep w W →
      ∀ (G : ℝ × Space → CVec3) (A B : ℝ), TimeSupp A B G → IsPhaseTest 0 G →
        Integrable (fun p => dotL (G p) (W p)) volume →
          phasePair P r (perT P G) w = (P⁻¹ : ℝ) • ∫ p, dotL (G p) (W p)

/-- The **local weak identity** for representatives `W`, `Fr` of `w`, `f` with `(μ + L₀)w = f`:
`∫ (μΨ + L₀ᵗΨ)·W = ∫ Ψ·Fr` for every smooth compactly supported `ℂ³`-valued `Ψ` on `ℝ × ℝ³`. -/
def LocalIdentity (ν : ℝ) (μ : ℂ) (W Fr : ℝ × Space → CVec3) : Prop :=
  ∀ Ψ : ℝ × Space → CVec3, ContDiff ℝ ∞ Ψ → HasCompactSupport Ψ →
    ∫ p, dotL ((μ • Ψ + L0T ν Ψ) p) (W p) = ∫ p, dotL (Ψ p) (Fr p)

/-- **From `HasPhaseOp` to the local identity** (task `PartII-a:F03/1/3`, uses `RepLocInt` and
`PeriodizedPairing`): for `Ψ` smooth and compactly supported choose `A, B, R` with
`Ψ = 0` for `τ ∉ [A,B]` and for `‖y‖ > R` (`HasCompactSupport`), so `Ψ`, `G₁ = μΨ + L₀ᵗΨ` are
`IsPhaseTest 0` with `TimeSupp A B` (`timeSupp_L0T`, `B0411.isPhaseTest_L0T`); `perT P Ψ` is a phase
test (`isPhaseTest_perT`); `L0T ν (perT P Ψ) = perT P (L0T ν Ψ)` (`B0424.L0T_perT`), `perT` is
additive and `ℂ`-homogeneous (`perT_eq_sum` with a common index set), so
`μ • perT P Ψ + L0T ν (perT P Ψ) = perT P G₁`. Apply `HasPhaseOp` to `perT P Ψ`, both sides with
`PeriodizedPairing` (integrability from `RepLocInt` for the continuous compactly supported `Ψ`,
`G₁`), and cancel `P⁻¹ ≠ 0`. -/
def LocalIdentityOfPhaseOp : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ) (μ : ℂ) (f w : Yq P r),
    HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) w f →
      ∀ W Fr : ℝ × Space → CVec3, IsRep w W → IsRep f Fr → LocalIdentity ν μ W Fr

/-- **Change of variables on the left side** (task `PartII-a:F03/1/4`, unconditional): for every
measurable-or-not `W` and every `ζ`, with `θ = e^t`, `x = e^{t/2} y`,
`∫ windowField · ζ = ∫ e^{2t} χ(t) W_c(τ₀ + t, y) ζ(e^t, e^{t/2} y) dt dy`.
Proof: `windowField = 0` for `θ ≤ 0`; `B0424.integral_expChart` (weight `e^t`, `log e^t = t`), then
`B0424.integral_dilChart` (weight `e^{3t/2}`); total weight `e^{3t/2} e^t e^{-t/2} = e^{2t}`, and
`e^{-t/2} • e^{t/2} • y = y`. -/
def WindowChartU : Prop :=
  ∀ (χ : ℝ → ℝ) (τ₀ : ℝ) (W : ℝ × Space → CVec3) (c : Fin 3) (ζ : PS 3 → ℝ),
    ∫ X, windowField χ τ₀ W c X * (ζ X : ℂ) =
      ∫ p : ℝ × Space, ((Real.exp (2 * p.1) * χ p.1 : ℝ) : ℂ) * W (τ₀ + p.1, p.2) c *
        (ζ (Real.exp p.1, Real.exp (p.1 / 2) • p.2) : ℂ)

/-- **Change of variables on the right side** (task `PartII-a:F03/1/5`, unconditional):
`∫ windowForce · φ = ∫ e^t [(χ'(t) - μχ(t)) W_c + χ(t) Fr_c](τ₀ + t, y) φ(e^t, e^{t/2} y) dt dy`
(total weight `e^{3t/2} · e^t · e^{-3t/2} = e^t`; same proof as `WindowChartU`). -/
def WindowChartF : Prop :=
  ∀ (μ : ℂ) (χ : ℝ → ℝ) (τ₀ : ℝ) (W Fr : ℝ × Space → CVec3) (c : Fin 3) (φ : PS 3 → ℝ),
    ∫ X, windowForce μ χ τ₀ W Fr c X * (φ X : ℂ) =
      ∫ p : ℝ × Space, ((Real.exp p.1 : ℝ) : ℂ) *
        ((((deriv χ p.1 : ℝ) : ℂ) - μ * (χ p.1 : ℂ)) * W (τ₀ + p.1, p.2) c +
          (χ p.1 : ℂ) * Fr (τ₀ + p.1, p.2) c) *
        (φ (Real.exp p.1, Real.exp (p.1 / 2) • p.2) : ℂ)

/-- **The local identity at the pulled-back test** (task `PartII-a:F03/1/6`; calculus of
`Units/B0424/{Calc,Tests}.lean`): if `W`, `Fr` satisfy `LocalIdentity ν μ` and have integrable dot
products against continuous compactly supported fields, then for a real `ST` test `φ`, the cutoff
`χ` and a component `c`,
`∫ e^{2t}χ(t) W_c(τ₀+t,y) (-φ_θ - νΔφ)(e^t, e^{t/2}y)
   = ∫ e^t [(χ' - μχ) W_c + χ Fr_c](τ₀+t,y) φ(e^t, e^{t/2}y)`.
Proof: `Ξ = B0424.timeTest χ φ` (`Ξ(t,x) = χ(t)φ(e^t,x)`, `isSTTest_timeTest`, `tD_timeTest`,
`sLap_timeTest`); `Ψ = B0424.phaseTest τ₀ Ξ e_c` is smooth with compact support
(`phaseTest_supp`, `contDiff_phaseScal`) and `L0T_phaseTest` gives
`(μΨ + L0TΨ)(τ₀+t, y) = e^t[(μχ - χ')φ̃ - e^tχ(φ_θ + νΔφ)~] e_c`; apply `LocalIdentity` to `Ψ`,
`dotL (s • e_c) (W p) = s * W p c`, split the integral of the difference
(integrability: the two scalar coefficients are continuous with compact support, so
`s • e_c` is a continuous compactly supported field) and rearrange. -/
def WindowTestIdentity : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (W Fr : ℝ × Space → CVec3),
    (∀ G : ℝ × Space → CVec3, Continuous G → HasCompactSupport G →
      Integrable (fun p => dotL (G p) (W p)) volume) →
    (∀ G : ℝ × Space → CVec3, Continuous G → HasCompactSupport G →
      Integrable (fun p => dotL (G p) (Fr p)) volume) →
    LocalIdentity ν μ W Fr →
    ∀ χ : ℝ → ℝ, WindowCutoff χ → ∀ (τ₀ : ℝ) (c : Fin 3) (φ : PS 3 → ℝ), IsSTTest φ →
      ∫ p : ℝ × Space, ((Real.exp (2 * p.1) * χ p.1 : ℝ) : ℂ) * W (τ₀ + p.1, p.2) c *
          ((-tD φ (Real.exp p.1, Real.exp (p.1 / 2) • p.2) -
            ν * sLap φ (Real.exp p.1, Real.exp (p.1 / 2) • p.2) : ℝ) : ℂ) =
        ∫ p : ℝ × Space, ((Real.exp p.1 : ℝ) : ℂ) *
          ((((deriv χ p.1 : ℝ) : ℂ) - μ * (χ p.1 : ℂ)) * W (τ₀ + p.1, p.2) c +
            (χ p.1 : ℂ) * Fr (τ₀ + p.1, p.2) c) *
          (φ (Real.exp p.1, Real.exp (p.1 / 2) • p.2) : ℂ)

/-- **`PartII-a:F03/1`, conditional on the five leaves**: the transformed equation
`(∂_θ - νΔ_x) u_c = F_c` weakly on `ℝ × ℝ³`. (`PeriodizedPairing` enters only through
`LocalIdentityOfPhaseOp`.) -/
theorem windowEquation_of (hrep : RepLocInt) (h3 : LocalIdentityOfPhaseOp)
    (hU : WindowChartU) (hF : WindowChartF) (hT : WindowTestIdentity) : WindowEquation := by
  intro r _ hr P _ ν μ f w hw W Fr hW hFr χ hχ τ₀ c φ hφ
  have hI := h3 r hr P ν μ f w hw W Fr hW hFr
  obtain ⟨_, hWi⟩ := hrep r hr P w W hW
  obtain ⟨_, hFi⟩ := hrep r hr P f Fr hFr
  rw [hU χ τ₀ W c (fun X => -tD φ X - ν * sLap φ X), hF μ χ τ₀ W Fr c φ]
  exact hT ν μ W Fr hWi hFi hI χ hχ τ₀ c φ hφ

end UnforcedLeray.Short.PartIIa
