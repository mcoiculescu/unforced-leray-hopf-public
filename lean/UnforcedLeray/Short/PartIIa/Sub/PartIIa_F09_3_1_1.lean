import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_3_1
import UnforcedLeray.Short.PartIIa.Sub.F03_1

/-!
# Part II-a, task `PartII-a:F09/3/1/1`: the transformed adjoint equation (conditional)

Source `the November 2 reference manuscript`
lines 1426-1442 (time reversal `t = τ₀ - τ`, `θ = 1 - e^{-t}`, `x = e^{-t/2} y`; `L^* = -𝒯 - νΔ + 1`).
Analogue of `Sub/F03_1.lean` (`windowEquation_of`).

## Route (and the checked computation)

`HasPhaseOp (μ̄ + L₀) w f` gives, by periodization (`RepLocInt`, `PeriodizedPairing` of
`Sub/F03_1.lean` are reused verbatim), the local identity `AdjLocalIdentity`:
`∫ (μ̄Ψ + L₀Ψ)·W = ∫ Ψ·Fr` for smooth compactly supported `Ψ`.  Take
`Ψ(τ,y) = e^{-3t/2} χ(t) φ(1 - e^{-t}, e^{-t/2} y) e_c`, `t = τ₀ - τ` (`adjTest`).  With `θ = 1-e^{-t}`,
`x = e^{-t/2}y` (tilde = evaluated at `(θ,x)`) one has `∂_τ Ψ = -∂_t Ψ`, `y·∇_yΨ = χ (x·∇φ)~`,
`Δ_yΨ = e^{-t} χ (Δφ)~`, and `L₀ = ∂_τ - ½ y·∇ - νΔ - ½`, hence
`(μ̄ + L₀)Ψ = e^{-3t/2} {[(μ̄+1)χ - χ'] φ~ - e^{-t} χ (φ_θ + νΔφ)~} e_c`   (`AdjTestCalc`).
So the local identity reads
`∫ e^{-5t/2} χ W_c(τ₀-t,y) (-φ_θ - νΔφ)~ = ∫ e^{-3t/2} [(χ' - (1+μ̄)χ) W_c + χ Fr_c](τ₀-t,y) φ~`
(`AdjWindowTestIdentity`), and the two charts `(t,y) ↦ (1 - e^{-t}, e^{-t/2} y)`, with Jacobian
`e^{-t}·e^{-3t/2} = e^{-5t/2}`, turn the sides into `∫ u (-φ_θ - νΔφ)` and `∫ F φ`
(`AdjWindowChartU`, `AdjWindowChartF`; note `adjWindowField` at `(1-e^{-t}, e^{-t/2}y)` is
`χ(t) W(τ₀-t, y)` and `adjWindowForce` is `e^{t}[...]`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.B0411 UnforcedLeray.Parabolic
  UnforcedLeray.Short.PartIIa.Rep

/-- The local weak identity for `(μ̄ + L₀) w = f`:
`∫ (μ̄Ψ + L₀Ψ)·W = ∫ Ψ·Fr` for every smooth compactly supported `ℂ³`-valued `Ψ`. -/
def AdjLocalIdentity (ν : ℝ) (μ : ℂ) (W Fr : ℝ × Space → CVec3) : Prop :=
  ∀ Ψ : ℝ × Space → CVec3, ContDiff ℝ ∞ Ψ → HasCompactSupport Ψ →
    ∫ p, dotL (((starRingEnd ℂ) μ • Ψ + L0 ν Ψ) p) (W p) = ∫ p, dotL (Ψ p) (Fr p)

/-- **From `HasPhaseOp` to the local identity** (analogue of `LocalIdentityOfPhaseOp`; periodize
`Ψ` with `perT`, use `PeriodizedPairing`, `RepLocInt`; needs `L0 ν (perT P Ψ) = perT P (L0 ν Ψ)`,
the `L0` analogue of `B0424.L0T_perT`). -/
def AdjLocalIdentityOfPhaseOp : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ) (μ : ℂ) (f w : Yq P r),
    HasPhaseOp (fun Φ => (starRingEnd ℂ) μ • Φ + L0 ν Φ) w f →
      ∀ W Fr : ℝ × Space → CVec3, IsRep w W → IsRep f Fr → AdjLocalIdentity ν μ W Fr

/-- **Left change of variables** (unconditional): with `θ = 1 - e^{-t}`, `x = e^{-t/2} y`,
`∫ adjWindowField · ζ = ∫ e^{-5t/2} χ(t) W_c(τ₀ - t, y) ζ(1 - e^{-t}, e^{-t/2} y) dt dy`. -/
def AdjWindowChartU : Prop :=
  ∀ (χ : ℝ → ℝ) (τ₀ : ℝ) (W : ℝ × Space → CVec3) (c : Fin 3) (ζ : PS 3 → ℝ),
    ∫ X, adjWindowField χ τ₀ W c X * (ζ X : ℂ) =
      ∫ p : ℝ × Space, ((Real.exp (-(5 * p.1 / 2)) * χ p.1 : ℝ) : ℂ) * W (τ₀ - p.1, p.2) c *
        (ζ (1 - Real.exp (-p.1), Real.exp (-p.1 / 2) • p.2) : ℂ)

/-- **Right change of variables** (unconditional):
`∫ adjWindowForce · φ = ∫ e^{-3t/2} [(χ'(t) - (1+μ̄)χ(t)) W_c + χ(t) Fr_c](τ₀ - t, y)
  φ(1 - e^{-t}, e^{-t/2} y) dt dy` (weights `e^{-5t/2} · e^{t}`). -/
def AdjWindowChartF : Prop :=
  ∀ (μ : ℂ) (χ : ℝ → ℝ) (τ₀ : ℝ) (W Fr : ℝ × Space → CVec3) (c : Fin 3) (φ : PS 3 → ℝ),
    ∫ X, adjWindowForce μ χ τ₀ W Fr c X * (φ X : ℂ) =
      ∫ p : ℝ × Space, ((Real.exp (-(3 * p.1 / 2)) : ℝ) : ℂ) *
        ((((deriv χ p.1 : ℝ) : ℂ) - (1 + (starRingEnd ℂ) μ) * (χ p.1 : ℂ)) *
            W (τ₀ - p.1, p.2) c + (χ p.1 : ℂ) * Fr (τ₀ - p.1, p.2) c) *
          (φ (1 - Real.exp (-p.1), Real.exp (-p.1 / 2) • p.2) : ℂ)

/-- The pulled-back test `Ψ(τ,y) = e^{-3t/2} χ(t) φ(1 - e^{-t}, e^{-t/2} y) e_c`, `t = τ₀ - τ`. -/
def adjTest (χ : ℝ → ℝ) (τ₀ : ℝ) (φ : PS 3 → ℝ) (c : Fin 3) : ℝ × Space → CVec3 :=
  fun p => ((Real.exp (-(3 * (τ₀ - p.1) / 2)) * χ (τ₀ - p.1) *
    φ (1 - Real.exp (-(τ₀ - p.1)), Real.exp (-(τ₀ - p.1) / 2) • p.2) : ℝ) : ℂ) •
      EuclideanSpace.single c (1 : ℂ)

/-- `adjTest` is smooth with compact support for a cutoff `χ` and an `ST` test `φ`. -/
def AdjTestSmooth : Prop :=
  ∀ (χ : ℝ → ℝ), WindowCutoff χ → ∀ (τ₀ : ℝ) (φ : PS 3 → ℝ), IsSTTest φ → ∀ c : Fin 3,
    ContDiff ℝ ∞ (adjTest χ τ₀ φ c) ∧ HasCompactSupport (adjTest χ τ₀ φ c)

/-- **The adjoint calculus** (checked computation in the header): for smooth `χ`, smooth `φ`,
`(μ̄ + L₀)(adjTest) (τ,y) = s • e_c` with, `t = τ₀ - τ`,
`s = e^{-3t/2} {[(μ̄+1)χ(t) - χ'(t)] φ~ - e^{-t} χ(t) (tD φ + ν sLap φ)~}`, `~` at
`(1 - e^{-t}, e^{-t/2} y)`. -/
def AdjTestCalc : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (χ : ℝ → ℝ), WindowCutoff χ → ∀ (τ₀ : ℝ) (φ : PS 3 → ℝ), IsSTTest φ →
    ∀ (c : Fin 3) (p : ℝ × Space),
      ((starRingEnd ℂ) μ • adjTest χ τ₀ φ c + L0 ν (adjTest χ τ₀ φ c)) p =
        (((Real.exp (-(3 * (τ₀ - p.1) / 2)) : ℝ) : ℂ) *
          ((((starRingEnd ℂ) μ + 1) * (χ (τ₀ - p.1) : ℂ) - ((deriv χ (τ₀ - p.1) : ℝ) : ℂ)) *
              (φ (1 - Real.exp (-(τ₀ - p.1)), Real.exp (-(τ₀ - p.1) / 2) • p.2) : ℂ) -
            ((Real.exp (-(τ₀ - p.1)) * χ (τ₀ - p.1) *
              (tD φ (1 - Real.exp (-(τ₀ - p.1)), Real.exp (-(τ₀ - p.1) / 2) • p.2) +
                ν * sLap φ (1 - Real.exp (-(τ₀ - p.1)), Real.exp (-(τ₀ - p.1) / 2) • p.2)) : ℝ) :
              ℂ))) • EuclideanSpace.single c (1 : ℂ)

/-- **The local identity at the pulled-back test**: from `AdjLocalIdentity`, `AdjTestSmooth`,
`AdjTestCalc` (reflect `τ = τ₀ - t`; `dotL (s • e_c) (W p) = s * W p c`). -/
def AdjWindowTestIdentity : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (W Fr : ℝ × Space → CVec3),
    (∀ G : ℝ × Space → CVec3, Continuous G → HasCompactSupport G →
      Integrable (fun p => dotL (G p) (W p)) volume) →
    (∀ G : ℝ × Space → CVec3, Continuous G → HasCompactSupport G →
      Integrable (fun p => dotL (G p) (Fr p)) volume) →
    AdjLocalIdentity ν μ W Fr →
    ∀ χ : ℝ → ℝ, WindowCutoff χ → ∀ (τ₀ : ℝ) (c : Fin 3) (φ : PS 3 → ℝ), IsSTTest φ →
      ∫ p : ℝ × Space, ((Real.exp (-(5 * p.1 / 2)) * χ p.1 : ℝ) : ℂ) * W (τ₀ - p.1, p.2) c *
          ((-tD φ (1 - Real.exp (-p.1), Real.exp (-p.1 / 2) • p.2) -
            ν * sLap φ (1 - Real.exp (-p.1), Real.exp (-p.1 / 2) • p.2) : ℝ) : ℂ) =
        ∫ p : ℝ × Space, ((Real.exp (-(3 * p.1 / 2)) : ℝ) : ℂ) *
          ((((deriv χ p.1 : ℝ) : ℂ) - (1 + (starRingEnd ℂ) μ) * (χ p.1 : ℂ)) *
              W (τ₀ - p.1, p.2) c + (χ p.1 : ℂ) * Fr (τ₀ - p.1, p.2) c) *
            (φ (1 - Real.exp (-p.1), Real.exp (-p.1 / 2) • p.2) : ℂ)

/-- **`PartII-a:F09/3/1/1`, conditional on its leaves**: the transformed adjoint equation. -/
theorem adjointWindowEquation_of (hrep : RepLocInt) (h3 : AdjLocalIdentityOfPhaseOp)
    (hU : AdjWindowChartU) (hF : AdjWindowChartF) (hT : AdjWindowTestIdentity) :
    AdjointWindowEquation := by
  intro r _ hr P _ ν μ f w hw W Fr hW hFr χ hχ τ₀ c φ hφ
  have hI := h3 r hr P ν μ f w hw W Fr hW hFr
  obtain ⟨_, hWi⟩ := hrep r hr P w W hW
  obtain ⟨_, hFi⟩ := hrep r hr P f Fr hFr
  rw [hU χ τ₀ W c (fun X => -tD φ X - ν * sLap φ X), hF μ χ τ₀ W Fr c φ]
  exact hT ν μ W Fr hWi hFi hI χ hχ τ₀ c φ hφ

end UnforcedLeray.Short.PartIIa
