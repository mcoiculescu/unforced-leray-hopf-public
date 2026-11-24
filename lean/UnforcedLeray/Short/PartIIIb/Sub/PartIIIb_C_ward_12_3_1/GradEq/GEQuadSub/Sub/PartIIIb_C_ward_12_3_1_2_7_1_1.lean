import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Defs

/-!
# Spatial mollification commutes with the weak `y_j`-derivative (decomposition)

Source `the November 2 reference manuscript`
lines 2562-2564 (local Friedrichs argument in `y`), phase tests 2525-2531.

NOTE on the target: the task statement had `hρ : ContDiff ℝ ⊤ ρ`; in this Mathlib `⊤ : WithTop ℕ∞`
is `ω` (analytic), so a compactly supported such `ρ` is `0` and the statement is vacuous.  The
intended hypothesis is `ContDiff ℝ ∞ ρ` (smooth); everything here uses `∞`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open UnforcedLeray.Cons.C03.Concrete (phaseInt)
open scoped ContDiff

/-- Convolution in `y` only: `(spatMol ρ f)(τ, y) = ∫ ρ(y') f(τ, y - y') dy'`. -/
def spatMol (ρ : UnforcedLeray.Space → ℝ) (f : ℝ × UnforcedLeray.Space → ℂ) :
    ℝ × UnforcedLeray.Space → ℂ :=
  fun x => ∫ y', (ρ y' : ℂ) * f (x.1, x.2 - y')

/-- The adjoint-mollified test `ψ(τ,z) = ∫ ρ(y') φ(τ, z + y') dy'`. -/
def mollTest (ρ : UnforcedLeray.Space → ℝ) (φ : ℝ × UnforcedLeray.Space → ℂ) :
    ℝ × UnforcedLeray.Space → ℂ :=
  fun x => ∫ y', (ρ y' : ℂ) * φ (x.1, x.2 + y')

/-- Lemma A: `mollTest ρ φ` is `C^∞` on `ℝ × ℝ³` (`ρ` smooth with compact support, `φ` a phase
test; `φ` has `y`-compact support and is smooth, so the integrand is smooth with locally uniform
compact support and one differentiates under the integral). -/
def MollTestSmooth : Prop :=
  ∀ (P : ℝ) (ρ : UnforcedLeray.Space → ℝ), ContDiff ℝ ∞ ρ → HasCompactSupport ρ →
    ∀ φ : ℝ × UnforcedLeray.Space → ℂ, IsPhaseTest P φ → ContDiff ℝ ∞ (mollTest ρ φ)

/-- Lemma B: `mollTest ρ φ` is `P`-periodic in `τ` and vanishes for `‖z‖` beyond some radius
(radius of `φ` plus radius of the support of `ρ`). -/
def MollTestPerSupp : Prop :=
  ∀ (P : ℝ) (ρ : UnforcedLeray.Space → ℝ), HasCompactSupport ρ →
    ∀ φ : ℝ × UnforcedLeray.Space → ℂ, IsPhaseTest P φ →
      (∀ τ y, mollTest ρ φ (τ + P, y) = mollTest ρ φ (τ, y)) ∧
      ∃ R, ∀ τ y, R < ‖y‖ → mollTest ρ φ (τ, y) = 0

/-- Lemma C: `∂_{y_j}` commutes with `mollTest` (differentiation under the integral, `φ`
smooth with `y`-compact support, `ρ` compactly supported and continuous). -/
def MollTestDy : Prop :=
  ∀ (P : ℝ) (j : Fin 3) (ρ : UnforcedLeray.Space → ℝ), ContDiff ℝ ∞ ρ → HasCompactSupport ρ →
    ∀ φ : ℝ × UnforcedLeray.Space → ℂ, IsPhaseTest P φ →
      dy j (mollTest ρ φ) = mollTest ρ (dy j φ)

/-- Lemma D (Fubini + translation in `y`):
`⟨φ, ρ * f⟩ = ⟨mollTest ρ φ, f⟩` on the phase cell, for `f ∈ L^1_loc` (source 2562-2564). -/
def MollFubini : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ρ : UnforcedLeray.Space → ℝ), ContDiff ℝ ∞ ρ → HasCompactSupport ρ →
    ∀ f : ℝ × UnforcedLeray.Space → ℂ, MemLpLoc P f 1 →
      ∀ φ : ℝ × UnforcedLeray.Space → ℂ, IsPhaseTest P φ →
        phaseInt P (fun x => φ x * spatMol ρ f x) = phaseInt P (fun x => mollTest ρ φ x * f x)

theorem weakDyS_spatMol_of (hA : MollTestSmooth) (hB : MollTestPerSupp) (hC : MollTestDy)
    (hD : MollFubini) (P : ℝ) [Fact (0 < P)] (j : Fin 3) (ρ : UnforcedLeray.Space → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ) (f Df : ℝ × UnforcedLeray.Space → ℂ)
    (hf : MemLpLoc P f 1) (hDf : MemLpLoc P Df 1) (h : WeakDyS P j f Df) :
    WeakDyS P j (spatMol ρ f) (spatMol ρ Df) := by
  intro φ hφ
  have hψ : IsPhaseTest P (mollTest ρ φ) :=
    ⟨hA P ρ hρ hc φ hφ, (hB P ρ hc φ hφ).1, (hB P ρ hc φ hφ).2⟩
  have h1 := hD P ρ hρ hc f hf (dy j φ) (hφ.dy j)
  have h2 := hD P ρ hρ hc Df hDf φ hφ
  have h3 := h (mollTest ρ φ) hψ
  rw [h1, ← hC P j ρ hρ hc φ hφ, h3, h2]

end UnforcedLeray.Short.PartIIIb.Concrete
