import UnforcedLeray.Lib.AxisymmetricB.Lift
import UnforcedLeray.Lib.AxisymmetricB.Bridge
import UnforcedLeray.Units.B0412.Action
import UnforcedLeray.Lib.PhaseSpace.Ops

/-!
# `NvShellJets`: the calculus leaves (shell jets of the ring lift)

Source `the November 2 reference manuscript`
lines 2545-2549 (on `ϱ < R` the inlet field has arbitrary axial decay; fixed derivative orders)
and 1206-1222 (the ring chart `s = R²/ϱ²`, `η = R z/ϱ`, the log-radius phase, and the lift
`u = (R/ϱ) (v₁ e_r + v₂ e_z)`).

On the shell `ρ₀ ≤ ϱ(y) ≤ R₀` the ring lift is `Nv R b τ y = frameFac R y (b (chart R τ y))`
with the frame factor `frameFac R y = √(age R y) • frameL y : Merid →L[ℝ] Space`.  The jets of
`Nv R b τ` are bounded by Leibniz (frame factor × `b ∘ chart`) and Faà di Bruno
(`b ∘ chart`); the leaves below are the calculus facts this needs:

* `ShellInvBound`: a function smooth off the axis and invariant under `y ↦ y + t e₃` has
  bounded jets on the shell (compactness of `{ρ₀ ≤ ϱ ≤ R₀, y₃ = 0}` and translation);
* `ShellFrameJets`, `ShellAgeJets`, `ShellPhaseJets`: the frame factor, `s = R²/ϱ²` and the
  phase `ξ = Rτ/2 − (R/2) log s` have bounded jets on the shell (for `ξ`, derivatives of order
  `≥ 1`, uniformly in `τ`);
* `ShellTransJets`: `η = R y₃/ϱ` has jets `≤ C (1 + |y₃|)` on the shell;
* `ShellAbsorb`: `(1+|t|)^m e^{-a|t|} ≤ C_N (1+|t|)^{-N}`;
* `ShellDτ`: `∂_τ (realC ∘ Nv R b) = realC (Nv R ((R/2) ∂_ξ b))` off the axis (`∂_τ = (R/2)∂_ξ`).
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.Shell

open UnforcedLeray.Axi

/-- The frame factor `y ↦ √s(y) (v ↦ v_r e_r(y) + v_z e_z)` of the ring lift (source 1214-1216:
`u_r = (R/ϱ) v₁`, `u_z = (R/ϱ) v₂`; `√s = R/ϱ`). -/
def frameFac (R : ℝ) (y : UnforcedLeray.Space) : Merid →L[ℝ] UnforcedLeray.Space :=
  √(age R y) • frameL y

theorem Nv_eq_frameFac (R : ℝ) (b : ℝ × (ℝ × ℝ) → Merid) (τ : ℝ) (y : UnforcedLeray.Space) :
    Nv R b τ y = frameFac R y (b (chart R τ y)) := rfl

/-- **Leaf (compactness on the shell; source 2545-2549, 1206-1222).**  A function `f` that is
`C^∞` off the axis and invariant under axial translations `y ↦ y + t e₃` has, for every `n`,
jets of order `≤ n` bounded on the shell `ρ₀ ≤ ϱ ≤ R₀` (`ρ₀ > 0`): the slice
`{ρ₀ ≤ ϱ ≤ R₀, y₃ = 0}` is compact and avoids the axis, and `D^i f(y) = D^i f(y − y₃ e₃)`. -/
def ShellInvBound : Prop :=
  ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (f : UnforcedLeray.Space → F),
    ContDiffOn ℝ ∞ f axisᶜ → (∀ (x : UnforcedLeray.Space) (t : ℝ), f (x + t • e3) = f x) →
    ∀ (n : ℕ) (ρ0 R0 : ℝ), 0 < ρ0 → ∃ C : ℝ, ∀ y : UnforcedLeray.Space, ρ0 ≤ ϱ y → ϱ y ≤ R0 →
      ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i f y‖ ≤ C

/-- **Leaf (frame factor; source 1214-1216, 2545-2549).**  The jets of the frame factor
`√s · frameL` are bounded on the shell. -/
def ShellFrameJets : Prop :=
  ∀ (R ρ0 R0 : ℝ) (n : ℕ), 0 < R → 0 < ρ0 → ∃ C : ℝ, ∀ y : UnforcedLeray.Space,
    ρ0 ≤ ϱ y → ϱ y ≤ R0 → ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i (frameFac R) y‖ ≤ C

/-- **Leaf (age; source 1209, 2545-2549).**  The jets of `s = R²/ϱ²` are bounded on the shell. -/
def ShellAgeJets : Prop :=
  ∀ (R ρ0 R0 : ℝ) (n : ℕ), 0 < R → 0 < ρ0 → ∃ C : ℝ, ∀ y : UnforcedLeray.Space,
    ρ0 ≤ ϱ y → ϱ y ≤ R0 → ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i (age R) y‖ ≤ C

/-- **Leaf (phase; source 1209, 2545-2549).**  The derivatives of order `1..n` of the phase
`ξ = Rτ/2 − (R/2) log s` are bounded on the shell, uniformly in `τ` (they do not see `τ`). -/
def ShellPhaseJets : Prop :=
  ∀ (R ρ0 R0 : ℝ) (n : ℕ), 0 < R → 0 < ρ0 → ∃ C : ℝ, ∀ (τ : ℝ) (y : UnforcedLeray.Space),
    ρ0 ≤ ϱ y → ϱ y ≤ R0 → ∀ i : ℕ, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i (phase R τ) y‖ ≤ C

/-- **Leaf (transverse coordinate; source 1209, 2545-2549).**  The jets of `η = R y₃/ϱ` are
`≤ C (1 + |y₃|)` on the shell (`η = (R y₃) · ϱ⁻¹`, Leibniz; `ϱ⁻¹` has bounded jets). -/
def ShellTransJets : Prop :=
  ∀ (R ρ0 R0 : ℝ) (n : ℕ), 0 < R → 0 < ρ0 → ∃ C : ℝ, ∀ y : UnforcedLeray.Space,
    ρ0 ≤ ϱ y → ϱ y ≤ R0 → ∀ i : ℕ, i ≤ n →
      ‖iteratedFDeriv ℝ i (Axi.trans R) y‖ ≤ C * (1 + |y 2|)

/-- **Leaf (absorption; source 2545-2549, arbitrary axial decay).**  Polynomial factors are
absorbed by the exponential decay: `(1+|t|)^m e^{-a|t|} ≤ C (1+|t|)^{-N}`. -/
def ShellAbsorb : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ m N : ℕ, ∃ C : ℝ, ∀ t : ℝ,
    (1 + |t|) ^ m * Real.exp (-(a * |t|)) ≤ C * (1 + |t|) ^ (-(N : ℝ))

/-- **Leaf (phase-time derivative; source 1206-1222: `ξ` is affine in the phase time with slope
`R/2`).**  Off the axis, `∂_τ realC (Nv R b τ x) = realC (Nv R ((R/2) ∂_ξ b) τ x)`. -/
def ShellDτ : Prop :=
  ∀ (R : ℝ) (b : ℝ × (ℝ × ℝ) → Merid), 0 < R → ContDiff ℝ ∞ b →
    ∀ (τ : ℝ) (x : UnforcedLeray.Space), x ∉ axis →
      UnforcedLeray.PhaseSpace.dτ
          (fun q : ℝ × UnforcedLeray.Space => UnforcedLeray.B0412.realC (Nv R b q.1 q.2)) (τ, x) =
        UnforcedLeray.B0412.realC (Nv R (fun m => (R / 2) • dQ b m) τ x)

end UnforcedLeray.Short.PartIIIb.Concrete.Shell
