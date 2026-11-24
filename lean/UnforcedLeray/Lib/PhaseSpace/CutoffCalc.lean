import UnforcedLeray.Lib.PhaseSpace.Ops
import UnforcedLeray.Lib.PhaseSpace.Multiplier

/-!
# Product rules for spatial multipliers of phase functions (helper for INF25 T25.3)

For a smooth scalar `a : ℝ³ → ℝ` and a smooth phase function `Ψ`, the transposed operators
of `Ops.lean` applied to `a Ψ` (`mulT a Ψ`) are

* `∂_τ (aΨ) = a ∂_τ Ψ`,
* `∂ⱼ (aΨ) = a ∂ⱼΨ + (∂ⱼa) Ψ`,
* `Δ (aΨ) = a ΔΨ + 2 ∑ⱼ (∂ⱼa) ∂ⱼΨ + (Δa) Ψ`,
* `T₀ᵗ (aΨ) = a T₀ᵗΨ + ½ (y·∇a) Ψ`.

These are the commutator identities of the cutoff argument of T25.3 (scoping note
INF15-INF17-INF25 §5).

Status: infrastructure only.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.PhaseSpace

/-- The spatial derivative `∂ⱼ a` of a scalar function on `ℝ³`. -/
def sd (j : Fin 3) (a : Space → ℝ) : Space → ℝ := fun y => fderiv ℝ a y (coordinateVector j)

/-- `y·∇a`. -/
def radS (a : Space → ℝ) : Space → ℝ := fun y => ∑ j : Fin 3, y j * sd j a y

/-- `Δa`. -/
def lapS (a : Space → ℝ) : Space → ℝ := fun y => ∑ j : Fin 3, sd j (sd j a) y

theorem contDiff_sd {a : Space → ℝ} (ha : ContDiff ℝ ∞ a) (j : Fin 3) :
    ContDiff ℝ ∞ (sd j a) :=
  (ha.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem contDiff_mulT {a : Space → ℝ} (ha : ContDiff ℝ ∞ a) {Ψ : ℝ × Space → CVec3}
    (hΨ : ContDiff ℝ ∞ Ψ) : ContDiff ℝ ∞ (mulT a Ψ) :=
  (ha.comp contDiff_snd).smul hΨ

theorem contDiff_dy {Ψ : ℝ × Space → CVec3} (hΨ : ContDiff ℝ ∞ Ψ) (j : Fin 3) :
    ContDiff ℝ ∞ (dy j Ψ) :=
  (hΨ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem contDiff_dτ {Ψ : ℝ × Space → CVec3} (hΨ : ContDiff ℝ ∞ Ψ) : ContDiff ℝ ∞ (dτ Ψ) :=
  (hΨ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem fderiv_mulT_apply {a : Space → ℝ} (ha : Differentiable ℝ a) {Ψ : ℝ × Space → CVec3}
    (hΨ : Differentiable ℝ Ψ) (p v : ℝ × Space) :
    fderiv ℝ (mulT a Ψ) p v = a p.2 • fderiv ℝ Ψ p v + (fderiv ℝ a p.2 v.2) • Ψ p := by
  have h1 : HasFDerivAt (fun p : ℝ × Space => a p.2)
      ((fderiv ℝ a p.2).comp (ContinuousLinearMap.snd ℝ ℝ Space)) p :=
    (ha p.2).hasFDerivAt.comp p hasFDerivAt_snd
  have h2 := h1.smul (hΨ p).hasFDerivAt
  rw [show mulT a Ψ = (fun p : ℝ × Space => a p.2) • Ψ from rfl, h2.fderiv]
  simp

theorem dτ_mulT {a : Space → ℝ} (ha : Differentiable ℝ a) {Ψ : ℝ × Space → CVec3}
    (hΨ : Differentiable ℝ Ψ) : dτ (mulT a Ψ) = mulT a (dτ Ψ) := by
  funext p
  simp [dτ, mulT, fderiv_mulT_apply ha hΨ]

theorem dy_mulT {a : Space → ℝ} (ha : Differentiable ℝ a) {Ψ : ℝ × Space → CVec3}
    (hΨ : Differentiable ℝ Ψ) (j : Fin 3) :
    dy j (mulT a Ψ) = mulT a (dy j Ψ) + mulT (sd j a) Ψ := by
  funext p
  simp [dy, mulT, sd, fderiv_mulT_apply ha hΨ]

theorem dy_add {F G : ℝ × Space → CVec3} (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    (j : Fin 3) : dy j (F + G) = dy j F + dy j G := by
  funext p
  simp [dy, fderiv_add (hF p) (hG p)]

theorem lapT_mulT_apply {a : Space → ℝ} (ha : ContDiff ℝ ∞ a) {Ψ : ℝ × Space → CVec3}
    (hΨ : ContDiff ℝ ∞ Ψ) (p : ℝ × Space) :
    lapT (mulT a Ψ) p = a p.2 • lapT Ψ p + ∑ j : Fin 3, (2 * sd j a p.2) • dy j Ψ p +
      lapS a p.2 • Ψ p := by
  have hd : ∀ {b : Space → ℝ}, ContDiff ℝ ∞ b → Differentiable ℝ b :=
    fun hb => hb.differentiable (by simp)
  have hD : ∀ {G : ℝ × Space → CVec3}, ContDiff ℝ ∞ G → Differentiable ℝ G :=
    fun hG => hG.differentiable (by simp)
  have hj : ∀ j : Fin 3, dy j (dy j (mulT a Ψ)) =
      mulT a (dy j (dy j Ψ)) + mulT (sd j a) (dy j Ψ) +
        (mulT (sd j a) (dy j Ψ) + mulT (sd j (sd j a)) Ψ) := by
    intro j
    rw [dy_mulT (hd ha) (hD hΨ),
      dy_add (hD (contDiff_mulT ha (contDiff_dy hΨ j))) (hD (contDiff_mulT (contDiff_sd ha j) hΨ)),
      dy_mulT (hd ha) (hD (contDiff_dy hΨ j)), dy_mulT (hd (contDiff_sd ha j)) (hD hΨ)]
  simp only [lapT, lapS, hj, Pi.add_apply, mulT, Finset.smul_sum, Finset.sum_smul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  module

theorem radialT_mulT_apply {a : Space → ℝ} (ha : ContDiff ℝ ∞ a) {Ψ : ℝ × Space → CVec3}
    (hΨ : ContDiff ℝ ∞ Ψ) (p : ℝ × Space) :
    radialT (mulT a Ψ) p = a p.2 • radialT Ψ p + radS a p.2 • Ψ p := by
  have hda : Differentiable ℝ a := ha.differentiable (by simp)
  have hdΨ : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
  simp only [radialT, radS, dy_mulT hda hdΨ, Pi.add_apply, mulT, Finset.smul_sum,
    Finset.sum_smul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  module

theorem driftT_mulT_apply {a : Space → ℝ} (ha : ContDiff ℝ ∞ a) {Ψ : ℝ × Space → CVec3}
    (hΨ : ContDiff ℝ ∞ Ψ) (p : ℝ × Space) :
    driftT (mulT a Ψ) p = a p.2 • driftT Ψ p + ((1 / 2 : ℝ) * radS a p.2) • Ψ p := by
  have hda : Differentiable ℝ a := ha.differentiable (by simp)
  have hdΨ : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
  simp only [driftT, dτ_mulT hda hdΨ, radialT_mulT_apply ha hΨ p]
  simp only [mulT]
  module

/-! ### Scaled functions -/

theorem sd_comp_smul {b : Space → ℝ} (hb : Differentiable ℝ b) (c : ℝ) (j : Fin 3) :
    sd j (fun y => b (c • y)) = fun y => c * sd j b (c • y) := by
  funext y
  have h : HasFDerivAt (fun y : Space => b (c • y))
      ((fderiv ℝ b (c • y)).comp (c • ContinuousLinearMap.id ℝ Space)) y :=
    (hb (c • y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul c)
  simp only [sd]
  rw [h.fderiv]
  simp [map_smul, smul_eq_mul]

end UnforcedLeray.PhaseSpace
