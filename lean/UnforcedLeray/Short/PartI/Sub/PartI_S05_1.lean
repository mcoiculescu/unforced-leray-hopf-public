import UnforcedLeray.Short.PartI.Sub.PartI_S05

/-!
# Part I, task `PartI:S05/1`: the planar Laplacian of a Gaussian growing mode

Target: `gaussianModeLaplacian_proof : GaussianModeLaplacian`, source lines 788-803 of
`the November 2 reference manuscript`.

This file proves the reduction of the target to one polar identity, `PolarLaplacianCore`:
* `radialDelta2_eq_h`: on `(0, ∞)` the radial operator of `φ` is `h` (Rayleigh equation, `h_mul`);
* `gaussianModeLaplacian_of_core`: `PolarLaplacianCore` implies `GaussianModeLaplacian`
  (Mathlib's complex-plane Laplacian formula, the identity off `0`, and continuity at `0`).


-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- Step (ii): on `(0, ∞)` the radial operator of `φ` is the vorticity profile `h`. -/
theorem radialDelta2_eq_h (G : Planar.GaussianGrowingMode) {r : ℝ} (hr : 0 < r) :
    B0034.radialDelta2 G.φ r = G.h r := by
  have hne : ((GaussianVortex.radialOmega r : ℂ) - G.c) ≠ 0 := by
    intro h0
    have him := congrArg Complex.im h0
    simp at him
    have := G.im_pos
    linarith
  have h1 := G.φ_rayleigh r hr
  have h2 := G.h_mul r
  have key : ((GaussianVortex.radialOmega r : ℂ) - G.c) *
      (B0034.radialDelta2 G.φ r - G.h r) = 0 := by
    linear_combination h1 - h2
  have := (mul_eq_zero.1 key).resolve_left hne
  exact sub_eq_zero.1 this

/-- A continuous identity on the dense set `{y ≠ 0}` holds on all of `ℂ`. -/
theorem eq_everywhere_of_eq_off_zero {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ y : ℂ, y ≠ 0 → f y = g y) : ∀ y : ℂ, f y = g y := by
  have hd : Dense ({(0 : ℂ)}ᶜ : Set ℂ) := dense_compl_singleton 0
  have := Continuous.ext_on hd hf hg (fun y hy => h y hy)
  intro y
  exact congrFun this y

/-- **Core identity.** For a profile `ψ` smooth on `(0, ∞)` and `y ≠ 0`,
the planar Laplacian of the angular-two sector function `ψ(|y|) e^{2iϑ}` is the sector function
of the radial operator `ψ'' + ψ'/r - 4ψ/r²` (`B0034.radialDelta2`). -/
def PolarLaplacianCore : Prop :=
  ∀ ψ : ℝ → ℂ, ContDiffOn ℝ ∞ ψ (Ioi 0) → ∀ y : ℂ, y ≠ 0 →
    Laplacian.laplacian (Planar.NUE.Ang.ofProfile 2 ψ) y =
      Planar.NUE.Ang.ofProfile 2 (B0034.radialDelta2 ψ) y

/-- The reduction: the core polar identity gives the planar Laplacian identity `ΔΨ = q` for every
Gaussian growing mode, via the complex-plane Laplacian formula, the identity off `0`, and
continuity of both sides at `0`. -/
theorem gaussianModeLaplacian_of_core (hcore : PolarLaplacianCore) :
    GaussianModeLaplacian := by
  unfold PolarLaplacianCore at hcore
  intro G
  have hcont : Continuous (fun y : ℂ => Laplacian.laplacian G.Ψ y) := by
    have e : (fun y : ℂ => Laplacian.laplacian G.Ψ y) = fun y : ℂ =>
        iteratedFDeriv ℝ 2 G.Ψ y ![1, 1] + iteratedFDeriv ℝ 2 G.Ψ y ![Complex.I, Complex.I] := by
      funext y
      exact congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane G.Ψ) y
    rw [e]
    have hc : Continuous fun y : ℂ => iteratedFDeriv ℝ 2 G.Ψ y :=
      G.Ψ_smooth.continuous_iteratedFDeriv
        (by first | exact WithTop.coe_le_coe.2 le_top | simp | exact_mod_cast le_top)
    have hev : ∀ m : Fin 2 → ℂ, Continuous fun y : ℂ => iteratedFDeriv ℝ 2 G.Ψ y m := by
      intro m
      first
        | exact (ContinuousMultilinearMap.continuous_eval_const m).comp hc
        | fun_prop
        | continuity
    exact (hev _).add (hev _)
  have hall : ∀ z : ℂ, Laplacian.laplacian G.Ψ z = G.q z := by
    apply eq_everywhere_of_eq_off_zero hcont G.q_smooth.continuous
    intro z hz
    have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
    rw [G.Ψ_eq, hcore G.φ G.φ_smooth z hz, G.q_eq]
    simp only [Planar.NUE.Ang.ofProfile]
    rw [radialDelta2_eq_h G hr]
  intro y
  have h : Laplacian.laplacian G.Ψ y =
      iteratedFDeriv ℝ 2 G.Ψ y ![1, 1] + iteratedFDeriv ℝ 2 G.Ψ y ![Complex.I, Complex.I] :=
    congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane G.Ψ) y
  rw [← h]
  exact hall y

end UnforcedLeray.Short.PartI

end
