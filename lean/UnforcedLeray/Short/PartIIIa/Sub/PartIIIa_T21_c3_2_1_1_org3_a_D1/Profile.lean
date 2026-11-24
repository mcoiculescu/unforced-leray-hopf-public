import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Helper for `PartIII-a:T21/c3/2/1/1/org/3/a/1/1`: the transported profile

Source: `the November 2 reference manuscript` (SP) 2962-2964 (radial Euler
transport `T(z)f(y) = f(e^{-izΩ(|y|)} y)`, `Ω(|y|) = e^{-|y|²/4}`, cf. SP 841-852).

`tprof g (z, y) = g(flowP z y)` with `flowP z y` the rotation of `y` by the angle `-zΩ(|y|)`.
The flow preserves `|y|`, and `tprof g` solves the transport equation
`∂_z tprof g + V·∇_y tprof g = 0`, `V(y) = Ω(|y|)(-y₂, y₁)` (`fderiv_tprof_vort`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.RelFreeTestSub.D1Aux

/-- `Ω(y) = e^{-|y|²/4}`. -/
def omg (y : ℝ × ℝ) : ℝ := Real.exp (-((y.1 ^ 2 + y.2 ^ 2) / 4))

/-- Rotation by the angle `α`. -/
def rotP (α : ℝ) (y : ℝ × ℝ) : ℝ × ℝ :=
  (Real.cos α * y.1 - Real.sin α * y.2, Real.sin α * y.1 + Real.cos α * y.2)

/-- The radial Euler flow `y ↦ e^{-izΩ(|y|)} y`. -/
def flowP (z : ℝ) (y : ℝ × ℝ) : ℝ × ℝ := rotP (-(z * omg y)) y

/-- The transported profile `(z, y) ↦ g(flowP z y)`. -/
def tprof (g : ℝ × ℝ → ℝ) (p : ℝ × (ℝ × ℝ)) : ℝ := g (flowP p.1 p.2)

/-- The central vortex velocity in moving variables, `V(y) = Ω(|y|)(-y₂, y₁)`. -/
def vortV (y : ℝ × ℝ) : ℝ × ℝ := (-(omg y * y.2), omg y * y.1)

theorem rotP_normSq (α : ℝ) (y : ℝ × ℝ) :
    (rotP α y).1 ^ 2 + (rotP α y).2 ^ 2 = y.1 ^ 2 + y.2 ^ 2 := by
  simp only [rotP]
  have h := Real.sin_sq_add_cos_sq α
  linear_combination (y.1 ^ 2 + y.2 ^ 2) * h

theorem omg_rotP (α : ℝ) (y : ℝ × ℝ) : omg (rotP α y) = omg y := by
  simp only [omg, rotP_normSq]

theorem rotP_rotP (α β : ℝ) (y : ℝ × ℝ) : rotP α (rotP β y) = rotP (α + β) y := by
  simp only [rotP, Real.cos_add, Real.sin_add, Prod.mk.injEq]
  constructor <;> ring

theorem rotP_zero (y : ℝ × ℝ) : rotP 0 y = y := by
  simp [rotP]

theorem flowP_zero (y : ℝ × ℝ) : flowP 0 y = y := by
  simp [flowP, rotP_zero]

theorem flowP_normSq (z : ℝ) (y : ℝ × ℝ) :
    (flowP z y).1 ^ 2 + (flowP z y).2 ^ 2 = y.1 ^ 2 + y.2 ^ 2 := rotP_normSq _ _

theorem flowP_shift (z h : ℝ) (y : ℝ × ℝ) :
    flowP (z + h) (rotP (h * omg y) y) = flowP z y := by
  simp only [flowP, omg_rotP, rotP_rotP]
  congr 1
  ring

theorem tprof_shift (g : ℝ × ℝ → ℝ) (z h : ℝ) (y : ℝ × ℝ) :
    tprof g (z + h, rotP (h * omg y) y) = tprof g (z, y) := by
  simp only [tprof, flowP_shift]

theorem tprof_zero (g : ℝ × ℝ → ℝ) (y : ℝ × ℝ) : tprof g (0, y) = g y := by
  simp [tprof, flowP_zero]

theorem contDiff_omg : ContDiff ℝ ∞ omg := by
  unfold omg; fun_prop

theorem contDiff_flowP : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => flowP p.1 p.2) := by
  unfold flowP rotP omg; fun_prop

theorem contDiff_tprof {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (tprof g) :=
  hg.comp contDiff_flowP

theorem tprof_eq_zero {g : ℝ × ℝ → ℝ} {R : ℝ}
    (hg : ∀ y : ℝ × ℝ, R ^ 2 < y.1 ^ 2 + y.2 ^ 2 → g y = 0)
    {p : ℝ × (ℝ × ℝ)} (hp : R ^ 2 < p.2.1 ^ 2 + p.2.2 ^ 2) : tprof g p = 0 := by
  unfold tprof
  apply hg
  rw [flowP_normSq]
  exact hp

theorem hasDerivAt_rotP_curve (y : ℝ × ℝ) :
    HasDerivAt (fun h : ℝ => rotP (h * omg y) y) (vortV y) 0 := by
  have hθ : HasDerivAt (fun h : ℝ => h * omg y) (omg y) 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).mul_const (omg y)
  have hc := (Real.hasDerivAt_cos ((0 : ℝ) * omg y)).comp (0 : ℝ) hθ
  have hs := (Real.hasDerivAt_sin ((0 : ℝ) * omg y)).comp (0 : ℝ) hθ
  have h1 := (hc.mul_const y.1).sub (hs.mul_const y.2)
  have h2 := (hs.mul_const y.1).add (hc.mul_const y.2)
  have h3 := h1.prodMk h2
  have hv : ((-Real.sin (0 * omg y) * omg y * y.1 - Real.cos (0 * omg y) * omg y * y.2),
      (Real.cos (0 * omg y) * omg y * y.1 + -Real.sin (0 * omg y) * omg y * y.2)) = vortV y := by
    simp [vortV]
  rw [← hv]
  exact h3

/-- **Transport identity**: `∂_z tprof g + V·∇_y tprof g = 0`. -/
theorem fderiv_tprof_vort {g : ℝ × ℝ → ℝ} {z : ℝ} {y : ℝ × ℝ}
    (hd : DifferentiableAt ℝ (tprof g) (z, y)) :
    fderiv ℝ (tprof g) (z, y) ((1 : ℝ), vortV y) = 0 := by
  set c : ℝ → ℝ × (ℝ × ℝ) := fun h => (z + h, rotP (h * omg y) y) with hcdef
  have hcurve : HasDerivAt c ((1 : ℝ), vortV y) 0 :=
    ((hasDerivAt_id' (0 : ℝ)).const_add z).prodMk (hasDerivAt_rotP_curve y)
  have h0 : c 0 = (z, y) := by simp [hcdef, rotP_zero]
  have hl : HasFDerivAt (tprof g) (fderiv ℝ (tprof g) (z, y)) (c 0) := by
    rw [h0]; exact hd.hasFDerivAt
  have hcomp := hl.comp_hasDerivAt (0 : ℝ) hcurve
  have hconst : (tprof g ∘ c) = fun _ => tprof g (z, y) := by
    funext h
    simp only [Function.comp, hcdef, tprof_shift]
  rw [hconst] at hcomp
  exact hcomp.unique (hasDerivAt_const _ _)

end UnforcedLeray.Short.IIIa.RelFreeTestSub.D1Aux
