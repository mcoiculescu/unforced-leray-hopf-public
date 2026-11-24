import UnforcedLeray.Units.B0147.CellNorm

/-!
# B0147 helper: the rescaling `y = x/√a`

Blueprint unit **B0147** (`eq:st18-t00145`, `paper/main.tex` lines 2217–2234), helper file.

With `λ = a^{-1/2}` (`lam a`) and `L = λc`:

* `velocity_scale`: `V_c^k(x) = λ³ ∑ₙ U_k(λx - nLe₁)` (unit B0146's `periodicVelocity`);
* `crossStress_scale`: `Q_c^{kl}(x) = λ⁶ bil L U_k U_l (λx)` (unit B0146's `crossStress`);
* `derivWord_scale`: every derivative word of length `j` produces the factor `λʲ`; the
  identity holds for every function since Mathlib's `deriv` commutes with dilations
  (`deriv_comp_mul_left`), and genuine partial derivatives are transported
  (`hasPartialX_scale`, `hasPartialY_scale`);
* the transverse weight `(1 + η²/a)^m` is `(1 + (λη)²)^m` and commutes with the lattice sum.
-/

set_option autoImplicit false

noncomputable section

open Filter
open scoped Topology

namespace UnforcedLeray.B0147

open UnforcedLeray.GaussianVortex
open UnforcedLeray.B0146 (latticeSum shift uc vcomp)
open UnforcedLeray.B0151 (derivWord)
open UnforcedLeray.B0113 (heatWidth)

theorem partialX_scale (K l : ℝ) (D : Plane → ℝ) :
    partialX (fun z => K * D (l * z.1, l * z.2)) =
      fun z => K * l * partialX D (l * z.1, l * z.2) := by
  funext z
  show deriv (fun x => K * D (l * x, l * z.2)) z.1 =
    K * l * deriv (fun x => D (x, l * z.2)) (l * z.1)
  rw [deriv_const_mul_field]
  have h := deriv_comp_mul_left l (fun u => D (u, l * z.2)) z.1
  simp only [smul_eq_mul] at h
  rw [h]
  ring

theorem partialY_scale (K l : ℝ) (D : Plane → ℝ) :
    partialY (fun z => K * D (l * z.1, l * z.2)) =
      fun z => K * l * partialY D (l * z.1, l * z.2) := by
  funext z
  show deriv (fun y => K * D (l * z.1, l * y)) z.2 =
    K * l * deriv (fun y => D (l * z.1, y)) (l * z.2)
  rw [deriv_const_mul_field]
  have h := deriv_comp_mul_left l (fun u => D (l * z.1, u)) z.2
  simp only [smul_eq_mul] at h
  rw [h]
  ring

/-- **Dilation of derivative words**: `D_w [K h(l·)] = K l^{|w|} (D_w h)(l·)`. -/
theorem derivWord_scale (w : List Bool) (K l : ℝ) (h : Plane → ℝ) :
    derivWord w (fun z => K * h (l * z.1, l * z.2)) =
      fun z => K * l ^ w.length * derivWord w h (l * z.1, l * z.2) := by
  induction w with
  | nil =>
    funext z
    simp [derivWord]
  | cons b w ih =>
    cases b
    · show partialY (derivWord w _) = _
      rw [ih, partialY_scale]
      funext z
      show K * l ^ w.length * l * partialY (derivWord w h) (l * z.1, l * z.2) =
        K * l ^ (w.length + 1) * partialY (derivWord w h) (l * z.1, l * z.2)
      ring
    · show partialX (derivWord w _) = _
      rw [ih, partialX_scale]
      funext z
      show K * l ^ w.length * l * partialX (derivWord w h) (l * z.1, l * z.2) =
        K * l ^ (w.length + 1) * partialX (derivWord w h) (l * z.1, l * z.2)
      ring

theorem hasPartialX_scale (K l : ℝ) (D : Plane → ℝ) (z : Plane)
    (h : B0146.HasPartialX D (l * z.1, l * z.2)) :
    B0146.HasPartialX (fun x => K * D (l * x.1, l * x.2)) z := by
  have h1 : HasDerivAt (fun t : ℝ => l * t) l z.1 := by
    simpa using (hasDerivAt_id z.1).const_mul l
  exact B0146.hasPartialX_of ((h.comp z.1 h1).const_mul K)

theorem hasPartialY_scale (K l : ℝ) (D : Plane → ℝ) (z : Plane)
    (h : B0146.HasPartialY D (l * z.1, l * z.2)) :
    B0146.HasPartialY (fun x => K * D (l * x.1, l * x.2)) z := by
  have h1 : HasDerivAt (fun t : ℝ => l * t) l z.2 := by
    simpa using (hasDerivAt_id z.2).const_mul l
  exact B0146.hasPartialY_of ((h.comp z.2 h1).const_mul K)

/-- The transverse weight commutes with the lattice sum. -/
theorem latticeSum_weight (L : ℝ) (m : ℕ) (f : Plane → ℝ) (y : Plane) :
    (1 + y.2 ^ 2) ^ m * latticeSum L f y = latticeSum L (fun x => (1 + x.2 ^ 2) ^ m * f x) y := by
  simp only [latticeSum]
  rw [← tsum_mul_left]
  rfl

theorem shift_scale (c l : ℝ) (n : ℤ) (z : Plane) :
    (l * (shift c n z).1, l * (shift c n z).2) = shift (l * c) n (l * z.1, l * z.2) :=
  Prod.ext (by simp only [shift]; ring) (by simp only [shift])

/-- Dilation of a lattice sum: period `c` becomes `lc`. -/
theorem latticeSum_scale {c κ l : ℝ} {g h : Plane → ℝ}
    (hg : ∀ w, g w = κ * h (l * w.1, l * w.2)) (z : Plane) :
    latticeSum c g z = κ * latticeSum (l * c) h (l * z.1, l * z.2) := by
  simp only [latticeSum]
  rw [← tsum_mul_left]
  congr 1
  funext n
  rw [hg, shift_scale]

variable {ν c s : ℝ}

theorem vcomp_periodicVelocity (hc : c ≠ 0) (ha : 0 < heatWidth ν s) (k : Fin 2) (z : Plane) :
    vcomp (B0146.periodicVelocity ν c s z) k = latticeSum c (uc k (heatWidth ν s)) z := by
  rw [B0146.periodicVelocity_eq hc ha]
  fin_cases k <;> rfl

/-- `V_c^k(x) = λ³ ∑ₙ U_k(λx - nλc e₁)`. -/
theorem velocity_scale (hc : c ≠ 0) (ha : 0 < heatWidth ν s) (k : Fin 2) :
    (fun x => vcomp (B0146.periodicVelocity ν c s x) k) = fun x =>
      lam (heatWidth ν s) ^ 3 *
        latticeSum (lam (heatWidth ν s) * c) (U k)
          (lam (heatWidth ν s) * x.1, lam (heatWidth ν s) * x.2) := by
  funext x
  rw [vcomp_periodicVelocity hc ha, latticeSum_scale (fun w => uc_scale ha k w)]

/-- `Q_c^{kl}(x) = λ⁶ ∑_{i≠j} U_k(λx - iλc e₁) U_l(λx - jλc e₁)`. -/
theorem crossStress_scale (ha : 0 < heatWidth ν s) (k l : Fin 2) :
    (fun x => B0146.crossStress ν c s x k l) = fun x =>
      lam (heatWidth ν s) ^ 6 *
        bil (lam (heatWidth ν s) * c) (U k) (U l)
          (lam (heatWidth ν s) * x.1, lam (heatWidth ν s) * x.2) := by
  funext z
  simp only [B0146.crossStress, B0146.imageVelocity, B0146.isoVelocity_eq, bil]
  rw [← tsum_mul_left]
  congr 1
  funext p
  have e : ∀ (k : Fin 2) (w : Plane), vcomp (B0113.vExp (heatWidth ν s) w) k =
      lam (heatWidth ν s) ^ 3 * U k (lam (heatWidth ν s) * w.1, lam (heatWidth ν s) * w.2) :=
    fun k w => uc_scale ha k w
  rw [e, e, shift_scale, shift_scale]
  ring

theorem lam_pow_eq_rpow {a : ℝ} (ha : 0 < a) (n : ℕ) : lam a ^ n = a ^ (-(n : ℝ) / 2) := by
  have h1 : lam a = a ^ (-(1 / 2 : ℝ)) := by
    rw [lam, Real.sqrt_eq_rpow, Real.rpow_neg ha.le]
  rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul ha.le]
  congr 1
  ring

theorem weight_eq {a : ℝ} (ha : 0 < a) (m : ℕ) (z : Plane) :
    (1 + z.2 ^ 2 / a) ^ m = (1 + (lam a * z.2) ^ 2) ^ m := by
  rw [mul_pow, lam_sq ha, div_eq_inv_mul]

/-- `a ≤ c²` is the rescaled period bound `λc ≥ 1`. -/
theorem one_le_lam_mul {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (hac : a ≤ c ^ 2) :
    1 ≤ lam a * c := by
  have h1 : Real.sqrt a ≤ c := by
    have := Real.sqrt_le_sqrt hac
    rwa [Real.sqrt_sq hc.le] at this
  have h2 : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  rw [lam, inv_mul_eq_div, le_div_iff₀ h2, one_mul]
  exact h1

theorem lam_mul_sq {a c : ℝ} (ha : 0 < a) : (lam a * c) ^ 2 = c ^ 2 / a := by
  rw [mul_pow, lam_sq ha, inv_mul_eq_div]

end UnforcedLeray.B0147
