import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult

/-!
# B0221 helper: second derivatives along lines and curves

Blueprint unit B0221 (label `eq:st18-t00114`), `paper/main.tex` lines 3316–3346; infrastructure
INF10 (multivariable chain rule in cylindrical/similarity coordinates).

The conjugation identity of B0221 is a chain-rule computation. This file reduces it to
one-variable calculus:

* `fderiv_eq_deriv_line`, `secondPartial_eq_deriv_deriv`: a first (second) partial
  derivative of a `C²` function is the first (second) derivative along the coordinate line
  (adapted from `Units/B0013/PolarLaplacian.lean`, `iteratedFDeriv_two_eq_deriv_deriv`,
  there on `ℂ`);
* `deriv_mul_comp`, `deriv_deriv_mul_comp`: first and second derivatives of
  `t ↦ A(t) b(c(t))` for a curve `c` and a `C²` function `b` (Leibniz and chain rules);
* `hasDerivAt_comp_eventually`, `hasDerivAt_comp_deriv`: first and second derivatives of a
  composite `t ↦ h(R(t))` of one-variable maps.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set

namespace UnforcedLeray.B0221

section Lines

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasDerivAt_line (x v : E) (t : ℝ) : HasDerivAt (fun s : ℝ => x + s • v) v t := by
  simpa using ((hasDerivAt_id t).smul_const v).const_add x

/-- A first partial derivative is the derivative along the line `t ↦ x + t v`. -/
theorem fderiv_eq_deriv_line {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) (v : E) :
    fderiv ℝ f x v = deriv (fun t : ℝ => f (x + t • v)) 0 := by
  have h := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line x v 0) (by simp)
  exact h.deriv.symm

/-- A second partial derivative `∂_v ∂_v f(x)` of a `C²` function is the second derivative
along the line `t ↦ x + t v`. -/
theorem secondPartial_eq_deriv_deriv {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (v : E) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x v = deriv (deriv fun t : ℝ => f (x + t • v)) 0 := by
  have hev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
    (hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hD : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : Tendsto (fun s : ℝ => x + s • v) (𝓝 0) (𝓝 x) := by
    have := (hasDerivAt_line x v 0).continuousAt.tendsto
    simpa using this
  have h1 : deriv (fun t : ℝ => f (x + t • v)) =ᶠ[𝓝 0] fun t => fderiv ℝ f (x + t • v) v := by
    filter_upwards [hc.eventually hev] with t ht
    exact (ht.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_line x v t)).deriv
  rw [h1.deriv_eq]
  have hg : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) x :=
    hD.clm_apply (differentiableAt_const v)
  have := hg.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line x v 0) (by simp)
  exact this.deriv.symm

/-- `(A · b∘c)'(t₀) = A' b(c) + A Db(c)(c')`. -/
theorem deriv_mul_comp {A : ℝ → ℝ} {A'0 : ℝ} {c : ℝ → F} {c'0 : F} {b : F → ℝ} {t0 : ℝ}
    (hA : HasDerivAt A A'0 t0) (hc : HasDerivAt c c'0 t0) (hb : DifferentiableAt ℝ b (c t0)) :
    deriv (fun t => A t * b (c t)) t0 = A'0 * b (c t0) + A t0 * fderiv ℝ b (c t0) c'0 :=
  (hA.mul (hb.hasFDerivAt.comp_hasDerivAt t0 hc)).deriv

/-- `(A · b∘c)''(t₀) = A'' b + 2 A' Db(c') + A (D²b(c',c') + Db(c''))` for `b` of class `C²`
at `c(t₀)`. -/
theorem deriv_deriv_mul_comp {A A' : ℝ → ℝ} {A'' : ℝ} {c c' : ℝ → F} {c'' : F} {b : F → ℝ}
    {t0 : ℝ} (hA : ∀ᶠ t in 𝓝 t0, HasDerivAt A (A' t) t) (hA' : HasDerivAt A' A'' t0)
    (hc : ∀ᶠ t in 𝓝 t0, HasDerivAt c (c' t) t) (hc' : HasDerivAt c' c'' t0)
    (hb : ContDiffAt ℝ 2 b (c t0)) :
    deriv (deriv fun t => A t * b (c t)) t0 =
      A'' * b (c t0) + 2 * (A' t0 * fderiv ℝ b (c t0) (c' t0)) +
        A t0 * (fderiv ℝ (fderiv ℝ b) (c t0) (c' t0) (c' t0) + fderiv ℝ b (c t0) c'') := by
  have hev : ∀ᶠ p in 𝓝 (c t0), DifferentiableAt ℝ b p :=
    (hb.eventually (by simp)).mono fun p hp => hp.differentiableAt (by norm_num)
  have hD : DifferentiableAt ℝ (fderiv ℝ b) (c t0) :=
    (hb.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hct : Tendsto c (𝓝 t0) (𝓝 (c t0)) := hc.self_of_nhds.continuousAt.tendsto
  have h1 : deriv (fun t => A t * b (c t)) =ᶠ[𝓝 t0]
      fun t => A' t * b (c t) + A t * fderiv ℝ b (c t) (c' t) := by
    filter_upwards [hA, hc, hct.eventually hev] with t hAt hct' hbt
    exact (hAt.mul (hbt.hasFDerivAt.comp_hasDerivAt t hct')).deriv
  rw [h1.deriv_eq]
  have hb0 : HasDerivAt (fun t => b (c t)) (fderiv ℝ b (c t0) (c' t0)) t0 :=
    (hb.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t0 hc.self_of_nhds
  have hDc : HasDerivAt (fun t => fderiv ℝ b (c t)) (fderiv ℝ (fderiv ℝ b) (c t0) (c' t0)) t0 :=
    hD.hasFDerivAt.comp_hasDerivAt t0 hc.self_of_nhds
  have h3 : HasDerivAt (fun t => A' t * b (c t) + A t * fderiv ℝ b (c t) (c' t))
      (A'' * b (c t0) + A' t0 * fderiv ℝ b (c t0) (c' t0) +
        (A' t0 * fderiv ℝ b (c t0) (c' t0) +
          A t0 * (fderiv ℝ (fderiv ℝ b) (c t0) (c' t0) (c' t0) + fderiv ℝ b (c t0) c''))) t0 :=
    (hA'.mul hb0).add (hA.self_of_nhds.mul (hDc.clm_apply hc'))
  rw [h3.deriv]
  ring

/-- First derivative of a composite `t ↦ h(R(t))`, near `t₀`. -/
theorem hasDerivAt_comp_eventually {h h' : ℝ → F} {R R' : ℝ → ℝ} {t0 : ℝ}
    (hh : ∀ᶠ u in 𝓝 (R t0), HasDerivAt h (h' u) u)
    (hR : ∀ᶠ t in 𝓝 t0, HasDerivAt R (R' t) t) :
    ∀ᶠ t in 𝓝 t0, HasDerivAt (fun t => h (R t)) (R' t • h' (R t)) t := by
  have hRc : Tendsto R (𝓝 t0) (𝓝 (R t0)) := hR.self_of_nhds.continuousAt.tendsto
  filter_upwards [hR, hRc.eventually hh] with t hRt hht
  exact hht.scomp t hRt

/-- Second derivative of a composite `t ↦ h(R(t))` at `t₀`. -/
theorem hasDerivAt_comp_deriv {h' : ℝ → F} {h'' : F} {R R' : ℝ → ℝ} {R'' : ℝ} {t0 : ℝ}
    (hh' : HasDerivAt h' h'' (R t0)) (hR : ∀ᶠ t in 𝓝 t0, HasDerivAt R (R' t) t)
    (hR' : HasDerivAt R' R'' t0) :
    HasDerivAt (fun t => R' t • h' (R t)) (R' t0 • (R' t0 • h'') + R'' • h' (R t0)) t0 :=
  hR'.smul (hh'.scomp t0 hR.self_of_nhds)

end Lines

end UnforcedLeray.B0221
