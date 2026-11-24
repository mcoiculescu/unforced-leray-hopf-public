import UnforcedLeray.Cons.L2.CanonicalBranch
import UnforcedLeray.Lib.PlanarSpectralB.AdjointDomain
import UnforcedLeray.Lib.ComplexODEC.O10Tail

/-!
# Radial expression for the closed Gaussian oscillator

This leaf records the direct polar calculation needed to identify the concrete closed `D` action
on the growing mode with the profile oscillator appearing in `kapMode`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.B0010 UnforcedLeray.B0094 UnforcedLeray.Blueprint.Planar
open UnforcedLeray.ComplexODEC Set Filter Topology
open scoped ContDiff



namespace UnforcedLeray.Cons.G3b

/-- The profile oscillator applied to `r² β(r²)` is the Gaussian radial coefficient. -/
theorem oscillatorD_radialSq {β : ℝ → ℂ} (hβ : ContDiff ℝ ∞ β) {r : ℝ}
    (hr : r ≠ 0) :
    oscillatorD (fun x => (x : ℂ) ^ 2 * β (x ^ 2)) r =
      (r : ℂ) ^ 2 *
        (4 * (r ^ 2 : ℝ) * deriv (deriv β) (r ^ 2) +
          ((r ^ 2 + 12 : ℝ) : ℂ) * deriv β (r ^ 2) + 3 * β (r ^ 2)) := by
  let g : ℝ → ℂ := fun x => β (x ^ 2)
  have hg1 : ∀ x, deriv g x = (2 * (x : ℂ)) * deriv β (x ^ 2) := by
    intro x
    have hβx : HasDerivAt β (deriv β (x ^ 2)) (x ^ 2) :=
      (hβ.differentiable (by simp) (x ^ 2)).hasDerivAt
    have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have hc := HasDerivAt.scomp (x := x) (h := fun y : ℝ => y ^ 2)
      (g₁ := β) hβx hpow
    change deriv (β ∘ (fun y : ℝ => y ^ 2)) x = _
    rw [hc.deriv]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    simp only [smul_eq_mul]
    push_cast
    rfl
  have hg2 : ∀ x, deriv (deriv g) x =
      (2 : ℂ) * deriv β (x ^ 2) +
        (4 * (x : ℂ) ^ 2) * deriv (deriv β) (x ^ 2) := by
    intro x
    rw [show deriv g = fun (y : ℝ) => (2 * (y : ℂ)) * deriv β (y ^ 2) from funext hg1]
    -- The second chain rule is applied to `deriv β`, which is differentiable since β is smooth.
    have hβ' : ContDiff ℝ ∞ (deriv β) := (contDiff_infty_iff_deriv.mp hβ).2
    have hβ'x : HasDerivAt (deriv β) (deriv (deriv β) (x ^ 2)) (x ^ 2) :=
      (hβ'.differentiable (by simp) (x ^ 2)).hasDerivAt
    have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have hc := HasDerivAt.scomp (x := x) (h := fun y : ℝ => y ^ 2)
      (g₁ := deriv β) hβ'x hpow
    have hchain : deriv (fun y : ℝ => deriv β (y ^ 2)) x =
        (2 * (x : ℂ)) * deriv (deriv β) (x ^ 2) := by
      change deriv (deriv β ∘ (fun y : ℝ => y ^ 2)) x = _
      rw [hc.deriv]
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      simp only [smul_eq_mul]
      push_cast
      rfl
    have hclm : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x := by
      simpa using (hasDerivAt_id x).ofReal_comp
    have hlinAt : HasDerivAt (fun y : ℝ => (2 * (y : ℂ))) 2 x := by
      have hh := hclm.const_mul (2 : ℂ)
      simpa using hh
    have hlin : deriv (fun y : ℝ => (2 * (y : ℂ))) x = 2 := hlinAt.deriv
    change deriv ((fun y : ℝ => (2 * (y : ℂ))) *
      (deriv β ∘ (fun y : ℝ => y ^ 2))) x = _
    rw [deriv_mul hlinAt.differentiableAt hc.differentiableAt]
    have hchain' : deriv (deriv β ∘ (fun y : ℝ => y ^ 2)) x =
        (2 * (x : ℂ)) * deriv (deriv β) (x ^ 2) := by
      simpa only [Function.comp_def] using hchain
    rw [hlin, hchain']
    simp only [Function.comp_apply]
    ring

  have hf1 : ∀ x : ℝ, deriv (fun x : ℝ => (x : ℂ) ^ 2 * β (x ^ 2)) x =
      (2 * (x : ℂ)) * g x + (x : ℂ) ^ 2 * deriv g x := by
    intro x
    have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have hβx : HasDerivAt β (deriv β (x ^ 2)) (x ^ 2) :=
      (hβ.differentiable (by simp) (x ^ 2)).hasDerivAt
    have hcomp := HasDerivAt.scomp (x := x) (h := fun y : ℝ => y ^ 2)
      (g₁ := β) hβx hpow
    have hsq : HasDerivAt (fun y : ℝ => (y : ℂ) ^ 2) (2 * (x : ℂ)) x := by
      have hcast : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x := by
        simpa using (hasDerivAt_id x).ofReal_comp
      convert! hcast.pow 2 using 1 <;> simp
    change deriv ((fun y : ℝ => (y : ℂ) ^ 2) * g) x = _
    change deriv ((fun y : ℝ => (y : ℂ) ^ 2) *
      (β ∘ (fun y : ℝ => y ^ 2))) x = _
    rw [deriv_mul hsq.differentiableAt hcomp.differentiableAt, hsq.deriv]
    change (2 * (x : ℂ)) * g x + (x : ℂ) ^ 2 * deriv g x = _
    rfl
  have hf2 : deriv (deriv (fun x : ℝ => (x : ℂ) ^ 2 * β (x ^ 2))) r =
      (2 : ℂ) * g r + (4 * (r : ℂ)) * deriv g r +
        (r : ℂ) ^ 2 * deriv (deriv g) r := by
    rw [show deriv (fun x : ℝ => (x : ℂ) ^ 2 * β (x ^ 2)) =
        fun (x : ℝ) => (2 * (x : ℂ)) * g x + (x : ℂ) ^ 2 * deriv g x from funext hf1]
    change deriv ((fun x : ℝ => (2 * (x : ℂ)) * g x) +
      (fun x : ℝ => (x : ℂ) ^ 2 * deriv g x)) r = _
    have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * r) r := by
      simpa using hasDerivAt_pow 2 r
    have hβ' : ContDiff ℝ ∞ (deriv β) := (contDiff_infty_iff_deriv.mp hβ).2
    have hβ'r : HasDerivAt (deriv β) (deriv (deriv β) (r ^ 2)) (r ^ 2) :=
      (hβ'.differentiable (by simp) (r ^ 2)).hasDerivAt
    have hβr : HasDerivAt β (deriv β (r ^ 2)) (r ^ 2) :=
      (hβ.differentiable (by simp) (r ^ 2)).hasDerivAt
    have hcomp := HasDerivAt.scomp (x := r) (h := fun y : ℝ => y ^ 2)
      (g₁ := β) hβr hpow
    have hcomp' := HasDerivAt.scomp (x := r) (h := fun y : ℝ => y ^ 2)
      (g₁ := deriv β) hβ'r hpow
    have hgDeriv : deriv g = fun y : ℝ => (2 * (y : ℂ)) * deriv β (y ^ 2) := funext hg1
    have hclm : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) r := by
      simpa using (hasDerivAt_id r).ofReal_comp
    have hlinAt : HasDerivAt (fun x : ℝ => (2 * (x : ℂ))) 2 r := by
      have hh := hclm.const_mul (2 : ℂ)
      simpa using hh
    have hlin : deriv (fun x : ℝ => (2 * (x : ℂ))) r = 2 := hlinAt.deriv
    have hgdDiff : DifferentiableAt ℝ (deriv g) r := by
      rw [hgDeriv]
      exact hlinAt.differentiableAt.mul hcomp'.differentiableAt
    have hsqAt : HasDerivAt (fun x : ℝ => (x : ℂ) ^ 2) (2 * (r : ℂ)) r := by
      have h := HasDerivAt.comp r (hasDerivAt_pow 2 (r : ℂ))
        Complex.ofRealCLM.hasDerivAt
      simpa [Function.comp_def, Complex.ofRealCLM_apply, pow_one] using h
    have hsq : deriv (fun x : ℝ => (x : ℂ) ^ 2) r = 2 * (r : ℂ) := hsqAt.deriv
    change deriv (((fun x : ℝ => (2 * (x : ℂ))) *
      (β ∘ (fun y : ℝ => y ^ 2))) +
      ((fun x : ℝ => (x : ℂ) ^ 2) * deriv g)) r = _
    rw [deriv_add (hlinAt.differentiableAt.mul hcomp.differentiableAt)
        (hsqAt.differentiableAt.mul hgdDiff),
      deriv_mul hlinAt.differentiableAt hcomp.differentiableAt,
      deriv_mul hsqAt.differentiableAt hgdDiff,
      hlin, hsq, hg1 r, hg2 r]
    simp only [Function.comp_apply]
    rw [hcomp.deriv, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    simp only [smul_eq_mul]
    push_cast
    simp only [g]
    have hcoef (z : ℂ) :
        (r : ℂ) * (r : ℂ) * z * 4 + (r : ℂ) ^ 2 * z * 6 =
          (r : ℂ) ^ 2 * z * 10 := by
      rw [show (r : ℂ) * (r : ℂ) = (r : ℂ) ^ 2 by rw [pow_two]]
      calc
        _ = ((r : ℂ) ^ 2 * z) * (4 + 6) := by rw [← mul_add]
        _ = (r : ℂ) ^ 2 * z * 10 := by norm_num
    linear_combination hcoef (deriv β (r ^ 2))
  unfold oscillatorD
  rw [hf1 r, hf2, hg1, hg2]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  field_simp
  push_cast
  ring

/-- The actual whole-line mode has the same oscillator action as its smooth `modeBeta` radial
representative. The equality on the positive half-line transfers the first two derivatives. -/
theorem oscillatorD_modeVort_eq_modeBeta_radial {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) {β₀ : ℂ}
    (hβ : ∀ t, F t = β₀ * regLog c t) {r : ℝ} (hr : 0 < r) :
    oscillatorD (modeVort c F) r =
      (r : ℂ) ^ 2 *
        (4 * (r ^ 2 : ℝ) * deriv (deriv (modeBeta c β₀)) (r ^ 2) +
          ((r ^ 2 + 12 : ℝ) : ℂ) * deriv (modeBeta c β₀) (r ^ 2) +
          3 * modeBeta c β₀ (r ^ 2)) := by
  let f : ℝ → ℂ := fun x => (x : ℂ) ^ 2 * modeBeta c β₀ (x ^ 2)
  have hEq : Set.EqOn (modeVort c F) f (Ioi 0) := by
    intro x hx
    have hxpos : 0 < x := hx
    have hq := modeQ_eq (c := c) (F := F) (β₀ := β₀) hβ (x : ℂ)
    rw [modeQ_eq_modeVort_ofReal hxpos] at hq
    simpa [f, Complex.norm_real, abs_of_pos hxpos] using hq
  have hEq1 := hEq.iteratedDeriv_of_isOpen isOpen_Ioi 1
  have hEq2 := hEq.iteratedDeriv_of_isOpen isOpen_Ioi 2
  have hderiv1 : deriv (modeVort c F) r = deriv f r := by
    simpa only [iteratedDeriv_one] using hEq1 hr
  have hderiv2 : deriv (deriv (modeVort c F)) r = deriv (deriv f) r := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hEq2 hr
  calc
    oscillatorD (modeVort c F) r = oscillatorD f r := by
      unfold oscillatorD
      rw [hEq hr, hderiv1, hderiv2]
    _ = _ := oscillatorD_radialSq (contDiff_modeBeta hF.im_ne_zero β₀) hr.ne'

end UnforcedLeray.Cons.G3b
