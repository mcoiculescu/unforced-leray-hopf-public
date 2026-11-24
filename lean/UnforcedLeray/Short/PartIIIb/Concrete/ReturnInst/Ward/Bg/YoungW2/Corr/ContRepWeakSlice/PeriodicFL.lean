import Mathlib.Analysis.Fourier.AddCircle

/-!
# Fundamental lemma for continuous periodic functions (helper of `bgContRepWeakSlice`)

A continuous `P`-periodic real function orthogonal to every `cos (2π m t / P)` and
`sin (2π m t / P)` on a period vanishes (completeness of the Fourier basis on `AddCircle P`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology AddCircle
open scoped Real

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem periodic_eq_zero_of_trig {P : ℝ} (hP : 0 < P) {H : ℝ → ℝ} (hc : Continuous H)
    (hper : ∀ t, H (t + P) = H t)
    (hcos : ∀ m : ℤ, ∫ t in Ioc 0 P, Real.cos (2 * π * m * t / P) * H t = 0)
    (hsin : ∀ m : ℤ, ∫ t in Ioc 0 P, Real.sin (2 * π * m * t / P) * H t = 0) :
    ∀ t, H t = 0 := by
  have : Fact (0 < P) := ⟨hP⟩
  have hperc : Function.Periodic (fun t => (H t : ℂ)) P := fun t => by simp [hper t]
  let Hc : C(AddCircle P, ℂ) :=
    ⟨hperc.lift, continuous_coinduced_dom.mpr (Complex.continuous_ofReal.comp hc)⟩
  have hHc : ∀ t : ℝ, Hc (t : AddCircle P) = (H t : ℂ) := fun t => rfl
  have hcoef : ∀ n : ℤ, fourierCoeff Hc n = 0 := by
    intro n
    rw [fourierCoeff_eq_intervalIntegral _ _ 0, zero_add, intervalIntegral.integral_of_le hP.le]
    have h1 : ∀ x : ℝ, (fourier (-n) (x : AddCircle P) : ℂ) • Hc (x : AddCircle P) =
        ((Real.cos (2 * π * (-n : ℤ) * x / P) * H x : ℝ) : ℂ) +
          ((Real.sin (2 * π * (-n : ℤ) * x / P) * H x : ℝ) : ℂ) * Complex.I := by
      intro x
      rw [fourier_coe_apply, hHc, smul_eq_mul, Complex.exp_eq_exp_ℂ, ← Complex.exp_eq_exp_ℂ]
      have : (2 * ↑π * Complex.I * ↑(-n : ℤ) * ↑x / ↑P : ℂ) =
          ((2 * π * (-n : ℤ) * x / P : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.exp_mul_I]
      push_cast
      ring
    simp_rw [h1]
    have hi1 : IntegrableOn (fun x : ℝ => Real.cos (2 * π * (-n : ℤ) * x / P) * H x) (Ioc 0 P) := by
      refine (Continuous.integrableOn_Ioc ?_)
      fun_prop
    have hi2 : IntegrableOn (fun x : ℝ => Real.sin (2 * π * (-n : ℤ) * x / P) * H x) (Ioc 0 P) := by
      refine (Continuous.integrableOn_Ioc ?_)
      fun_prop
    have hi1' : Integrable (fun x : ℝ => ((Real.cos (2 * π * (-n : ℤ) * x / P) * H x : ℝ) : ℂ))
        (volume.restrict (Ioc 0 P)) := hi1.ofReal
    have hi2' : Integrable (fun x : ℝ => ((Real.sin (2 * π * (-n : ℤ) * x / P) * H x : ℝ) : ℂ) * Complex.I)
        (volume.restrict (Ioc 0 P)) := hi2.ofReal.mul_const Complex.I
    rw [integral_add hi1' hi2', integral_mul_const, integral_complex_ofReal, integral_complex_ofReal]
    have a1 := hcos (-n)
    have a2 := hsin (-n)
    rw [a1, a2]; simp
  have hL2 : ContinuousMap.toLp (E := ℂ) 2 haarAddCircle ℂ Hc = 0 := by
    apply fourierBasis.repr.injective
    ext n
    rw [fourierBasis_repr, fourierCoeff_toLp, hcoef]
    simp
  have hae : (fun x => Hc x) =ᵐ[haarAddCircle] 0 := by
    have := ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ) haarAddCircle Hc
    rw [hL2] at this
    filter_upwards [this] with x hx
    simpa using hx.symm
  have h0 : ∀ x, Hc x = 0 := by
    intro x
    have := (Continuous.ae_eq_iff_eq (μ := (haarAddCircle : Measure (AddCircle P)))
      Hc.continuous continuous_const (g := fun _ => (0:ℂ))).mp hae
    exact congrFun this x
  intro t
  have := h0 (t : AddCircle P)
  rw [hHc] at this
  exact_mod_cast this

end UnforcedLeray.Short.PartIIIb.Concrete
