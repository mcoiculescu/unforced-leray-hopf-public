import UnforcedLeray.Short.PartI.Sub.T02_3_8

/-!
# Part I, task `PartI:T02/3/8/FourierPointwise`: pointwise Fourier inversion from a summable majorant (leaf O5 of `CylinderPoissonBound`)

Source of record: `the November 2 reference manuscript`, lines 276-288 (the zero-mean
part of a periodic function is bounded by its summable Fourier coefficients).

Target: `CylPoisFourierPointwise` (`Short/PartI/Sub/T02_3_8.lean`, line 203).

## Proof (plan A: pointwise Fourier series)

Fix `c > 0`, `f`, `η`, and put `F q = f (q, η)`.

* `F` is continuous and `(c/2 - -c/2)`-periodic (`cpFP_cont`, `cpFP_periodic`), since `c/2 - -c/2 = c`.
* `cpFPLift` is a continuous map `G` on `AddCircle (c/2 - -c/2)` with `G ↑q = F q`
  (`Function.Periodic.lift`, continuous by `continuous_coinduced_dom`).
* `cpFP_coeff`: the Fourier coefficients of `G` are the `q`-modes `Cyl.qMode c hc n f η`
  (both are integrals over `[-c/2, c/2]`, via `fourierCoeff_eq_intervalIntegral` and
  `fourierCoeffOn_eq_integral`).
* The coefficients are summable (`Summable.of_norm_bounded_eventually`: the bound holds off `n = 0`),
  so `has_pointwise_sum_fourier_series_of_summable` gives `HasSum (fun n => G_n • fourier n ↑x) (F x)`.
* Subtract the `n = 0` term (`hasSum_ite_eq`). Each remaining term has norm at most `A n`
  (`‖fourier n y‖ = 1`), and the zero term is `0 ≤ A 0`; `HasSum.norm_le_of_bounded` concludes.

All auxiliary names start with `cpFP`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- The centred period `c/2 - -c/2` is positive. -/
theorem cpFP_period_pos {c : ℝ} (hc : 0 < c) : 0 < c / 2 - -c / 2 := by linarith

/-- The slice `q ↦ f (q, η)` of a continuous function on the plane is continuous. -/
theorem cpFP_cont {f : Plane → ℂ} (η : ℝ) (hf : Continuous f) :
    Continuous (fun q : ℝ => f (q, η)) :=
  hf.comp (by fun_prop)

/-- The slice `q ↦ f (q, η)` of a `c`-periodic function is `(c/2 - -c/2)`-periodic. -/
theorem cpFP_periodic {c : ℝ} {f : Plane → ℂ} (η : ℝ) (hp : Cyl.IsPeriodic c f) :
    Function.Periodic (fun q : ℝ => f (q, η)) (c / 2 - -c / 2) := by
  rw [Cyl.half_sub_neg_half]
  exact hp.slice η

/-- The continuous function on `AddCircle (c/2 - -c/2)` induced by a continuous periodic `F`. -/
def cpFPLift (c : ℝ) (F : ℝ → ℂ) (hper : Function.Periodic F (c / 2 - -c / 2))
    (hF : Continuous F) : ContinuousMap (AddCircle (c / 2 - -c / 2)) ℂ :=
  ⟨hper.lift, by
    refine continuous_coinduced_dom.mpr ?_
    convert hF using 1
    funext x
    exact hper.lift_coe x⟩

/-- The Fourier coefficients of a continuous function `G` on `AddCircle (c/2 - -c/2)` that agrees
with `F` on the reals are the `q`-modes of `F` on `[-c/2, c/2]`. -/
theorem cpFP_coeff {c : ℝ} (hc : 0 < c) [Fact (0 < c / 2 - -c / 2)]
    (G : ContinuousMap (AddCircle (c / 2 - -c / 2)) ℂ) (F : ℝ → ℂ)
    (hG : ∀ x : ℝ, G (x : AddCircle (c / 2 - -c / 2)) = F x) (n : ℤ) :
    fourierCoeff G n = fourierCoeffOn (Cyl.neg_half_lt_half hc) F n := by
  rw [fourierCoeff_eq_intervalIntegral G n (-c / 2),
    fourierCoeffOn_eq_integral F n (Cyl.neg_half_lt_half hc),
    show -c / 2 + (c / 2 - -c / 2) = c / 2 by ring]
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [hG]

/-- Pointwise Fourier inversion for a continuous function on the circle with a summable majorant
of its non-zero coefficients. -/
theorem cpFP_main {c : ℝ} (hc : 0 < c) [Fact (0 < c / 2 - -c / 2)]
    (G : ContinuousMap (AddCircle (c / 2 - -c / 2)) ℂ) (F : ℝ → ℂ)
    (hG : ∀ x : ℝ, G (x : AddCircle (c / 2 - -c / 2)) = F x)
    (A : ℤ → ℝ) (hA : Summable A) (hA0 : ∀ n, 0 ≤ A n)
    (hbound : ∀ n : ℤ, n ≠ 0 → ‖fourierCoeffOn (Cyl.neg_half_lt_half hc) F n‖ ≤ A n)
    (x : ℝ) :
    ‖F x - fourierCoeffOn (Cyl.neg_half_lt_half hc) F 0‖ ≤ ∑' n, A n := by
  have hcoeff := cpFP_coeff hc G F hG
  have hsum : Summable (fourierCoeff G) := by
    refine Summable.of_norm_bounded_eventually hA ?_
    filter_upwards [Filter.eventually_cofinite_ne 0] with n hn
    rw [hcoeff n]
    exact hbound n hn
  have hpt := has_pointwise_sum_fourier_series_of_summable hsum (x : AddCircle (c / 2 - -c / 2))
  have hfn : ∀ (m : ℤ) (y : AddCircle (c / 2 - -c / 2)), ‖fourier m y‖ = 1 :=
    fun m y => Circle.norm_coe _
  have h0 : fourierCoeff G 0 • fourier 0 (x : AddCircle (c / 2 - -c / 2)) =
      fourierCoeffOn (Cyl.neg_half_lt_half hc) F 0 := by
    rw [fourier_zero, smul_eq_mul, mul_one, hcoeff 0]
  have hs0 : HasSum
      (fun n : ℤ => if n = 0 then fourierCoeff G 0 • fourier 0 (x : AddCircle (c / 2 - -c / 2))
        else 0)
      (fourierCoeff G 0 • fourier 0 (x : AddCircle (c / 2 - -c / 2))) :=
    hasSum_ite_eq 0 _
  have hdiff := hpt.sub hs0
  have hval : G (x : AddCircle (c / 2 - -c / 2)) -
      fourierCoeff G 0 • fourier 0 (x : AddCircle (c / 2 - -c / 2)) =
      F x - fourierCoeffOn (Cyl.neg_half_lt_half hc) F 0 := by
    rw [hG x, h0]
  rw [hval] at hdiff
  refine HasSum.norm_le_of_bounded hdiff hA.hasSum fun n => ?_
  show ‖fourierCoeff G n • fourier n (x : AddCircle (c / 2 - -c / 2)) -
      (if n = 0 then fourierCoeff G 0 • fourier 0 (x : AddCircle (c / 2 - -c / 2)) else 0)‖ ≤ A n
  by_cases hn : n = 0
  · subst hn
    simp [hA0 0]
  · rw [if_neg hn, sub_zero, norm_smul, hcoeff n, hfn n, mul_one]
    exact hbound n hn

/-- **Leaf O5** (pointwise Fourier inversion from a summable majorant). Target `CylPoisFourierPointwise`
(`Short/PartI/Sub/T02_3_8.lean`). -/
theorem cylPoisFourierPointwise : CylPoisFourierPointwise := by
  unfold CylPoisFourierPointwise
  intro c hc f A η hf hp hA hA0 hbound x
  haveI : Fact (0 < c / 2 - -c / 2) := ⟨cpFP_period_pos hc⟩
  have hper := cpFP_periodic (f := f) η hp
  have hF := cpFP_cont (f := f) η hf
  exact cpFP_main hc (cpFPLift c (fun q : ℝ => f (q, η)) hper hF) (fun q : ℝ => f (q, η))
    (fun y => hper.lift_coe y) A hA hA0 hbound x

end UnforcedLeray.Short.PartI
