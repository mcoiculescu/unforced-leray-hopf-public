import UnforcedLeray.Infra.AnalyticFredholm.FiniteRank
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Local reduction of the analytic Fredholm theorem to a scalar determinant

Let `X` be a complex Banach space and `F : ℂ → (X →L[ℂ] X)` analytic at `w`, with `F w`
approximable by finite-rank operators.  Choose a finite-rank `G = ∑ i, (φ i).smulRight (v i)`
with `‖F w - G‖ < 1`.  Near `w` the operator `1 - (F z - G)` is invertible with analytic inverse
`B z`, and

`1 - F z = (1 - G B z) (1 - (F z - G))`,   `G B z = ∑ i, (φ i ∘ B z).smulRight (v i)`.

By the determinant criterion (`isUnit_one_sub_sumRankOne_iff`), `1 - F z` is invertible iff
`d z = det (1 - M z) ≠ 0`, where `M z i j = φ i (B z (v j))`; `d` is analytic at `w`
(`exists_local_det`).  The principle of isolated zeros then gives the local dichotomy
`eventually_not_isUnit_or_eventually_isUnit`: either `1 - F z` is non-invertible on a whole
neighbourhood of `w`, or it is invertible on a punctured neighbourhood of `w`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace UnforcedLeray.Infra.AnalyticFredholm

/-- The determinant of an analytic family of matrices is analytic. -/
theorem analyticAt_det {𝕜 E ι : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [Fintype ι] [DecidableEq ι] {M : E → Matrix ι ι 𝕜} {w : E}
    (hM : ∀ i j, AnalyticAt 𝕜 (fun z => M z i j) w) :
    AnalyticAt 𝕜 (fun z => (M z).det) w := by
  simp_rw [Matrix.det_apply']
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => hM _ _)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- **Local determinant.** If `F` is analytic at `w` and `F w` is approximable by finite-rank
operators, there is a scalar function `d`, analytic at `w`, such that near `w` the operator
`1 - F z` is invertible exactly when `d z ≠ 0`. -/
theorem exists_local_det {F : ℂ → X →L[ℂ] X} {w : ℂ} (hF : AnalyticAt ℂ F w)
    (hw : IsApproximable (F w)) :
    ∃ d : ℂ → ℂ, AnalyticAt ℂ d w ∧ ∀ᶠ z in 𝓝 w, (IsUnit (1 - F z) ↔ d z ≠ 0) := by
  obtain ⟨G, hG, hdist⟩ := Metric.mem_closure_iff.mp hw 1 one_pos
  obtain ⟨n, φ, v, rfl⟩ := IsFiniteRank.exists_eq_sumRankOne hG
  have hnorm : ‖F w - sumRankOne φ v‖ < 1 := by rwa [dist_eq_norm] at hdist
  set G := sumRankOne φ v with hGdef
  let u : (X →L[ℂ] X)ˣ := Units.oneSub (F w - G) hnorm
  have hu : (u : X →L[ℂ] X) = 1 - (F w - G) := Units.val_oneSub _ _
  let B : ℂ → X →L[ℂ] X := fun z => Ring.inverse (1 - (F z - G))
  have h1 : AnalyticAt ℂ (fun z => 1 - (F z - G)) w :=
    analyticAt_const.sub (hF.sub analyticAt_const)
  have hB : AnalyticAt ℂ B w := (analyticAt_inverse (𝕜 := ℂ) u).comp_of_eq h1 hu.symm
  have hunit : ∀ᶠ z in 𝓝 w, IsUnit (1 - (F z - G)) := by
    have hmem : {x : X →L[ℂ] X | IsUnit x} ∈ 𝓝 (1 - (F w - G)) :=
      Units.isOpen.mem_nhds ⟨u, hu⟩
    exact h1.continuousAt hmem
  refine ⟨fun z => (1 - gramMatrix (fun i => (φ i).comp (B z)) v).det, ?_, ?_⟩
  · apply analyticAt_det
    intro i j
    simp only [Matrix.sub_apply, gramMatrix, Matrix.of_apply, ContinuousLinearMap.comp_apply]
    refine analyticAt_const.sub ?_
    have he : (fun z => φ i (B z (v j))) =
        ((φ i).comp (ContinuousLinearMap.apply ℂ X (v j))) ∘ B := rfl
    rw [he]
    exact (((φ i).comp (ContinuousLinearMap.apply ℂ X (v j))).analyticAt _).comp hB
  · filter_upwards [hunit] with z hz
    have hinv : B z * (1 - (F z - G)) = 1 := Ring.inverse_mul_cancel _ hz
    have hcomp : sumRankOne (fun i => (φ i).comp (B z)) v = G * B z :=
      (sumRankOne_comp φ v (B z)).symm
    have hfact : 1 - F z =
        (1 - sumRankOne (fun i => (φ i).comp (B z)) v) * (1 - (F z - G)) := by
      rw [hcomp, sub_mul, one_mul, mul_assoc, hinv, mul_one]
      abel
    rw [hfact, ← hz.unit_spec, Units.isUnit_mul_units]
    exact isUnit_one_sub_sumRankOne_iff _ _

/-- **Local dichotomy.** If `F` is analytic at `w` and `F w` is approximable, then either
`1 - F z` fails to be invertible for all `z` near `w`, or `1 - F z` is invertible for all
`z ≠ w` near `w`. -/
theorem eventually_not_isUnit_or_eventually_isUnit {F : ℂ → X →L[ℂ] X} {w : ℂ}
    (hF : AnalyticAt ℂ F w) (hw : IsApproximable (F w)) :
    (∀ᶠ z in 𝓝 w, ¬ IsUnit (1 - F z)) ∨ ∀ᶠ z in 𝓝[≠] w, IsUnit (1 - F z) := by
  obtain ⟨d, hd, hiff⟩ := exists_local_det hF hw
  rcases hd.eventually_eq_zero_or_eventually_ne_zero with h0 | hne
  · left
    filter_upwards [h0, hiff] with z hz hz'
    rw [hz'] at *
    exact fun h => h hz
  · right
    filter_upwards [hne, nhdsWithin_le_nhds hiff] with z hz hz'
    exact hz'.mpr hz

end UnforcedLeray.Infra.AnalyticFredholm
