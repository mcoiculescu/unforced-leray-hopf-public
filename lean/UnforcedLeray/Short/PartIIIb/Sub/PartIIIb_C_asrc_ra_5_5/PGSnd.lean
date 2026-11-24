import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_5
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# `PartIII-b:C/asrc/ra/5/5` : polynomial growth of the projection `p ↦ p.2`

Toolkit lemma for `PolyGrowth`: the projection onto the meridional vector is a continuous
linear map, so its derivatives of order `≥ 2` vanish, its first derivative is the map itself
(norm `≤ 1`), and its value has norm `≤ 1 + |x|²`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem polyGrowth_snd (n : ℕ) : PolyGrowth n (fun p : ℝ × (ℝ × ℝ) => p.2) := by
  refine ⟨contDiff_snd.contDiffOn, fun s0 s1 _ _ => ⟨2, 1, by norm_num, fun m _ s _ x => ?_⟩⟩
  have hsq : 0 ≤ sq2 x := by unfold sq2; positivity
  rcases m with _ | _ | k
  · rw [norm_iteratedFDeriv_zero]
    show ‖x‖ ≤ 2 * (1 + sq2 x) ^ 1
    rw [pow_one, Prod.norm_def]
    apply max_le
    · simp only [Real.norm_eq_abs]
      unfold sq2
      nlinarith [sq_abs x.1, abs_nonneg x.1, sq_nonneg (|x.1| - 1), sq_nonneg x.2]
    · simp only [Real.norm_eq_abs]
      unfold sq2
      nlinarith [sq_abs x.2, abs_nonneg x.2, sq_nonneg (|x.2| - 1), sq_nonneg x.1]
  · rw [norm_iteratedFDeriv_one]
    have hd : fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => p.2) (s, x) =
        ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ) :=
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).fderiv
    rw [hd]
    have h1 := ContinuousLinearMap.norm_snd_le ℝ ℝ (ℝ × ℝ)
    have h2 : (1 : ℝ) ≤ 2 * (1 + sq2 x) ^ 1 := by rw [pow_one]; linarith
    linarith
  · have hc : fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => p.2) =
        fun _ => ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ) :=
      funext fun y => (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).fderiv
    have e1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fun p : ℝ × (ℝ × ℝ) => p.2)
      (x := (s, x)) (n := k + 1)
    rw [hc] at e1
    have hz : ‖iteratedFDeriv ℝ (k + 1) (fun _ : ℝ × (ℝ × ℝ) =>
        ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) (s, x)‖ = 0 := by
      rw [iteratedFDeriv_const_of_ne (by omega)]
      simp
    have h2 : (0 : ℝ) ≤ 2 * (1 + sq2 x) ^ 1 := by rw [pow_one]; linarith
    rw [← e1, hz]
    exact h2

end UnforcedLeray.Short.PartIIIb.Concrete
