import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.JetWord
import UnforcedLeray.Lib.Train.Ops

/-!
Helper for task `PartII-b:G4/3/6/1/5/2` (`VcSpatialJetBound`, SP line 2205): the jet norm of a
`Vec`-valued smooth field is bounded by the sum over components and coordinate words of the
coordinate derivatives (vector analogue of `cjw_norm_le_sum`).
-/

set_option autoImplicit false

open scoped ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Train UnforcedLeray.Short.PartI

/-- The embedding of the `k`-th coordinate line into `Vec`. -/
noncomputable def vecLine (k : Fin 2) : ℝ →L[ℝ] Vec :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single k (1 : ℝ))

theorem norm_vecLine_le (k : Fin 2) : ‖vecLine k‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun t => ?_)
  simp [vecLine, norm_smul]

theorem vec_eq_sum_line (v : Vec) : v = vecLine 0 (v 0) + vecLine 1 (v 1) := by
  ext j
  fin_cases j <;> simp [vecLine]

theorem contDiff_comp_proj {F : UnforcedLeray.Cyl.Plane → Vec} (hF : ContDiff ℝ ∞ F) (k : Fin 2) :
    ContDiff ℝ ∞ (fun x => F x k) :=
  (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp hF

theorem norm_jet_vec_le (F : UnforcedLeray.Cyl.Plane → Vec) (hF : ContDiff ℝ ∞ F) (l : ℕ)
    (z : UnforcedLeray.Cyl.Plane) :
    ‖iteratedFDeriv ℝ l F z‖ ≤
      ‖iteratedFDeriv ℝ l (fun x => F x 0) z‖ + ‖iteratedFDeriv ℝ l (fun x => F x 1) z‖ := by
  have hF0 := contDiff_comp_proj hF 0
  have hF1 := contDiff_comp_proj hF 1
  have e : F = (vecLine 0 ∘ fun x => F x 0) + (vecLine 1 ∘ fun x => F x 1) := by
    funext x
    exact vec_eq_sum_line (F x)
  have c0 : ContDiffAt ℝ l (fun x => F x 0) z :=
    (hF0.of_le (by exact_mod_cast le_top)).contDiffAt
  have c1 : ContDiffAt ℝ l (fun x => F x 1) z :=
    (hF1.of_le (by exact_mod_cast le_top)).contDiffAt
  have d0 : ContDiffAt ℝ l (vecLine 0 ∘ fun x => F x 0) z :=
    ((vecLine 0).contDiff.contDiffAt).comp z c0
  have d1 : ContDiffAt ℝ l (vecLine 1 ∘ fun x => F x 1) z :=
    ((vecLine 1).contDiff.contDiffAt).comp z c1
  have e2 : iteratedFDeriv ℝ l F z = iteratedFDeriv ℝ l ((vecLine 0 ∘ fun x => F x 0) +
      (vecLine 1 ∘ fun x => F x 1)) z := by rw [← e]
  rw [e2, iteratedFDeriv_add_apply d0 d1]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine ((vecLine 0).norm_iteratedFDeriv_comp_left c0 le_rfl).trans ?_
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_vecLine_le 0)
  · refine ((vecLine 1).norm_iteratedFDeriv_comp_left c1 le_rfl).trans ?_
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_vecLine_le 1)

end UnforcedLeray.Short.IIb
