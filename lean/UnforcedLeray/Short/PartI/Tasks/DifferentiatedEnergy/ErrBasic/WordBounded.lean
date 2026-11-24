import UnforcedLeray.Short.PartI.Sub.PartI_T08_1

/-!
# Part I, task `PartI:T08/1/1` (`trainWordBounded_proof`): bounded word derivatives of the train

Source: `the November 2 reference manuscript`, lines 270-288 (`BUC`: all spatial
derivatives bounded on `[0, S]`). The Prop is `TrainWordBounded` in `Sub/PartI_T08_1.lean`.

Route: `IsBUCTrain.deriv_bound` at `S = s` bounds `‖D^l (tr.v s)‖` uniformly in `z`, with `l = |w|`.
The coordinate `g = fun x => tr.v s x k` satisfies `g = (EuclideanSpace.proj k) ∘ tr.v s`, so
`‖D^l g‖ ≤ ‖D^l (tr.v s)‖` (`ContinuousLinearMap.norm_iteratedFDeriv_comp_left`, `‖proj k‖ ≤ 1`).
Finally `|∂_w g(z)| ≤ ‖D^l g(z)‖` by `cylJetWord_proof`.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

theorem trainWordBounded_proof : UnforcedLeray.Short.PartI.TrainWordBounded := by
  intro ν c tr htr s hs w k
  obtain ⟨M0, hM0⟩ := IsBUCTrain.deriv_bound htr hs w.length
  have hv : ContDiff ℝ ∞ (tr.v s) := TrainErrorEquation.contDiff_slice tr.isTrain.smooth_v hs
  have hproj : ‖(EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
      simpa using PiLp.norm_apply_le x k)
  have hg : ContDiff ℝ ∞ (fun x => tr.v s x k) :=
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv
  have hj : ((w.length : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  refine ⟨M0, fun z => ?_⟩
  have hw := (cylJetWord_proof (fun x => tr.v s x k) hg w.length z).1 w rfl
  have hcomp : ‖iteratedFDeriv ℝ w.length (fun x => tr.v s x k) z‖ ≤
      ‖iteratedFDeriv ℝ w.length (tr.v s) z‖ := by
    have h := ContinuousLinearMap.norm_iteratedFDeriv_comp_left
      (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
      (f := tr.v s) (x := z) (n := w.length) hv.contDiffAt hj
    calc ‖iteratedFDeriv ℝ w.length (fun x => tr.v s x k) z‖
        = ‖iteratedFDeriv ℝ w.length
            ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) ∘ tr.v s) z‖ := rfl
      _ ≤ ‖(EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ *
            ‖iteratedFDeriv ℝ w.length (tr.v s) z‖ := h
      _ ≤ 1 * ‖iteratedFDeriv ℝ w.length (tr.v s) z‖ :=
            mul_le_mul_of_nonneg_right hproj (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ w.length (tr.v s) z‖ := one_mul _
  have hbound := hM0 s ⟨hs, le_rfl⟩ z
  show |B0151.derivWord w (fun x => tr.v s x k) z| ≤ M0
  calc |B0151.derivWord w (fun x => tr.v s x k) z|
      ≤ ‖Train.jet w.length (fun x => tr.v s x k) z‖ := hw
    _ = ‖iteratedFDeriv ℝ w.length (fun x => tr.v s x k) z‖ := rfl
    _ ≤ ‖iteratedFDeriv ℝ w.length (tr.v s) z‖ := hcomp
    _ ≤ M0 := hbound

end UnforcedLeray.Short.PartI
