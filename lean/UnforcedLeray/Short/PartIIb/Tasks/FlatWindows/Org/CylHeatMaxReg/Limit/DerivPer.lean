import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_4

/-!
# Part II-b, task `PartII-b:T13/1/4/4/2` (`ChmDerivPer`): derivatives of smooth periodic functions

Source of record: `the November 2 reference manuscript` (SP) lines 1933-1935.
For `w` smooth and `qShift c`-invariant, `cdv j w` is smooth and `qShift c`-invariant: the
translation `qShift c x = x + (0, (c, 0))` commutes with the derivative.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- The spatial derivative of a smooth function is smooth (derivative-part of `ChmDerivPer`). -/
theorem chmDerivPer_cdv_contDiff (u : Coord → ℂ) (hu : ContDiff ℝ ∞ u) (j : Fin 3) :
    ContDiff ℝ ∞ (cdv j u) := by
  unfold cdv
  exact (hu.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

/-- **Leaf 2 (derivatives of smooth periodic functions are smooth periodic, SP 1933-1935).** -/
theorem chmDerivPer : ChmDerivPer := by
  intro c w hw hper j
  refine ⟨chmDerivPer_cdv_contDiff w hw j, ?_⟩
  set a : Coord := ((0 : ℝ), ((c : ℝ), (0 : ℝ))) with ha
  have hq : ∀ y : Coord, qShift c y = y + a := by
    intro y
    exact Prod.ext (by simp [qShift, ha]) (Prod.ext (by simp [qShift, ha]) (by simp [qShift, ha]))
  have hfun : (fun y : Coord => w (y + a)) = w := by
    funext y
    rw [← hq y]
    exact hper y
  have key : ∀ x : Coord, fderiv ℝ w (qShift c x) = fderiv ℝ w x := by
    intro x
    have h1 := fderiv_comp_add_right (𝕜 := ℝ) (f := w) a (x := x)
    rw [hfun] at h1
    rw [hq x]
    exact h1.symm
  intro x
  unfold cdv
  rw [key x]

end UnforcedLeray.Short.IIb
