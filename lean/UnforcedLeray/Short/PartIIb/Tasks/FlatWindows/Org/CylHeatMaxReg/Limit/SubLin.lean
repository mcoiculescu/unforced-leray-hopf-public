import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_4

/-!
# Part II-b, task `PartII-b:T13/1/4/4/1` (`ChmSubLin`): linearity on nice functions

Source of record: `the November 2 reference manuscript` (SP) lines 1933-1935.
Four parts: differences of `ChmNice` functions are `ChmNice`; the spatial derivatives and
`chmRhs ν` are additive. Differentiability of smooth functions gives the derivative-of-difference
identities.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- Smooth functions on `Coord` are differentiable. -/
theorem chmSubLin_diff (u : Coord → ℂ) (hu : ContDiff ℝ ∞ u) : Differentiable ℝ u :=
  hu.differentiable (by simp)

/-- The spatial derivative of a smooth function is smooth. -/
theorem chmSubLin_cdv_contDiff (u : Coord → ℂ) (hu : ContDiff ℝ ∞ u) (j : Fin 3) :
    ContDiff ℝ ∞ (cdv j u) := by
  unfold cdv
  exact (hu.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

/-- Spatial derivatives commute with differences of differentiable functions. -/
theorem chmSubLin_cdv_sub (u v : Coord → ℂ) (hu : Differentiable ℝ u) (hv : Differentiable ℝ v)
    (j : Fin 3) : cdv j (fun x => u x - v x) = fun x => cdv j u x - cdv j v x := by
  funext x
  unfold cdv
  rw [fderiv_fun_sub (hu x) (hv x)]
  rfl

/-- **Leaf 1 (linearity on nice functions, SP 1933-1935).** -/
theorem chmSubLin : ChmSubLin := by
  intro r c hr w w' hw hw'
  have hsub : ∀ j : Fin 3, cdv j (fun x => w x - w' x) = fun x => cdv j w x - cdv j w' x :=
    fun j => chmSubLin_cdv_sub w w' (chmSubLin_diff w hw.smooth) (chmSubLin_diff w' hw'.smooth) j
  have hb : ∀ i j : Fin 3, cdv i (cdv j (fun x => w x - w' x)) =
      fun x => cdv i (cdv j w) x - cdv i (cdv j w') x := by
    intro i j
    rw [hsub j]
    exact chmSubLin_cdv_sub (cdv j w) (cdv j w')
      (chmSubLin_diff _ (chmSubLin_cdv_contDiff w hw.smooth j))
      (chmSubLin_diff _ (chmSubLin_cdv_contDiff w' hw'.smooth j)) i
  have hm : ∀ u : Coord → ℂ, ContDiff ℝ ∞ u → AEStronglyMeasurable u (cylMeas c) :=
    fun u hu => hu.continuous.aestronglyMeasurable
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := ENNReal.one_le_ofReal.2 hr.le
  refine ⟨?_, hsub, hb, ?_⟩
  · refine ⟨hw.smooth.sub hw'.smooth, ?_, ?_, ?_, ?_⟩
    · intro x
      show w (qShift c x) - w' (qShift c x) = w x - w' x
      rw [hw.periodic x, hw'.periodic x]
    · have h := eLpNorm_sub_le (hm w hw.smooth) (hm w' hw'.smooth) hone
      exact lt_of_le_of_lt h (ENNReal.add_lt_top.2 ⟨hw.mem0, hw'.mem0⟩)
    · intro j
      rw [hsub j]
      have h := eLpNorm_sub_le (hm _ (chmSubLin_cdv_contDiff w hw.smooth j))
        (hm _ (chmSubLin_cdv_contDiff w' hw'.smooth j)) hone
      exact lt_of_le_of_lt h (ENNReal.add_lt_top.2 ⟨hw.mem1 j, hw'.mem1 j⟩)
    · intro j k
      rw [hb j k]
      have h := eLpNorm_sub_le (hm _ (chmSubLin_cdv_contDiff _ (chmSubLin_cdv_contDiff w hw.smooth k) j))
        (hm _ (chmSubLin_cdv_contDiff _ (chmSubLin_cdv_contDiff w' hw'.smooth k) j)) hone
      exact lt_of_le_of_lt h (ENNReal.add_lt_top.2 ⟨hw.mem2 j k, hw'.mem2 j k⟩)
  · intro ν
    funext x
    show chmRhs ν (fun x => w x - w' x) x = chmRhs ν w x - chmRhs ν w' x
    have e0 : cdv 0 (fun x => w x - w' x) x = cdv 0 w x - cdv 0 w' x := congrFun (hsub 0) x
    have e11 : cdv 1 (cdv 1 (fun x => w x - w' x)) x =
        cdv 1 (cdv 1 w) x - cdv 1 (cdv 1 w') x := congrFun (hb 1 1) x
    have e22 : cdv 2 (cdv 2 (fun x => w x - w' x)) x =
        cdv 2 (cdv 2 w) x - cdv 2 (cdv 2 w') x := congrFun (hb 2 2) x
    unfold chmRhs
    rw [e0, e11, e22]
    ring

end UnforcedLeray.Short.IIb
