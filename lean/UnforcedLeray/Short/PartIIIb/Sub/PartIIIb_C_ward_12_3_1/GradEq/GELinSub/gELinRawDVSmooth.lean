import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.Props

/-!
# `GELinRawDVSmooth`: the spatial derivatives `∂_j raw` are smooth and periodic (source 1217-1219)

Task `PartIII-b:C/ward/12/3/1/2/6/3`.  `rawDV p j τ y = fderiv (raw τ) y e_j` is the derivative
of the jointly smooth field `F(τ,y) = raw τ y` in the direction `(0, e_j)`; its joint smoothness
follows from the chain rule through `y ↦ (τ, y)` and `ContDiff.fderiv_right`.  Periodicity is
inherited from `raw (τ + P) = raw τ` (as functions of `y`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open scoped ContDiff

/-- The spatial partial derivative `∂_j` of a jointly smooth field, as a jointly smooth field
(`∂_j F(τ,y) = fderiv of y ↦ F(τ,y) in e_j`). -/
theorem gELinRawDVSmooth_partial {F : ℝ × UnforcedLeray.Space → UnforcedLeray.Space}
    (hF : ContDiff ℝ ∞ F) (j : Fin 3) :
    ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space =>
      fderiv ℝ (fun y => F (x.1, y)) x.2 (EuclideanSpace.single j 1)) := by
  have key : ∀ x : ℝ × UnforcedLeray.Space,
      fderiv ℝ (fun y => F (x.1, y)) x.2 (EuclideanSpace.single j 1) =
        fderiv ℝ F x (0, EuclideanSpace.single j 1) := by
    intro x
    have hFd : HasFDerivAt F (fderiv ℝ F x) (x.1, x.2) :=
      (hF.differentiable (by simp) x).hasFDerivAt
    have hg : HasFDerivAt (fun y : UnforcedLeray.Space => ((x.1, y) : ℝ × UnforcedLeray.Space))
        (ContinuousLinearMap.inr ℝ ℝ UnforcedLeray.Space) x.2 :=
      hasFDerivAt_prodMk_right x.1 x.2
    have hc := hFd.comp x.2 hg
    have hfd : fderiv ℝ (fun y => F (x.1, y)) x.2 =
        (fderiv ℝ F x).comp (ContinuousLinearMap.inr ℝ ℝ UnforcedLeray.Space) := hc.fderiv
    rw [hfd]
    rfl
  have hd : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (m := ∞) (by simp)
  have hfun : (fun x : ℝ × UnforcedLeray.Space =>
      fderiv ℝ (fun y => F (x.1, y)) x.2 (EuclideanSpace.single j 1)) =
      fun x => fderiv ℝ F x (0, EuclideanSpace.single j 1) := funext key
  rw [hfun]
  exact hd.clm_apply contDiff_const

theorem gELinRawDVSmooth : GELinRawDVSmooth := by
  intro p hp j
  obtain ⟨hC, hPer⟩ := hp
  refine ⟨?_, ?_⟩
  · exact gELinRawDVSmooth_partial hC j
  · intro τ y
    show fderiv ℝ (p.raw (τ + p.period)) y (EuclideanSpace.single j 1) =
      fderiv ℝ (p.raw τ) y (EuclideanSpace.single j 1)
    rw [show p.raw (τ + p.period) = p.raw τ from funext (hPer τ)]

end UnforcedLeray.Short.PartIIIb.Concrete
