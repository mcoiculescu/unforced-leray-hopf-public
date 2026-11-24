import UnforcedLeray.Short.PartI.Sub.PartI_T04_6_1
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.CurlRegularity

/-!
# `PartI:T04/6/1/1`: integrability of `ω(s)²` on the cell (source lines 285-287)

Pointwise `|curl u z| ≤ 2‖Du z‖` for a differentiable `u`, continuity of `ω(s)` from
`crContinuous`, and `ω² ≤ 4‖Dv‖²` with `‖Dv‖² ∈ L¹(cell)` from `hcls.jet_l2` at `j = 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- Pointwise bound `|curl u z| ≤ 2 ‖Du z‖` for a differentiable velocity slice. -/
theorem apCurl_abs_le_fderiv {u : Plane → Vec} (hdiff : Differentiable ℝ u) (z : Plane) :
    |Cyl.curl u z| ≤ 2 * ‖fderiv ℝ u z‖ := by
  have hk1 : Differentiable ℝ (fun w => u w 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).differentiable.comp hdiff
  have hk0 : Differentiable ℝ (fun w => u w 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).differentiable.comp hdiff
  have hfq : HasFDerivAt (fun w => u w 1)
      ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).comp (fderiv ℝ u z)) z :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt.comp z (hdiff z).hasFDerivAt
  have hfe : HasFDerivAt (fun w => u w 0)
      ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).comp (fderiv ℝ u z)) z :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt.comp z (hdiff z).hasFDerivAt
  have hQ : Cyl.partialQ (fun w => u w 1) z = fderiv ℝ u z ((1 : ℝ), (0 : ℝ)) 1 := by
    have e1 := Cyl.partialQ_eq_fderiv hk1 z
    rw [hfq.fderiv] at e1
    exact e1
  have hE : Cyl.partialEta (fun w => u w 0) z = fderiv ℝ u z ((0 : ℝ), (1 : ℝ)) 0 := by
    have e0 := Cyl.partialEta_eq_fderiv hk0 z
    rw [hfe.fderiv] at e0
    exact e0
  have hcurl : Cyl.curl u z =
      fderiv ℝ u z ((1 : ℝ), (0 : ℝ)) 1 - fderiv ℝ u z ((0 : ℝ), (1 : ℝ)) 0 := by
    show Cyl.partialQ (fun w => u w 1) z - Cyl.partialEta (fun w => u w 0) z = _
    rw [hQ, hE]
  have hw1 : ‖(((1 : ℝ), (0 : ℝ)) : Plane)‖ ≤ 1 := by simp [Prod.norm_def]
  have hw2 : ‖(((0 : ℝ), (1 : ℝ)) : Plane)‖ ≤ 1 := by simp [Prod.norm_def]
  have hc1 : |fderiv ℝ u z ((1 : ℝ), (0 : ℝ)) 1| ≤ ‖fderiv ℝ u z‖ := by
    rw [← Real.norm_eq_abs]
    refine (PiLp.norm_apply_le (fderiv ℝ u z ((1 : ℝ), (0 : ℝ))) 1).trans ?_
    calc ‖fderiv ℝ u z ((1 : ℝ), (0 : ℝ))‖ ≤ ‖fderiv ℝ u z‖ * ‖(((1 : ℝ), (0 : ℝ)) : Plane)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ u z‖ * 1 := mul_le_mul_of_nonneg_left hw1 (norm_nonneg _)
      _ = ‖fderiv ℝ u z‖ := mul_one _
  have hc2 : |fderiv ℝ u z ((0 : ℝ), (1 : ℝ)) 0| ≤ ‖fderiv ℝ u z‖ := by
    rw [← Real.norm_eq_abs]
    refine (PiLp.norm_apply_le (fderiv ℝ u z ((0 : ℝ), (1 : ℝ))) 0).trans ?_
    calc ‖fderiv ℝ u z ((0 : ℝ), (1 : ℝ))‖ ≤ ‖fderiv ℝ u z‖ * ‖(((0 : ℝ), (1 : ℝ)) : Plane)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ u z‖ * 1 := mul_le_mul_of_nonneg_left hw2 (norm_nonneg _)
      _ = ‖fderiv ℝ u z‖ := mul_one _
  rw [hcurl]
  calc |fderiv ℝ u z ((1 : ℝ), (0 : ℝ)) 1 - fderiv ℝ u z ((0 : ℝ), (1 : ℝ)) 0|
      ≤ |fderiv ℝ u z ((1 : ℝ), (0 : ℝ)) 1| + |fderiv ℝ u z ((0 : ℝ), (1 : ℝ)) 0| :=
        abs_sub _ _
    _ ≤ 2 * ‖fderiv ℝ u z‖ := by linarith

/-- `apEnstrophyIntegrable`: `ω(s)² ∈ L¹(cell)` for `s ∈ [0,T]`. -/
theorem apEnstrophyIntegrable : UnforcedLeray.Short.PartI.APEnstrophyIntegrable := by
  intro ν c T v p hν hc hcls s hs
  -- the slice `v s` is differentiable on the whole plane
  have hdiff : Differentiable ℝ (v s) := by
    intro w
    have h1 : DifferentiableWithinAt ℝ (fun x : ℝ × Plane => v x.1 x.2)
        (Icc 0 T ×ˢ (univ : Set Plane)) (s, w) :=
      hcls.classical.smooth_v.differentiableOn (by simp) _ ⟨hs, mem_univ w⟩
    have h2 : DifferentiableWithinAt ℝ (fun w' : Plane => ((s, w') : ℝ × Plane)) univ w :=
      DifferentiableAt.differentiableWithinAt
        (((differentiable_const s).prodMk differentiable_id) w)
    have h3 : DifferentiableWithinAt ℝ ((fun x : ℝ × Plane => v x.1 x.2) ∘
        fun w' : Plane => ((s, w') : ℝ × Plane)) univ w :=
      DifferentiableWithinAt.comp w h1 h2 (fun w' _ => ⟨hs, mem_univ w'⟩)
    exact differentiableWithinAt_univ.mp h3
  -- continuity of `z ↦ curl (v s) z`
  have hcont : ContinuousOn (fun x : ℝ × Plane => Cyl.curl (v x.1) x.2)
      (Icc 0 T ×ˢ (univ : Set Plane)) :=
    crContinuous hcls.pos hcls.classical.smooth_v
  have hcz : Continuous (fun z : Plane => Cyl.curl (v s) z) := by
    have hc' : ContinuousOn ((fun x : ℝ × Plane => Cyl.curl (v x.1) x.2) ∘
        (fun z : Plane => ((s, z) : ℝ × Plane))) univ :=
      hcont.comp (f := fun z : Plane => ((s, z) : ℝ × Plane))
        ((continuous_const.prodMk continuous_id).continuousOn)
        (fun z _ => ⟨hs, mem_univ z⟩)
    exact continuousOn_univ.mp hc'
  obtain ⟨K, hK⟩ := hcls.jet_l2 1
  have hI : IntegrableOn (fun z => ‖iteratedFDeriv ℝ 1 (v s) z‖ ^ 2) (Cyl.cell c) :=
    (hK s hs).1
  refine Integrable.mono' (hI.const_mul 4) (hcz.pow 2).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun z => ?_)
  have hp := apCurl_abs_le_fderiv hdiff z
  rw [norm_iteratedFDeriv_one, Real.norm_of_nonneg (sq_nonneg _)]
  have hsq := sq_abs (Cyl.curl (v s) z)
  nlinarith [abs_nonneg (Cyl.curl (v s) z), norm_nonneg (fderiv ℝ (v s) z)]

end UnforcedLeray.Short.PartI
