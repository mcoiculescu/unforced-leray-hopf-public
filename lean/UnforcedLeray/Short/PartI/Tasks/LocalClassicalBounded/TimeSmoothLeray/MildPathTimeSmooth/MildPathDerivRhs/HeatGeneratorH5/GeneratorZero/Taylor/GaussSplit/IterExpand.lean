import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_7_1_1_1_1_1_2

/-!
# Part I, `PartI:T02/1/4/4/1/7/1/1/1/1/1/2/2`: coordinate expansion `HGIterExpand`

Source `the November 2 reference manuscript`, lines 261-288. For `f` smooth,
`∂_w f = w₁ ∂₁ f + w₂ ∂₂ f` by linearity of `fderiv f y` in `w`, and differentiating once more
(the coefficients `w₁, w₂` are constant in `y`) gives the second-order expansion.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane Vec2)

namespace HGIterAux

theorem decomp (w : Plane) :
    w = w.1 • ((1:ℝ), (0:ℝ)) + w.2 • ((0:ℝ), (1:ℝ)) := by
  ext <;> simp

theorem lin_decomp (L : Plane →L[ℝ] Vec2) (w : Plane) :
    L w = w.1 • L ((1:ℝ), (0:ℝ)) + w.2 • L ((0:ℝ), (1:ℝ)) := by
  conv_lhs => rw [decomp w]
  rw [map_add, map_smul, map_smul]

end HGIterAux

open HGIterAux in
theorem heatGaussSplit_iterExpand : UnforcedLeray.Short.PartI.HGIterExpand := by
  intro c _hc f hf x w
  have hsm := hf.smooth
  have d1 : Differentiable ℝ (Sob.iterD [((1:ℝ), (0:ℝ))] f) :=
    (Sob.contDiff_iterD hsm [((1:ℝ), (0:ℝ))]).differentiable (by simp)
  have d2 : Differentiable ℝ (Sob.iterD [((0:ℝ), (1:ℝ))] f) :=
    (Sob.contDiff_iterD hsm [((0:ℝ), (1:ℝ))]).differentiable (by simp)
  constructor
  · show fderiv ℝ f x w = w.1 • fderiv ℝ f x ((1:ℝ), (0:ℝ)) + w.2 • fderiv ℝ f x ((0:ℝ), (1:ℝ))
    exact lin_decomp (fderiv ℝ f x) w
  · have hfun : (fun y => fderiv ℝ f y w)
        = fun y => w.1 • Sob.iterD [((1:ℝ), (0:ℝ))] f y + w.2 • Sob.iterD [((0:ℝ), (1:ℝ))] f y :=
      funext fun y => lin_decomp (fderiv ℝ f y) w
    have hsum : fderiv ℝ (fun y => w.1 • Sob.iterD [((1:ℝ), (0:ℝ))] f y
          + w.2 • Sob.iterD [((0:ℝ), (1:ℝ))] f y) x
        = w.1 • fderiv ℝ (Sob.iterD [((1:ℝ), (0:ℝ))] f) x
          + w.2 • fderiv ℝ (Sob.iterD [((0:ℝ), (1:ℝ))] f) x :=
      (((d1 x).hasFDerivAt.const_smul w.1).add ((d2 x).hasFDerivAt.const_smul w.2)).fderiv
    show fderiv ℝ (fun y => fderiv ℝ f y w) x w = _
    rw [hfun, hsum, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, lin_decomp (fderiv ℝ (Sob.iterD [((1:ℝ), (0:ℝ))] f) x) w,
      lin_decomp (fderiv ℝ (Sob.iterD [((0:ℝ), (1:ℝ))] f) x) w]
    show _ = (w.1 * w.1) • fderiv ℝ (Sob.iterD [((1:ℝ), (0:ℝ))] f) x ((1:ℝ), (0:ℝ))
          + (w.1 * w.2) • (fderiv ℝ (Sob.iterD [((0:ℝ), (1:ℝ))] f) x ((1:ℝ), (0:ℝ))
              + fderiv ℝ (Sob.iterD [((1:ℝ), (0:ℝ))] f) x ((0:ℝ), (1:ℝ)))
          + (w.2 * w.2) • fderiv ℝ (Sob.iterD [((0:ℝ), (1:ℝ))] f) x ((0:ℝ), (1:ℝ))
    module

end UnforcedLeray.Short.PartI
