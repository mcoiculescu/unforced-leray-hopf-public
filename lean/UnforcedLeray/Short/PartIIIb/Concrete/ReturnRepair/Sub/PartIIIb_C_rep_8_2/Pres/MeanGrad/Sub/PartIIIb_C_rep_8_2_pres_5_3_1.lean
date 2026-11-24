import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGrad.Sub.PartIIIb_C_rep_8_2_pres_5_3

/-!
# `TrFd`: first-order WithLp transport (`PartIII-b:C/rep/8/2/pres/5/3/1`)

Source of record: `shorter-proof-2026-11-02.tex` lines 4784, 5455, 5267-5268.
`toLp ∘ DG ∘ ofLp` has operator norm at most `2‖DG‖`, since `‖toLp u‖₂ ≤ √3 ‖u‖_∞ ≤ 2‖u‖_∞`
and `‖ofLp h‖_∞ ≤ ‖h‖₂`.
-/

set_option autoImplicit false

noncomputable section

open WithLp

namespace UnforcedLeray.Short.PartIIIb.Concrete

open MeanScaleSub

theorem trFd : MeanScaleSub.TrFd := by
  unfold MeanScaleSub.TrFd
  intro G y hG
  let L : Space →L[ℝ] Vec3 :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toContinuousLinearMap
  let R : Vec3 →L[ℝ] Space :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  have hLapp : ∀ h : Space, L h = ofLp h := fun h => rfl
  have hRapp : ∀ u : Vec3, R u = toLp 2 u := fun u => rfl
  have hLb : ∀ h : Space, ‖L h‖ ≤ ‖h‖ := by
    intro h
    rw [hLapp]
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg h)).2 fun i => ?_
    exact PiLp.norm_apply_le h i
  have hRb : ∀ u : Vec3, ‖R u‖ ≤ 2 * ‖u‖ := by
    intro u
    rw [hRapp, EuclideanSpace.norm_eq, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have hi : ∀ i, ‖u i‖ ≤ ‖u‖ := fun i => norm_le_pi_norm u i
    calc ∑ i, ‖(toLp 2 u : Space) i‖ ^ 2 ≤ ∑ _i : Fin 3, ‖u‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hi i) 2
      _ = 3 * ‖u‖ ^ 2 := by simp
      _ ≤ (2 * ‖u‖) ^ 2 := by nlinarith [norm_nonneg u]
  have hG' : HasFDerivAt G (fderiv ℝ G (ofLp y)) (L y) := hG.hasFDerivAt
  have hd : HasFDerivAt (fun y' : Space => R (G (L y'))) (R.comp ((fderiv ℝ G (ofLp y)).comp L)) y :=
    R.hasFDerivAt.comp y (hG'.comp y L.hasFDerivAt)
  have hfd : fderiv ℝ (fun y' : Space => toLp 2 (G (ofLp y'))) y =
      R.comp ((fderiv ℝ G (ofLp y)).comp L) := hd.fderiv
  rw [hfd]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  have h1 := hRb ((fderiv ℝ G (ofLp y)) (L h))
  have h2 := (fderiv ℝ G (ofLp y)).le_opNorm (L h)
  have h3 := hLb h
  have h4 : 0 ≤ ‖fderiv ℝ G (ofLp y)‖ := norm_nonneg _
  have h5 := mul_le_mul_of_nonneg_left h3 h4
  calc ‖R ((fderiv ℝ G (ofLp y)) (L h))‖ ≤ 2 * ‖(fderiv ℝ G (ofLp y)) (L h)‖ := h1
    _ ≤ 2 * (‖fderiv ℝ G (ofLp y)‖ * ‖L h‖) := mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ ≤ 2 * ‖fderiv ℝ G (ofLp y)‖ * ‖h‖ := by nlinarith [h5]

end UnforcedLeray.Short.PartIIIb.Concrete
