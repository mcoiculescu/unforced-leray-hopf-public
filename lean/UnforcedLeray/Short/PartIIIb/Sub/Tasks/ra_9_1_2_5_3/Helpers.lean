import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1_2_5

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.T53

/-- The open chart domain `{s > 0}`. -/
theorem isOpen_U : IsOpen (Ioi 0 ×ˢ univ : Set Chart) := isOpen_Ioi.prod isOpen_univ

/-- Partial derivative in the second factor of a chart function, as a composition. -/
theorem partial_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Chart → E)
    (s : ℝ) (y : ℝ × ℝ) (hF : DifferentiableAt ℝ F (s, y)) :
    fderiv ℝ (fun x => F (s, x)) y
      = (fderiv ℝ F (s, y)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) := by
  have h1 : HasFDerivAt (fun x : ℝ × ℝ => (s, x)) (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) y :=
    hasFDerivAt_prodMk_right s y
  exact (hF.hasFDerivAt.comp y h1).fderiv

/-- The partial derivative in the spatial variable of a `C^5` chart function is `C^4` on `{s > 0}`. -/
theorem partial_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Chart → E)
    (hF : ContDiffOn ℝ 5 F (Ioi 0 ×ˢ univ)) :
    ContDiffOn ℝ 4 (fun p : Chart => fderiv ℝ (fun x => F (p.1, x)) p.2) (Ioi 0 ×ˢ univ) := by
  have h1 : ContDiffOn ℝ 4 (fun q : Chart => fderiv ℝ F q) (Ioi 0 ×ˢ univ) :=
    hF.fderiv_of_isOpen isOpen_U (by norm_num)
  have h2 : ContDiffOn ℝ 4
      (fun q : Chart => (fderiv ℝ F q).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)))
      (Ioi 0 ×ˢ univ) :=
    h1.clm_comp contDiffOn_const
  refine h2.congr ?_
  intro p hp
  have hd : DifferentiableAt ℝ F p :=
    ((hF p hp).differentiableWithinAt (by norm_num)).differentiableAt (isOpen_U.mem_nhds hp)
  exact partial_eq F p.1 p.2 hd

/-- Joint smoothness of `V_j` on `{s > 0}`. -/
theorem Vj_contDiffOn (ν : ℝ) (hν : 0 < ν) (j : ℤ) :
    ContDiffOn ℝ 5 (fun q : Chart => Vj ν q.1 j q.2) (Ioi 0 ×ˢ univ) := by
  have hA : ContDiff ℝ 5 (fun q : Chart => ageA ν q.1) := by
    unfold ageA; fun_prop
  have hAne : ∀ q ∈ (Ioi 0 ×ˢ univ : Set Chart), ageA ν q.1 ≠ 0 := by
    intro q hq
    have h0 : 0 < q.1 := hq.1
    have : 0 < 1 + ν * q.1 := by have := mul_pos hν h0; linarith
    unfold ageA
    exact ne_of_gt this
  have hinv : ContDiffOn ℝ 5 (fun q : Chart => (ageA ν q.1 ^ 2)⁻¹) (Ioi 0 ×ˢ univ) :=
    ((hA.pow 2).contDiffOn).inv (fun q hq => pow_ne_zero 2 (hAne q hq))
  have hNum : ContDiff ℝ 5 (fun q : Chart => -(sq2 (xj ν j q.2))) := by
    unfold sq2 xj; fun_prop
  have hDen : ContDiffOn ℝ 5 (fun q : Chart => 4 * ageA ν q.1) (Ioi 0 ×ˢ univ) :=
    (contDiff_const.mul hA).contDiffOn
  have hdivq : ContDiffOn ℝ 5
      (fun q : Chart => -(sq2 (xj ν j q.2)) / (4 * ageA ν q.1)) (Ioi 0 ×ˢ univ) :=
    hNum.contDiffOn.div hDen (fun q hq => mul_ne_zero (by norm_num) (hAne q hq))
  have hexp : ContDiffOn ℝ 5
      (fun q : Chart => Real.exp (-(sq2 (xj ν j q.2)) / (4 * ageA ν q.1))) (Ioi 0 ×ˢ univ) :=
    Real.contDiff_exp.comp_contDiffOn hdivq
  have hJ : ContDiff ℝ 5 (fun q : Chart => Jrot (xj ν j q.2)) := by
    unfold Jrot xj; fun_prop
  have hc := hinv.mul hexp
  exact hc.smul hJ.contDiffOn

/-- Joint smoothness of `ψ_j` on `{s > 0}`. -/
theorem psij_contDiffOn (ν : ℝ) (hν : 0 < ν) (j : ℤ) :
    ContDiffOn ℝ 5 (fun q : Chart => psij ν q.1 j q.2) (Ioi 0 ×ˢ univ) := by
  have hA : ContDiff ℝ 5 (fun q : Chart => ageA ν q.1) := by
    unfold ageA; fun_prop
  have hAne : ∀ q ∈ (Ioi 0 ×ˢ univ : Set Chart), ageA ν q.1 ≠ 0 := by
    intro q hq
    have h0 : 0 < q.1 := hq.1
    have : 0 < 1 + ν * q.1 := by have := mul_pos hν h0; linarith
    unfold ageA
    exact ne_of_gt this
  have hinv : ContDiffOn ℝ 5 (fun q : Chart => (ageA ν q.1)⁻¹) (Ioi 0 ×ˢ univ) :=
    hA.contDiffOn.inv (fun q hq => hAne q hq)
  have hNum : ContDiff ℝ 5 (fun q : Chart => -(sq2 (xj ν j q.2))) := by
    unfold sq2 xj; fun_prop
  have hDen : ContDiffOn ℝ 5 (fun q : Chart => 4 * ageA ν q.1) (Ioi 0 ×ˢ univ) :=
    (contDiff_const.mul hA).contDiffOn
  have hdivq : ContDiffOn ℝ 5
      (fun q : Chart => -(sq2 (xj ν j q.2)) / (4 * ageA ν q.1)) (Ioi 0 ×ˢ univ) :=
    hNum.contDiffOn.div hDen (fun q hq => mul_ne_zero (by norm_num) (hAne q hq))
  have hexp : ContDiffOn ℝ 5
      (fun q : Chart => Real.exp (-(sq2 (xj ν j q.2)) / (4 * ageA ν q.1))) (Ioi 0 ×ˢ univ) :=
    Real.contDiff_exp.comp_contDiffOn hdivq
  have hc : ContDiffOn ℝ 5
      (fun q : Chart => -2 * (ageA ν q.1)⁻¹ * Real.exp (-(sq2 (xj ν j q.2)) / (4 * ageA ν q.1)))
      (Ioi 0 ×ˢ univ) :=
    ((contDiffOn_const (c := (-2 : ℝ))).mul hinv).mul hexp
  exact hc

end UnforcedLeray.Short.PartIIIb.Concrete.T53
