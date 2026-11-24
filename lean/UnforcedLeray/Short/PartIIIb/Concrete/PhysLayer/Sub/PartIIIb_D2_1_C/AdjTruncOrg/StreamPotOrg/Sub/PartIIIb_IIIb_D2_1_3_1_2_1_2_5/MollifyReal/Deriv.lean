import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_5.Defs

/-!
# Partial derivatives of mollifications (`pdir_mollify_eq`)

Source `the November 2 reference manuscript` lines 1351-1362, 1470-1480.
For a smooth compactly supported kernel `ρ` and an `L⁶` field `u` with `L²` weak partial
derivatives `D j`, the partial derivative of `mollify ρ u` is `mollify ρ (D j)`.

Proof: `mollify ρ u` is the convolution `u ⋆ ρ`, so its derivative falls on `ρ`
(`HasCompactSupport.hasFDerivAt_convolution_right`). The weak derivative identity is then applied
to the test function `y ↦ ρ (x - y)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Pointwise form of the mollification: `mollify ρ f x = ∫ y, ρ (x - y) • f y`. -/
theorem mollify_apply_sub (ρ : Space → ℝ) (f : Space → CVec3) (x : Space) :
    mollify ρ f x = ∫ y : Space, ρ (x - y) • f y := by
  have h := integral_sub_left_eq_self (μ := volume) (fun z : Space => ρ z • f (x - z)) x
  simp only [sub_sub_cancel] at h
  simp only [mollify]
  exact h.symm

/-- The mollification is the convolution `f ⋆ ρ` with the flipped scalar action. -/
theorem mollify_eq_convolution_flip (ρ : Space → ℝ) (f : Space → CVec3) :
    mollify ρ f = MeasureTheory.convolution f ρ
      ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3).flip) volume := by
  funext x
  rw [MeasureTheory.convolution_def, mollify_apply_sub]
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply]

/-- Derivative of the mollification in direction `j`, written as an integral. -/
theorem pdir_mollify_integral {ρ : Space → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ)
    {u : Space → CVec3} (hu : MemLp u 6 volume) (j : Fin 3) (x : Space) :
    pdir j (mollify ρ u) x
      = ∫ t : Space, (fderiv ℝ ρ (x - t) (EuclideanSpace.single j (1 : ℝ))) • u t := by
  have hu1 : LocallyIntegrable u volume := hu.locallyIntegrable (by norm_num)
  have hg1 : ContDiff ℝ 1 ρ := hρ.of_le (by simp)
  have hcont : Continuous (fderiv ℝ ρ) := hρ.continuous_fderiv (by simp)
  have hconv := hc.hasFDerivAt_convolution_right
    ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3).flip) hu1 hg1 x
  have hint := (hc.fderiv ℝ).convolutionExists_right
    ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3).flip.precompR Space)
    hu1 hcont x
  unfold pdir
  rw [mollify_eq_convolution_flip ρ u, hconv.fderiv, MeasureTheory.convolution_def,
    ContinuousLinearMap.integral_apply hint]
  simp only [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply]

/-- Partial derivatives of mollifications of weakly differentiable fields. -/
theorem pdir_mollify_eq {ρ : Space → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ) {u : Space → CVec3} {D : Fin 3 → Space → CVec3} (hu : MemLp u 6 volume) (hD : ∀ j, MemLp (D j) 2 volume) (hw : ∀ j, WeakDeriv j u (D j)) (j : Fin 3) : pdir j (mollify ρ u) = mollify ρ (D j) := by
  funext x
  have hφC : ContDiff ℝ ∞ (fun y : Space => ((ρ (x - y) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hρ.comp (contDiff_const.sub contDiff_id))
  have hφc : HasCompactSupport (fun y : Space => ((ρ (x - y) : ℝ) : ℂ)) :=
    (hc.comp_homeomorph (Homeomorph.subLeft x)).comp_left (map_zero Complex.ofRealCLM)
  have hwd := hw j (fun y : Space => ((ρ (x - y) : ℝ) : ℂ)) hφC hφc
  have hg : ∀ y : Space, HasFDerivAt (fun y : Space => ρ (x - y))
      ((fderiv ℝ ρ (x - y)).comp (-ContinuousLinearMap.id ℝ Space)) y := by
    intro y
    have h1 : HasFDerivAt (fun y : Space => x - y) (-ContinuousLinearMap.id ℝ Space) y :=
      (hasFDerivAt_id y).const_sub x
    exact ((hρ.differentiable (by simp)).differentiableAt.hasFDerivAt).comp y h1
  have hderiv : ∀ y : Space,
      fderiv ℝ (fun y : Space => ((ρ (x - y) : ℝ) : ℂ)) y (EuclideanSpace.single j (1 : ℝ))
        = (((-(fderiv ℝ ρ (x - y) (EuclideanSpace.single j (1 : ℝ)))) : ℝ) : ℂ) := by
    intro y
    have hF : HasFDerivAt (fun y : Space => ((ρ (x - y) : ℝ) : ℂ))
        (Complex.ofRealCLM.comp ((fderiv ℝ ρ (x - y)).comp (-ContinuousLinearMap.id ℝ Space))) y :=
      Complex.ofRealCLM.hasFDerivAt.comp y (hg y)
    rw [hF.fderiv]
    simp [ContinuousLinearMap.comp_apply]
  have h1 : ∀ y : Space,
      fderiv ℝ (fun y : Space => ((ρ (x - y) : ℝ) : ℂ)) y (EuclideanSpace.single j (1 : ℝ)) • u y
        = -((fderiv ℝ ρ (x - y) (EuclideanSpace.single j (1 : ℝ))) • u y) := by
    intro y
    rw [hderiv y, Complex.coe_smul, neg_smul]
  have h2 : ∀ y : Space, ((ρ (x - y) : ℝ) : ℂ) • D j y = ρ (x - y) • D j y :=
    fun y => Complex.coe_smul _ _
  have key : ∫ y : Space, (fderiv ℝ ρ (x - y) (EuclideanSpace.single j (1 : ℝ))) • u y
      = ∫ y : Space, ρ (x - y) • D j y := by
    have hw' := hwd
    simp only [h1, h2, integral_neg] at hw'
    exact neg_inj.mp hw'
  rw [pdir_mollify_integral hρ hc hu j x, mollify_apply_sub]
  exact key

end UnforcedLeray.Short.PartIIIb.Concrete
