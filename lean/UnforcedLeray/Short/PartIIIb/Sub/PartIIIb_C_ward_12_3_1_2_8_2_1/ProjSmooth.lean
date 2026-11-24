import UnforcedLeray.Short.PartIIb.Sub.B1
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialPathSmooth
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialCutoffMainLimit

/-!
# A smooth representative `projSmooth` of the Leray-projected phase test

Source `the November 2 reference manuscript`
lines 1393-1400, 1409-1412.  For a phase test `Φ` the slice-wise Leray projection is
`𝔓Φ = Φ + ∇π` with `π` the (complex) Newton potential of the source `-div Φ`
(`lerayProjectedPhaseTest_eq_newtonPotentialGrad_ae`).  `π` is a genuinely smooth function of
`(τ, y)` (`contDiff_projectedPotentialRePath`), so `projSmooth Φ = Φ + ∇π` is a smooth
representative of `projTest P Φ`, and `L0T` can be applied to it classically.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete MeasureTheory
open scoped ContDiff

/-- The complex Newton potential `π = π_Re + i π_Im` of the Leray correction of `Φ`. -/
def projPot (Φ : ℝ × UnforcedLeray.Space → CVec3) : ℝ × UnforcedLeray.Space → ℂ :=
  fun z => (projectedPotentialRePath Φ z : ℂ) + Complex.I * (projectedPotentialImPath Φ z : ℂ)

/-- The smooth representative `𝔓Φ = Φ + ∇π` of the slice-wise Leray projection of `Φ`. -/
def projSmooth (Φ : ℝ × UnforcedLeray.Space → CVec3) : ℝ × UnforcedLeray.Space → CVec3 :=
  Φ + gradT (projPot Φ)

theorem contDiff_projPot {P : ℝ} {Φ : ℝ × UnforcedLeray.Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    ContDiff ℝ ∞ (projPot Φ) := by
  unfold projPot
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_projectedPotentialRePath hΦ)).add
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_projectedPotentialImPath hΦ)))

theorem dy_projPot {P : ℝ} {Φ : ℝ × UnforcedLeray.Space → CVec3} (hΦ : IsPhaseTest P Φ)
    (j : Fin 3) (z : ℝ × UnforcedLeray.Space) :
    dy j (projPot Φ) z = (fderiv ℝ (projectedPotentialRePath Φ) z (0, UnforcedLeray.coordinateVector j) : ℂ)
      + Complex.I * (fderiv ℝ (projectedPotentialImPath Φ) z (0, UnforcedLeray.coordinateVector j) : ℂ) := by
  have hR := (contDiff_projectedPotentialRePath hΦ).differentiable (by simp) z
  have hI := (contDiff_projectedPotentialImPath hΦ).differentiable (by simp) z
  have h1 : HasFDerivAt (projPot Φ)
      (Complex.ofRealCLM.comp (fderiv ℝ (projectedPotentialRePath Φ) z) +
        Complex.I • Complex.ofRealCLM.comp (fderiv ℝ (projectedPotentialImPath Φ) z)) z := by
    have a := Complex.ofRealCLM.hasFDerivAt.comp z hR.hasFDerivAt
    have b := (Complex.ofRealCLM.hasFDerivAt.comp z hI.hasFDerivAt).const_mul Complex.I
    exact a.add b
  unfold dy
  rw [h1.fderiv]
  simp

theorem spatialTestDerivative_slice {f : ℝ × UnforcedLeray.Space → ℝ} (hf : Differentiable ℝ f)
    (i : Fin 3) (τ : ℝ) (y : UnforcedLeray.Space) :
    UnforcedLeray.spatialTestDerivative i (fun y => f (τ, y)) y =
      fderiv ℝ f (τ, y) (0, UnforcedLeray.coordinateVector i) := by
  unfold UnforcedLeray.spatialTestDerivative
  let inc : UnforcedLeray.Space → ℝ × UnforcedLeray.Space := fun y => (τ, y)
  have hinc : HasFDerivAt inc
      (ContinuousLinearMap.prod 0 (ContinuousLinearMap.id ℝ UnforcedLeray.Space)) y := by
    simpa [inc] using (hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y)
  have hcomp := (hf (τ, y)).hasFDerivAt.comp y hinc
  change fderiv ℝ (f ∘ inc) y (UnforcedLeray.coordinateVector i) = _
  rw [hcomp.fderiv]
  simp [inc, ContinuousLinearMap.comp_apply]

/-- `projSmooth` is the identity plus the canonical Newton-gradient correction field. -/
theorem projSmooth_eq_add_correction {P : ℝ} {Φ : ℝ × UnforcedLeray.Space → CVec3}
    (hΦ : IsPhaseTest P Φ) (z : ℝ × UnforcedLeray.Space) :
    projSmooth Φ z = Φ z + projectedPotentialNewtonCorrectionField Φ z := by
  have hR := contDiff_projectedPotentialRePath hΦ
  have hI := contDiff_projectedPotentialImPath hΦ
  obtain ⟨τ, y⟩ := z
  simp only [projSmooth, Pi.add_apply, projectedPotentialNewtonCorrectionField, RieszLp.gradField]
  congr 1
  ext k
  simp only [gradT, dy_projPot hΦ, RieszLp.gradField]
  simp [spatialTestDerivative_slice (hR.differentiable (by simp)),
    spatialTestDerivative_slice (hI.differentiable (by simp)), Finset.sum_apply,
    EuclideanSpace.single_apply, RieszLp.ofReV_apply, RieszLp.ofImV_apply,
    UnforcedLeray.coordinateVector]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : k = x
  · subst h; simp; ring
  · simp [h, Pi.single_apply, Ne.symm h]

theorem contDiff_gradT {ψ : ℝ × UnforcedLeray.Space → ℂ} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (gradT ψ) := by
  unfold gradT dy
  refine ContDiff.sum fun j _ => ?_
  have hder : ContDiff ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => fderiv ℝ ψ z) :=
    hψ.fderiv_right (m := ∞) (by simp)
  exact (hder.clm_apply contDiff_const).smul contDiff_const

theorem contDiff_projSmooth {P : ℝ} {Φ : ℝ × UnforcedLeray.Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    ContDiff ℝ ∞ (projSmooth Φ) :=
  hΦ.smooth.add (contDiff_gradT (contDiff_projPot hΦ))

/-- `projSmooth Φ` is a smooth representative of `projTest P Φ`, slice by slice. -/
theorem projSmooth_slice_ae {P : ℝ} [Fact (0 < P)] {Φ : ℝ × UnforcedLeray.Space → CVec3}
    (hΦ : IsPhaseTest P Φ) (τ : ℝ) :
    (fun y => UnforcedLeray.Short.IIb.projTest P Φ (τ, y)) =ᵐ[volume]
      fun y => projSmooth Φ (τ, y) := by
  rw [UnforcedLeray.Short.IIb.projTest_of_isPhaseTest hΦ]
  filter_upwards [lerayProjectedPhaseTest_eq_newtonPotentialGrad_ae
    (UnforcedLeray.RieszLp.one_lt_of_holderConjugate UnforcedLeray.B0412.q0E_ne_top)
    (UnforcedLeray.PhaseSpace.conjExp_ne_top UnforcedLeray.B0412.one_lt_q0E) hΦ τ] with y hy
  rw [hy, projSmooth_eq_add_correction hΦ]
  simp [projectedPotentialNewtonCorrectionField, projectedPotentialRePath,
    projectedPotentialImPath, add_assoc]

end UnforcedLeray.Short.PartIIIb.Concrete
