import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_4_1.DerivY.Reduction

/-!
# Slice integration by parts (`SliceIntegrationByParts`)

Source `the November 2 reference manuscript`,
lines 2542-2551. The phase integral `phaseInt` is an iterated integral (phase outside, space
inside), so the identity is proved slice by slice in the phase variable and then integrated over
the phase cell by congruence. Periodicity hypotheses are not needed for this identity.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0412
open UnforcedLeray.Cons.C03.Concrete (Params IsSolTest pairF)

/-- Splitting a complex number times a real scalar into real and imaginary parts. -/
theorem sliceIBP_complex_split (z : ℂ) (f : ℝ) :
    z * (f : ℂ) = ((z.re * f : ℝ) : ℂ) + ((z.im * f : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [mul_comm]

/-- Real scalar component of the weak identity, with its integrability. -/
theorem sliceIBP_real_component {j : Fin 3} {F G : SpatialField}
    (hw : HasWeakSpatialDerivative j F G) {φ : Space → ℝ} (hφ : IsSpatialTest φ) (k : Fin 3) :
    Integrable (fun x => spatialTestDerivative j φ x * F x k) ∧
    Integrable (fun x => φ x * G x k) ∧
    ∫ x, spatialTestDerivative j φ x * F x k = -(∫ x, φ x * G x k) := by
  have hLI := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj k : Space →L[ℝ] ℝ)
    (hw.left_integrable φ hφ)
  have hRI := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj k : Space →L[ℝ] ℝ)
    (hw.right_integrable φ hφ)
  have hI := hw.identity φ hφ
  refine ⟨?_, ?_, ?_⟩
  · have := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integrable_comp (hw.left_integrable φ hφ)
    simpa [spatialTestDerivative] using this
  · have := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integrable_comp (hw.right_integrable φ hφ)
    simpa using this
  · calc ∫ x, spatialTestDerivative j φ x * F x k
        = ∫ x, (EuclideanSpace.proj k : Space →L[ℝ] ℝ) (spatialTestDerivative j φ x • F x) := by
          simp [spatialTestDerivative]
      _ = (EuclideanSpace.proj k : Space →L[ℝ] ℝ) (∫ x, spatialTestDerivative j φ x • F x) := hLI
      _ = (EuclideanSpace.proj k : Space →L[ℝ] ℝ) (-(∫ x, φ x • G x)) := by rw [hI]
      _ = -(∫ x, φ x * G x k) := by
          rw [map_neg, ← hRI]
          simp

/-- Complex scalar component of the weak identity (complex test `ψ`, real field components). -/
theorem sliceIBP_complex_component {j : Fin 3} {F G : SpatialField}
    (hw : HasWeakSpatialDerivative j F G) (k : Fin 3) {ψ : Space → ℂ}
    (hψs : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun x => fderiv ℝ ψ x (coordinateVector j) * ((F x k : ℝ) : ℂ)) ∧
    Integrable (fun x => ψ x * ((G x k : ℝ) : ℂ)) ∧
    ∫ x, fderiv ℝ ψ x (coordinateVector j) * ((F x k : ℝ) : ℂ) =
      -(∫ x, ψ x * ((G x k : ℝ) : ℂ)) := by
  have hdiff : Differentiable ℝ ψ := hψs.differentiable (by simp)
  have hdre : ∀ x v, fderiv ℝ (fun y => (ψ y).re) x v = (fderiv ℝ ψ x v).re := by
    intro x v
    have h2 := Complex.reCLM.hasFDerivAt.comp x (hdiff x).hasFDerivAt
    have h3 : (fun y => (ψ y).re) = Complex.reCLM ∘ ψ := by
      funext y
      simp
    rw [h3, h2.fderiv]
    simp
  have hdim : ∀ x v, fderiv ℝ (fun y => (ψ y).im) x v = (fderiv ℝ ψ x v).im := by
    intro x v
    have h2 := Complex.imCLM.hasFDerivAt.comp x (hdiff x).hasFDerivAt
    have h3 : (fun y => (ψ y).im) = Complex.imCLM ∘ ψ := by
      funext y
      simp
    rw [h3, h2.fderiv]
    simp
  have hreS : IsSpatialTest (fun y => (ψ y).re) := by
    refine ⟨?_, ?_⟩
    · have h := Complex.reCLM.contDiff.comp hψs
      simpa [Function.comp_def] using h
    · exact hψc.comp_left Complex.zero_re
  have himS : IsSpatialTest (fun y => (ψ y).im) := by
    refine ⟨?_, ?_⟩
    · have h := Complex.imCLM.contDiff.comp hψs
      simpa [Function.comp_def] using h
    · exact hψc.comp_left Complex.zero_im
  have hR := sliceIBP_real_component hw hreS k
  have hI := sliceIBP_real_component hw himS k
  unfold spatialTestDerivative at hR hI
  have hdec : ∀ x, fderiv ℝ ψ x (coordinateVector j) * ((F x k : ℝ) : ℂ) =
      ((fderiv ℝ (fun y => (ψ y).re) x (coordinateVector j) * F x k : ℝ) : ℂ) +
      ((fderiv ℝ (fun y => (ψ y).im) x (coordinateVector j) * F x k : ℝ) : ℂ) * Complex.I := by
    intro x
    rw [hdre, hdim]
    exact sliceIBP_complex_split _ _
  have hA : Integrable (fun x => fderiv ℝ ψ x (coordinateVector j) * ((F x k : ℝ) : ℂ)) := by
    have e : (fun x => fderiv ℝ ψ x (coordinateVector j) * ((F x k : ℝ) : ℂ)) = fun x =>
        ((fderiv ℝ (fun y => (ψ y).re) x (coordinateVector j) * F x k : ℝ) : ℂ) +
        ((fderiv ℝ (fun y => (ψ y).im) x (coordinateVector j) * F x k : ℝ) : ℂ) * Complex.I :=
      funext hdec
    rw [e]
    exact (hR.1.ofReal (𝕜 := ℂ)).add ((hI.1.ofReal (𝕜 := ℂ)).mul_const Complex.I)
  have hB : Integrable (fun x => ψ x * ((G x k : ℝ) : ℂ)) := by
    have e : (fun x => ψ x * ((G x k : ℝ) : ℂ)) = fun x =>
        ((((ψ x).re * G x k : ℝ)) : ℂ) + ((((ψ x).im * G x k : ℝ)) : ℂ) * Complex.I :=
      funext (fun x => sliceIBP_complex_split (ψ x) (G x k))
    rw [e]
    exact (hR.2.1.ofReal (𝕜 := ℂ)).add ((hI.2.1.ofReal (𝕜 := ℂ)).mul_const Complex.I)
  have hint : ∫ x, fderiv ℝ ψ x (coordinateVector j) * ((F x k : ℝ) : ℂ) =
      ((∫ x, fderiv ℝ (fun y => (ψ y).re) x (coordinateVector j) * F x k : ℝ) : ℂ) +
      ((∫ x, fderiv ℝ (fun y => (ψ y).im) x (coordinateVector j) * F x k : ℝ) : ℂ) * Complex.I := by
    have e : (fun x => fderiv ℝ ψ x (coordinateVector j) * ((F x k : ℝ) : ℂ)) = fun x =>
        ((fderiv ℝ (fun y => (ψ y).re) x (coordinateVector j) * F x k : ℝ) : ℂ) +
        ((fderiv ℝ (fun y => (ψ y).im) x (coordinateVector j) * F x k : ℝ) : ℂ) * Complex.I :=
      funext hdec
    have i1 : Integrable (fun x => ((fderiv ℝ (fun y => (ψ y).re) x (coordinateVector j) *
        F x k : ℝ) : ℂ)) := hR.1.ofReal (𝕜 := ℂ)
    have i2 : Integrable (fun x => ((fderiv ℝ (fun y => (ψ y).im) x (coordinateVector j) *
        F x k : ℝ) : ℂ) * Complex.I) := (hI.1.ofReal (𝕜 := ℂ)).mul_const Complex.I
    rw [e, integral_add i1 i2, integral_mul_const, integral_complex_ofReal,
      integral_complex_ofReal]
  have hint2 : ∫ x, ψ x * ((G x k : ℝ) : ℂ) =
      ((∫ x, (ψ x).re * G x k : ℝ) : ℂ) + ((∫ x, (ψ x).im * G x k : ℝ) : ℂ) * Complex.I := by
    have e : (fun x => ψ x * ((G x k : ℝ) : ℂ)) = fun x =>
        ((((ψ x).re * G x k : ℝ)) : ℂ) + ((((ψ x).im * G x k : ℝ)) : ℂ) * Complex.I :=
      funext (fun x => sliceIBP_complex_split (ψ x) (G x k))
    have i1 : Integrable (fun x => (((ψ x).re * G x k : ℝ) : ℂ)) := hR.2.1.ofReal (𝕜 := ℂ)
    have i2 : Integrable (fun x => (((ψ x).im * G x k : ℝ) : ℂ) * Complex.I) :=
      (hI.2.1.ofReal (𝕜 := ℂ)).mul_const Complex.I
    rw [e, integral_add i1 i2, integral_mul_const, integral_complex_ofReal,
      integral_complex_ofReal]
  refine ⟨hA, hB, ?_⟩
  rw [hint, hint2, hR.2.2, hI.2.2]
  push_cast
  ring

/-- The spatial derivative of a phase test, read in one component. -/
theorem sliceIBP_dy_apply {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (j : Fin 3)
    (t : ℝ) (k : Fin 3) (y : Space) :
    dy j Φ (t, y) k = fderiv ℝ (fun x : Space => Φ (t, x) k) y (coordinateVector j) := by
  have hdiff : Differentiable ℝ Φ := hΦ.smooth.differentiable (by simp)
  have hg : HasFDerivAt (fun x : Space => ((t, x) : ℝ × Space))
      (ContinuousLinearMap.inr ℝ ℝ Space) y :=
    (hasFDerivAt_const t y).prodMk (hasFDerivAt_id y)
  have h1 : HasFDerivAt (fun x : Space => Φ (t, x))
      ((fderiv ℝ Φ (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
    HasFDerivAt.comp y (hdiff (t, y)).hasFDerivAt hg
  have h2 : HasFDerivAt (fun x : Space => Φ (t, x) k)
      ((((EuclideanSpace.proj k : CVec3 →L[ℂ] ℂ).restrictScalars ℝ)).comp
        ((fderiv ℝ Φ (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space))) y :=
    HasFDerivAt.comp y (((EuclideanSpace.proj k : CVec3 →L[ℂ] ℂ).restrictScalars ℝ)).hasFDerivAt h1
  rw [h2.fderiv]
  simp [dy]

theorem sliceIBP_slice_contDiff {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    (t : ℝ) (k : Fin 3) :
    ContDiff ℝ ∞ (fun y : Space => Φ (t, y) k) := by
  have h1 : ContDiff ℝ ∞ (fun y : Space => Φ (t, y)) :=
    hΦ.smooth.comp (contDiff_const.prodMk contDiff_id)
  exact ((EuclideanSpace.proj k : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp h1

theorem sliceIBP_slice_compact {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    (t : ℝ) (k : Fin 3) :
    HasCompactSupport (fun y : Space => Φ (t, y) k) := by
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Space) R)
  intro y hy
  have hy' : R < ‖y‖ := by
    simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy
  simp [hR t y hy']

/-- The slice identity at a fixed phase `t`. -/
theorem sliceIBP_slice {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) {j : Fin 3}
    {Fs Gs : SpatialField} (hw : HasWeakSpatialDerivative j Fs Gs) (t : ℝ) :
    ∫ y, dotL (dy j Φ (t, y)) (realC (Fs y)) = ∫ y, dotL (Φ (t, y)) (realC (-(Gs y))) := by
  have hc : ∀ k : Fin 3,
      Integrable (fun y => dy j Φ (t, y) k * ((Fs y k : ℝ) : ℂ)) ∧
      Integrable (fun y => Φ (t, y) k * ((Gs y k : ℝ) : ℂ)) ∧
      ∫ y, dy j Φ (t, y) k * ((Fs y k : ℝ) : ℂ) =
        -(∫ y, Φ (t, y) k * ((Gs y k : ℝ) : ℂ)) := by
    intro k
    simp only [sliceIBP_dy_apply hΦ j t k]
    exact sliceIBP_complex_component hw k (sliceIBP_slice_contDiff hΦ t k)
      (sliceIBP_slice_compact hΦ t k)
  have hL : ∀ y, dotL (dy j Φ (t, y)) (realC (Fs y)) =
      ∑ k : Fin 3, dy j Φ (t, y) k * ((Fs y k : ℝ) : ℂ) := by
    intro y
    simp [dotL_apply, realC_apply]
  have hR : ∀ y, dotL (Φ (t, y)) (realC (-(Gs y))) =
      -∑ k : Fin 3, Φ (t, y) k * ((Gs y k : ℝ) : ℂ) := by
    intro y
    simp [dotL_apply, realC_apply, Finset.sum_neg_distrib]
  simp only [hL, hR]
  rw [integral_finsetSum _ (fun k _ => (hc k).1), integral_neg,
    integral_finsetSum _ (fun k _ => (hc k).2.1), ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun k _ => (hc k).2.2)

/-- **Slice integration by parts** (source 2542-2551), proved slice by slice. -/
theorem sliceIntegrationByParts_thm : SliceIntegrationByParts := by
  intro P hP j F G hFper hGper hFmem hGmem hFc hGc hw Φ hΦ
  unfold pairF UnforcedLeray.Cons.C03.Concrete.phaseInt
  congr 2
  funext t
  exact sliceIBP_slice hΦ (hw t) t

end UnforcedLeray.Short.PartIIIb.Concrete
