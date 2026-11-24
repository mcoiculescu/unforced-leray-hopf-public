import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf4.Force

/-!
# Leaf (d) of `PartIII-a:T21/c3/3/1/1`: measurability of the mode forcings

Source `the November 2 reference manuscript` (SP) lines 2916-2925, 2991-2997.

The forcings `complModeForce` are `frameProj` of the explicit residuals `movOscRes + movEulerRes`;
all ingredients are jointly measurable in `(r, y)` (periodised sums are continuous in `r`
for fixed `y` and in `y` for fixed `r`; derivatives are limits of difference quotients; the
Biot-Savart kernel is measurable in its period).  The amplitudes are continuous in `r` by the
strong continuity of the flow (`FlowMeas.continuousOn_ampl'`).  Invertibility of the Gram
matrix along the path follows from the biorthogonality in `PerFrameFacts`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub ComplCouplingSub

namespace ComplFreeRateSub

theorem complForcingMeasurable (κ : PlanarFrameKernels) (P : PlanarData) (ν m b K : ℝ) (hν : 0 < ν) (hF : PerFrameFacts κ ν m b K) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ : ℝ) : UnforcedLeray.Short.IIIa.ComplFreeRateSub.ComplForcingMeasurable κ P ν m b K hν hF tr t₁ t₂ := by
  intro hκ _hP hm hb _hBUC ht1 hts hbt f w u hw
  have hν1 : ν ≤ 1 := by
    have h1 : 1 ≤ clockTheta ν t₂ := hb.trans hbt
    have ha : 1 ≤ clockA ν t₂ := one_le_clockA hν.le (ht1.trans hts)
    unfold clockTheta at h1
    have hpos : 0 < ν * clockA ν t₂ := by positivity
    have := (one_le_inv₀ hpos).1 h1
    nlinarith
  have hr0 : ∀ r ∈ Icc t₁ t₂, 0 ≤ r := fun r hr => ht1.trans hr.1
  have hbr : ∀ r ∈ Icc t₁ t₂, b ≤ clockTheta ν r := fun r hr =>
    hbt.trans (theta_anti hν (hr0 r hr) hr.2)
  have hd1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) := fun r hr =>
    one_le_cellLen_of_theta hν hν1 (hr0 r hr) (hb.trans (hbr r hr))
  have hdet : ∀ r ∈ Icc t₁ t₂,
      (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))).det ≠ 0 := by
    intro r hr hdz
    have h1 := hF.1 r (hr0 r hr) (hbr r hr) 0 0
    have hinv : (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ = 0 :=
      Matrix.nonsing_inv_apply_not_isUnit _ (by rw [isUnit_iff_ne_zero]; exact not_not.2 hdz)
    have h0 : ∀ x, perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) 0 x = 0 := by
      intro x
      unfold perLam
      rw [hinv]
      simp
    simp only [h0, zero_mul, integral_zero, ite_true] at h1
    exact zero_ne_one h1
  have hforce := fun j => Leaf4Aux.measurable_force_joint hκ hν ht1 hts hd1 P hF hdet tr j
  refine ⟨fun r hr j => ?_, ?_⟩
  · have h := (hforce j).comp ((measurable_const (a := r)).prodMk measurable_id)
    have h' : Measurable (fun y : ℝ × ℝ => complModeForce κ P (periodizedFrame κ ν m b K hν hF)
        tr r j y) := by
      have := h
      simpa only [Function.comp_def, Leaf4Aux.rho_eq hr, id] using this
    exact h'.aestronglyMeasurable
  · refine Finset.aemeasurable_fun_sum _ (fun j _ => AEMeasurable.mul ?_ ?_)
    · have hc := FlowMeas.continuousOn_ampl' κ hm hν ht1 hts hbt hF hd1 hdet hw j
      have h1 := ENNReal.continuous_ofReal.comp_continuousOn (continuous_norm.comp_continuousOn hc)
      exact (h1.aemeasurable measurableSet_Icc).mono_measure
        (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
    · have hm1 := Leaf4Aux.measurable_xNorm_family (t₂ := t₂) hν ht1 m
        (fun r => complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr
          (Leaf4Aux.rho t₁ t₂ r) j) (hforce j)
      refine hm1.aemeasurable.congr ?_
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun r hr => ?_)
      have hrI : r ∈ Icc t₁ t₂ := ⟨hr.1.le, hr.2⟩
      simp only [Leaf4Aux.dRho, Leaf4Aux.rho_eq hrI, dd]

end ComplFreeRateSub

end UnforcedLeray.Short.IIIa
