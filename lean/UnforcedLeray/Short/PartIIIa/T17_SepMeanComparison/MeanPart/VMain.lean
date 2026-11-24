import UnforcedLeray.Short.PartIIIa.T17_SepMeanComparison.MeanPart.VDiff

/-!
# Mean part helper: `HasFDerivAt` of the `sepVmu0` integral (T17/2)
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem mp_tn_integrable (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hint : Integrable (fun w : (ℝ × ℝ) × ℝ => tensorNorm (G w.1 w.2)) volume) :
    Integrable (fun p : ℝ × ((ℝ × ℝ) × ℝ) => tensorNorm (G p.2.1 p.2.2)) mpRho2 := by
  have h := (integrable_const (1 : ℝ) (μ := volume.restrict (Ioo (0 : ℝ) 1))).mul_prod hint
  refine h.congr (Eventually.of_forall fun p => ?_)
  simp

theorem mp_V_diff (hK : SepKernelBounds) (μ : ℂ) (hμ : -(1 / 4) < μ.re) (ρo ρi : ℝ) (hρo : 0 ≤ ρo)
    (hρ : ρo < ρi) (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j)
    (hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0)
    (hint : Integrable (fun w : (ℝ × ℝ) × ℝ => tensorNorm (G w.1 w.2)) volume)
    (xo : Space) (hxo : ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)) (i : Fin 3) :
    HasFDerivAt (fun x => ∫ p, mpVF μ G p x i ∂mpRho2) (∫ p, mpVF' μ G p xo i ∂mpRho2) xo ∧
      (∀ x ∈ Metric.ball xo ((ρi - ρo) / 2), Integrable (fun p => mpVF μ G p x i) mpRho2) ∧
      Integrable (fun p => mpVF' μ G p xo i) mpRho2 := by
  obtain ⟨b0, b1, hb0, hb1, hpt⟩ := mp_V_pointwise hK
  set D1 := (ρi - ρo) / 2 with hD1
  have hD1pos : 0 < D1 := by rw [hD1]; linarith
  have hTn := mp_tn_integrable G hint
  have hI0 : Integrable (fun p : ℝ × ((ℝ × ℝ) × ℝ) =>
      b0 * D1 ^ (-4 : ℝ) * tensorNorm (G p.2.1 p.2.2)) mpRho2 := hTn.const_mul _
  have hI1 : Integrable (fun p : ℝ × ((ℝ × ℝ) × ℝ) =>
      b1 * D1 ^ (-5 : ℝ) * tensorNorm (G p.2.1 p.2.2)) mpRho2 := hTn.const_mul _
  have hint0 : ∀ x ∈ Metric.ball xo D1, Integrable (fun p => mpVF μ G p x i) mpRho2 := by
    intro x hx
    refine Integrable.mono' hI0 (mpVF_measurable μ G hGm x i).aestronglyMeasurable ?_
    filter_upwards [mpRho2_ae_mem] with p hp
    have hxn : ‖xo - x‖ < D1 := by
      rw [← dist_eq_norm, dist_comm]; exact hx
    exact (hpt μ hμ ρo ρi hρo hρ G hGs xo x hxo hxn p hp i).1
  have hint1 : Integrable (fun p => mpVF' μ G p xo i) mpRho2 := by
    refine Integrable.mono' hI1 (mpVF'_measurable μ G hGm xo i).aestronglyMeasurable ?_
    filter_upwards [mpRho2_ae_mem] with p hp
    exact (hpt μ hμ ρo ρi hρo hρ G hGs xo xo hxo (by rw [sub_self, norm_zero]; exact hD1pos) p hp i).2
  refine ⟨?_, hint0, hint1⟩
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x p => mpVF μ G p x i)
    (F' := fun x p => mpVF' μ G p x i) (μ := mpRho2) (bound := fun p =>
      b1 * D1 ^ (-5 : ℝ) * tensorNorm (G p.2.1 p.2.2)) (Metric.ball_mem_nhds xo hD1pos) ?_ (hint0 xo (Metric.mem_ball_self hD1pos))
    (mpVF'_measurable μ G hGm xo i).aestronglyMeasurable ?_ hI1 ?_
  · exact Eventually.of_forall fun x => (mpVF_measurable μ G hGm x i).aestronglyMeasurable
  · filter_upwards [mpRho2_ae_mem] with p hp x hx
    have hxn : ‖xo - x‖ < D1 := by
      rw [← dist_eq_norm, dist_comm]; exact hx
    exact (hpt μ hμ ρo ρi hρo hρ G hGs xo x hxo hxn p hp i).2
  · filter_upwards [mpRho2_ae_mem] with p hp x hx
    have hxn : ‖xo - x‖ < D1 := by
      rw [← dist_eq_norm, dist_comm]; exact hx
    by_cases hw : Real.sqrt (p.2.1.1 ^ 2 + p.2.1.2 ^ 2) ≤ ρo
    · have hgap := mp_gap ρo ρi xo x hxo p.1 hp p.2 hw
      have hnorm : D1 ≤ ‖x - p.1 • mpV3 p.2‖ := by
        refine le_trans ?_ (rho_le_norm _)
        rw [hD1]; linarith
      have hne : x - p.1 • mpV3 p.2 ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hnorm; linarith
      exact mpVF_hasFDerivAt μ G p x hne i
    · push_neg at hw
      have h0 : G p.2.1 p.2.2 = 0 := hGs _ _ hw
      have hf : (fun x => mpVF μ G p x i) = fun _ => 0 := funext fun x => mpVF_zero μ G p h0 x i
      rw [hf, mpVF'_zero μ G p h0]
      exact hasFDerivAt_const _ _

end UnforcedLeray.Short.IIIa

end
