import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.SubKF3
import UnforcedLeray.Short.PartIIIa.T14_HeatGBound
import UnforcedLeray.Short.PartIIIa.SeparatedKernels

/-!
# `kf3TailFDeriv : KF3TailFDeriv` (source 3597-3601)

For `θ > 0`, `∂_j∫_θ^∞G_a(x) da = ∫_θ^∞ ∂_jG_a(x) da`.
Route: `hasFDerivAt_integral_of_dominated_of_fderiv_le` on `Ioi θ` with the derivative
`kf3tfG1 a z = curryFin1 (D¹G_a(z))`, dominated by `C₁ a^{-2}` (`heatGBound 1`, `exp ≤ 1`),
then `ContinuousLinearMap.integral_apply` at `e_j`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.IIIa

/-- `a ↦ G_a(z)` is continuous on `(0, ∞)`. -/
theorem kf3tf_heatG_continuousOn (z : Space) :
    ContinuousOn (fun a : ℝ => heatG a z) (Ioi 0) := by
  unfold heatG
  refine ContinuousOn.mul ?_ ?_
  · have hc : ContinuousOn (fun a : ℝ => 4 * Real.pi * a) (Ioi 0) := by fun_prop
    exact ContinuousOn.rpow_const hc
      (fun a ha => by
        have h : (0:ℝ) < a := ha
        left
        positivity)
  · refine Real.continuous_exp.comp_continuousOn ?_
    have hd : ContinuousOn (fun a : ℝ => 4 * a) (Ioi 0) := by fun_prop
    refine ContinuousOn.div continuousOn_const hd (fun a ha => ?_)
    exact mul_ne_zero (by norm_num) (Set.mem_Ioi.1 ha).ne'

/-- The derivative of `G_a` at `z` as a continuous linear map, through the curry isometry. -/
def kf3tfG1 (a : ℝ) (z : Space) : Space →L[ℝ] ℝ :=
  continuousMultilinearCurryFin1 ℝ Space ℝ (iteratedFDeriv ℝ 1 (heatG a) z)

theorem kf3tf_G1_eq (a : ℝ) (z : Space) : fderiv ℝ (heatG a) z = kf3tfG1 a z := by
  unfold kf3tfG1
  ext v
  simp [iteratedFDeriv_one_apply, continuousMultilinearCurryFin1_apply]

theorem kf3tf_G1_norm (a : ℝ) (z : Space) :
    ‖kf3tfG1 a z‖ = ‖iteratedFDeriv ℝ 1 (heatG a) z‖ := by
  unfold kf3tfG1
  exact LinearIsometryEquiv.norm_map _ _

theorem kf3tf_G1_continuousOn (z : Space) :
    ContinuousOn (fun a : ℝ => kf3tfG1 a z) (Ioi 0) := by
  have hI : ContinuousOn (fun a : ℝ => iteratedFDeriv ℝ 1 (heatG a) z) (Ioi 0) := by
    have e : (fun a : ℝ => iteratedFDeriv ℝ 1 (heatG a) z) =
        fun a : ℝ => iteratedFDeriv ℝ 1 (UnforcedLeray.Heat.kernel a) z := by
      funext a
      rw [heatG_eq_heatKernel]
    rw [e]
    exact UnforcedLeray.Kernels.continuousOn_iteratedFDeriv_heatKernel 1 z
  unfold kf3tfG1
  exact (LinearIsometryEquiv.continuous _).comp_continuousOn hI

theorem kf3tf_heatG_smooth (a : ℝ) : ContDiff ℝ ∞ (heatG a) := by
  rw [heatG_eq_heatKernel]
  exact UnforcedLeray.Kernels.heatKernel_smooth a

/-- **Leaf: the first derivative of the heat tail** (source 3597-3601). -/
theorem kf3TailFDeriv : KF3TailFDeriv := by
  intro θ hθ x j
  obtain ⟨C1, hC1, hC1b⟩ := heatGBound 1
  obtain ⟨C0, hC0, hC0b⟩ := heatGBound 0
  -- pointwise bound of the derivative, uniform in `z`
  have hb : ∀ a : ℝ, 0 < a → ∀ z : Space, ‖kf3tfG1 a z‖ ≤ C1 * a ^ (-(2:ℝ)) := by
    intro a ha z
    rw [kf3tf_G1_norm]
    have h := hC1b a ha z
    have e : -(3 + ((1:ℕ):ℝ)) / 2 = -(2:ℝ) := by norm_num
    rw [e] at h
    have hexp : Real.exp (-‖z‖ ^ 2 / (8 * a)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_div, neg_nonpos]
      positivity
    have hpos : 0 ≤ C1 * a ^ (-(2:ℝ)) := mul_nonneg hC1 (Real.rpow_nonneg ha.le _)
    calc ‖iteratedFDeriv ℝ 1 (heatG a) z‖
        ≤ C1 * a ^ (-(2:ℝ)) * Real.exp (-‖z‖ ^ 2 / (8 * a)) := h
      _ ≤ C1 * a ^ (-(2:ℝ)) * 1 := mul_le_mul_of_nonneg_left hexp hpos
      _ = C1 * a ^ (-(2:ℝ)) := mul_one _
  -- pointwise bound of the value, uniform in `z`
  have hb0 : ∀ a : ℝ, 0 < a → ∀ z : Space, ‖heatG a z‖ ≤ C0 * a ^ (-(3/2:ℝ)) := by
    intro a ha z
    have hz : ‖iteratedFDeriv ℝ 0 (heatG a) z‖ = ‖heatG a z‖ := norm_iteratedFDeriv_zero
    rw [← hz]
    have h := hC0b a ha z
    have e : -(3 + ((0:ℕ):ℝ)) / 2 = -(3/2:ℝ) := by norm_num
    rw [e] at h
    have hexp : Real.exp (-‖z‖ ^ 2 / (8 * a)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_div, neg_nonpos]
      positivity
    have hpos : 0 ≤ C0 * a ^ (-(3/2:ℝ)) := mul_nonneg hC0 (Real.rpow_nonneg ha.le _)
    calc ‖iteratedFDeriv ℝ 0 (heatG a) z‖
        ≤ C0 * a ^ (-(3/2:ℝ)) * Real.exp (-‖z‖ ^ 2 / (8 * a)) := h
      _ ≤ C0 * a ^ (-(3/2:ℝ)) * 1 := mul_le_mul_of_nonneg_left hexp hpos
      _ = C0 * a ^ (-(3/2:ℝ)) := mul_one _
  have hsub : Ioi θ ⊆ Ioi (0:ℝ) := Ioi_subset_Ioi hθ.le
  have hbd_int : IntegrableOn (fun a : ℝ => C1 * a ^ (-(2:ℝ))) (Ioi θ) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hθ).const_mul C1
  have hval_int0 : IntegrableOn (fun a : ℝ => C0 * a ^ (-(3/2:ℝ))) (Ioi θ) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hθ).const_mul C0
  have hpos : ∀ a ∈ Ioi θ, 0 < a := fun a ha => lt_trans hθ ha
  -- integrability of the value `a ↦ G_a(x)` on `(θ, ∞)`
  have hFint : ∀ z : Space, Integrable (fun a : ℝ => heatG a z) (volume.restrict (Ioi θ)) := by
    intro z
    refine Integrable.mono' hval_int0
      ((kf3tf_heatG_continuousOn z).mono hsub |>.aestronglyMeasurable measurableSet_Ioi) ?_
    exact (ae_restrict_mem measurableSet_Ioi).mono (fun a ha => hb0 a (hpos a ha) z)
  -- measurability of the derivative family
  have hF'meas : AEStronglyMeasurable (fun a : ℝ => kf3tfG1 a x) (volume.restrict (Ioi θ)) :=
    ((kf3tf_G1_continuousOn x).mono hsub).aestronglyMeasurable measurableSet_Ioi
  have hint : Integrable (fun a : ℝ => kf3tfG1 a x) (volume.restrict (Ioi θ)) := by
    refine Integrable.mono' hbd_int hF'meas ?_
    exact (ae_restrict_mem measurableSet_Ioi).mono (fun a ha => hb a (hpos a ha) x)
  have hHas : HasFDerivAt (fun z => ∫ a in Ioi θ, heatG a z)
      (∫ a in Ioi θ, kf3tfG1 a x) x := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F' := fun z a => kf3tfG1 a z)
      (bound := fun a : ℝ => C1 * a ^ (-(2:ℝ))) (s := univ) univ_mem ?_ (hFint x) hF'meas ?_
      hbd_int ?_
    · exact Filter.Eventually.of_forall (fun z => (kf3tf_heatG_continuousOn z).mono hsub
        |>.aestronglyMeasurable measurableSet_Ioi)
    · exact (ae_restrict_mem measurableSet_Ioi).mono (fun a ha z _ => hb a (hpos a ha) z)
    · refine ae_of_all _ (fun a z _ => ?_)
      have hd := ((kf3tf_heatG_smooth a).differentiable (by simp)) z
      rw [← kf3tf_G1_eq]
      exact hd.hasFDerivAt
  show fderiv ℝ (fun z => ∫ a in Ioi θ, heatG a z) x (coordinateVector j) = _
  rw [hHas.fderiv, ContinuousLinearMap.integral_apply hint]
  refine integral_congr_ae (ae_of_all _ (fun a => ?_))
  simp only
  rw [kf3tf_G1_eq]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
