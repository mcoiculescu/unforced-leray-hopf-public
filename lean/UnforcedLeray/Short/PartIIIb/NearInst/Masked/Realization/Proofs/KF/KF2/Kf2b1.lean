import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Sub2
import UnforcedLeray.Units.B0225.Pointwise

/-!
# `KF2b1` (source 3613): Fubini integrability of the Laplace integrand

Template: `B0225.integrable_lapRep`. The integrand `(w, t) ↦ e^{-μt} G(t, w)` is strongly
measurable; its `t`-slices are integrable on `A` (`G t` a.e. equal to `S(t)x ∈ L²`), and
`∫_A |S(t)x| ≤ |A|^{1/2} M e^{ωt} ‖x‖`, which is integrable in `t` on `(0, ∞)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.B0223 UnforcedLeray.Infra

theorem kf2b1 : KF2b1 := by
  intro P _ S μ hμ x G hG hGT A hA
  have hK : StronglyMeasurable (fun p : PSpace P × ℝ => Complex.exp (-(μ * p.2)) • G p.2 p.1) := by
    refine (Continuous.stronglyMeasurable (by fun_prop :
      Continuous fun p : PSpace P × ℝ => Complex.exp (-(μ * p.2)))).smul ?_
    exact hG.comp_measurable measurable_swap
  rw [integrable_prod_iff' hK.aestronglyMeasurable]
  have hb : 0 < μ.re - S.ω := sub_pos.2 hμ
  have hC0 : 0 ≤ (volume A).toReal ^ (1 - 1 / (2 : ℝ≥0∞).toReal) := by positivity
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 0 < t := ht
    exact ((B0225.integrableOn_of_memLp' (Lp.memLp (S.T t x)) hA).congr
      (ae_restrict_of_ae (hGT t ht').symm)).smul (Complex.exp (-(μ * t)))
  · refine Integrable.mono'
      ((exp_neg_integrableOn_Ioi 0 hb).const_mul
        ((volume A).toReal ^ (1 - 1 / (2 : ℝ≥0∞).toReal) * S.M * ‖x‖)) ?_ ?_
    · exact (hK.norm.integral_prod_left' (μ := volume.restrict A)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht' : 0 < t := ht
      have hnorm : ∀ w : PSpace P,
          ‖Complex.exp (-(μ * t)) • G t w‖ = Real.exp (-(μ.re * t)) * ‖G t w‖ := by
        intro w
        rw [norm_smul, Infra.ExpSemigroup.norm_cexp_neg_mul]
      have h2 : ∫ w in A, ‖Complex.exp (-(μ * t)) • G t w‖ ∂volume =
          Real.exp (-(μ.re * t)) * ∫ w in A, ‖G t w‖ ∂volume := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Eventually.of_forall hnorm)
      have h3 : ∫ w in A, ‖G t w‖ ∂volume = ∫ w in A, ‖(S.T t x : PSpace P → SpaceC) w‖ ∂volume :=
        integral_congr_ae (ae_restrict_of_ae ((hGT t ht').mono fun w hw => by simp only [hw]))
      have h4 := B0225.integral_norm_le_Lp (S.T t x) hA
      have h5 := S.norm_T_apply_le ht'.le x
      have hnn : 0 ≤ ∫ w in A, ‖Complex.exp (-(μ * t)) • G t w‖ ∂volume :=
        integral_nonneg fun _ => norm_nonneg _
      rw [Real.norm_of_nonneg hnn, h2, h3]
      calc Real.exp (-(μ.re * t)) * ∫ w in A, ‖(S.T t x : PSpace P → SpaceC) w‖ ∂volume
          ≤ Real.exp (-(μ.re * t)) *
              ((volume A).toReal ^ (1 - 1 / (2 : ℝ≥0∞).toReal) * (S.M * Real.exp (S.ω * t) * ‖x‖)) := by
            refine mul_le_mul_of_nonneg_left (h4.trans ?_) (Real.exp_pos _).le
            exact mul_le_mul_of_nonneg_left h5 hC0
        _ = (volume A).toReal ^ (1 - 1 / (2 : ℝ≥0∞).toReal) * S.M * ‖x‖ *
              Real.exp (-(μ.re - S.ω) * t) := by
            rw [show -(μ.re - S.ω) * t = -(μ.re * t) + S.ω * t by ring, Real.exp_add]
            ring

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
