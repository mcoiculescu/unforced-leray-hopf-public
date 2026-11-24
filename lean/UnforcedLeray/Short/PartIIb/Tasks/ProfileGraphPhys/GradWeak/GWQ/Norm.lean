import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GLRot.GradEquivar
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_2

/-!
# `PartII-b:T10/7/1/2/4` (`GWQ`) helper: `√s Q_ε b ∈ H_r` from the `Y_r` bounds on `g_0, g_1`
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.GWQ

open UnforcedLeray UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

theorem theta_le (a b : ℝ) : ‖(a / Real.sqrt (a ^ 2 + b ^ 2) : ℝ)‖ₑ ≤ 1 := by
  rw [← ofReal_norm_eq_enorm]
  refine ENNReal.ofReal_le_one.2 ?_
  rw [Real.norm_eq_abs, abs_div]
  by_cases h0 : Real.sqrt (a ^ 2 + b ^ 2) = 0
  · rw [h0]; simp
  · have hp : 0 < Real.sqrt (a ^ 2 + b ^ 2) := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm h0)
    rw [abs_of_pos hp, div_le_one hp]
    exact Real.abs_le_sqrt (by nlinarith [sq_nonneg b])

theorem inHr_sqrtS {c ε r : ℝ} (hc : 0 < c) (hε : 0 < ε) (hr : 1 < r)
    {g0 g1 : ℝ × Space → CVec3} (hg0 : IsInYr (2 * ε * c) r g0) (hg1 : IsInYr (2 * ε * c) r g1)
    {Qb : CProf} (hQp : QPeriodic c (sqrtS Qb))
    (hQm : AEStronglyMeasurable (sqrtS Qb) (hMeas c r))
    (hE : NvC ε⁻¹ (sqrtS Qb) =ᵐ[volume] fun x : ℝ × Space =>
        (((x.2 0 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ)) • g0 x +
        (((x.2 1 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ)) • g1 x) :
    InHr c r (sqrtS Qb) := by
  have hr0 : 0 < r := by linarith
  have hP : 0 < 2 * ε * c := by positivity
  refine ⟨hQp, hQm, ?_⟩
  set f : ℝ × Space → CVec3 := fun x : ℝ × Space =>
        (((x.2 0 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ)) • g0 x +
        (((x.2 1 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ)) • g1 x with hf
  have hθ0 : Measurable fun x : ℝ × Space => (((x.2 0 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ)) := by
    fun_prop
  have hθ1 : Measurable fun x : ℝ × Space => (((x.2 1 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ)) := by
    fun_prop
  have hfm : AEStronglyMeasurable f volume :=
    (hθ0.aestronglyMeasurable.smul hg0.meas).add (hθ1.aestronglyMeasurable.smul hg1.meas)
  have hfin : phaseLpNorm (2 * ε * c) r f < ⊤ := by
    rw [gle_lt_top_iff _ r hP hr0 f hfm]
    have hpt : ∀ z, ‖f z‖ₑ ^ r ≤ 2 ^ (r - 1) * (‖g0 z‖ₑ ^ r + ‖g1 z‖ₑ ^ r) := fun z => by
      have h1 : ‖f z‖ₑ ≤ ‖g0 z‖ₑ + ‖g1 z‖ₑ := by
        refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [enorm_smul]
          calc _ ≤ 1 * ‖g0 z‖ₑ := by
                gcongr
                have := theta_le (z.2 0) (z.2 1)
                simpa [enorm_eq_nnnorm] using this
            _ = _ := one_mul _
        · rw [enorm_smul]
          calc _ ≤ 1 * ‖g1 z‖ₑ := by
                gcongr
                have := theta_le (z.2 1) (z.2 0)
                simpa [enorm_eq_nnnorm, add_comm] using this
            _ = _ := one_mul _
      exact (ENNReal.rpow_le_rpow h1 hr0.le).trans (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hr.le)
    have hu' := (gle_lt_top_iff _ r hP hr0 g0 hg0.meas).1 hg0.finite
    have hv' := (gle_lt_top_iff _ r hP hr0 g1 hg1.meas).1 hg1.finite
    have hmu := gle_aemeas_pow (2 * ε * c) r g0 hg0.meas
    have h2 : (2 : ℝ≥0∞) ^ (r - 1) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)
    calc ∫⁻ z, ‖f z‖ₑ ^ r ∂(gleMu (2 * ε * c))
        ≤ ∫⁻ z, 2 ^ (r - 1) * (‖g0 z‖ₑ ^ r + ‖g1 z‖ₑ ^ r) ∂(gleMu (2 * ε * c)) := lintegral_mono hpt
      _ = 2 ^ (r - 1) * (∫⁻ z, ‖g0 z‖ₑ ^ r ∂(gleMu (2 * ε * c)) +
            ∫⁻ z, ‖g1 z‖ₑ ^ r ∂(gleMu (2 * ε * c))) := by
          rw [lintegral_const_mul' _ _ h2, lintegral_add_left' hmu]
      _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 h2) (ENNReal.add_lt_top.2 ⟨hu', hv'⟩)
  have hnorm := phaseLpNorm_NvC hc hr0 hε (sqrtS Qb) hQp hQm
  rw [phaseLpNorm_congr_ae hE] at hnorm
  have hK : ENNReal.ofReal ((Real.pi * (ε⁻¹) ^ 2) ^ (1 / r)) ≠ 0 := by
    have : 0 < (Real.pi * (ε⁻¹) ^ 2) ^ (1 / r) := by positivity
    exact (ENNReal.ofReal_pos.2 this).ne'
  by_contra hcon
  have htop : hNorm c r (sqrtS Qb) = ⊤ := not_lt_top_iff.1 hcon
  rw [htop, ENNReal.mul_top hK] at hnorm
  exact absurd (hnorm ▸ hfin) (lt_irrefl _)

end UnforcedLeray.Short.IIb.GWQ
