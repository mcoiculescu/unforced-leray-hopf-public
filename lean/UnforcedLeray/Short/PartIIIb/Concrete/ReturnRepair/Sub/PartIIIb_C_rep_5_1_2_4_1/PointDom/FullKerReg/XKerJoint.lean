import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.KerBounds
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_2_4.GradKEuler

/-!
# Joint regularity of the phase-lag kernel `xKer` in `(h, x)`

`xKer ν μ h x M = c(h) (T(h)²)⁻¹ gradKCon 1 ((√T(h))⁻¹ x) M` (parabolic scaling, `scale_gradK`),
`T(h) = ν(1 - e^{-h})`, so `(h, x) ↦ xKer ν μ h x M` is `C²` on `{h > 0}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray

theorem pdLam_pow_eq (h r : ℝ) : pdLam h ^ r = Real.exp (-(h / 2) * r) := by
  unfold pdLam; rw [← Real.exp_mul]

theorem pdLam_sq_eq (h : ℝ) : pdLam h ^ 2 = Real.exp (-h) := by
  unfold pdLam; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

theorem xKer_eq_scaled (ν μ h : ℝ) (hν : 0 < ν) (hh : 0 < h) (x : Space)
    (M : Matrix (Fin 3) (Fin 3) ℝ) :
    xKer ν μ h x M = (-(Real.exp (-(h / 2) * (2 * μ + 3)) - Real.exp (-(h / 2) * (2 * μ + 5)))) •
      ((ν * (1 - Real.exp (-h))) ^ 2)⁻¹ • gradKCon 1 ((Real.sqrt (ν * (1 - Real.exp (-h))))⁻¹ • x) M := by
  have hT : 0 < ν * (1 - pdLam h ^ 2) := by
    rw [pdLam_sq_eq]
    have : Real.exp (-h) < 1 := by
      have := Real.exp_lt_exp.2 (show -h < 0 by linarith)
      simpa using this
    exact mul_pos hν (by linarith)
  unfold xKer
  rw [scale_gradK _ hT, pdLam_pow_eq, pdLam_pow_eq, pdLam_sq_eq]

/-- Joint `C²` regularity of `(h, x) ↦ xKer ν μ h x M` on `h > 0`. -/
theorem xKer_jointC2 (ν μ : ℝ) (hν : 0 < ν) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    ContDiffOn ℝ 2 (fun p : ℝ × Space => xKer ν μ p.1 p.2 M) {p : ℝ × Space | 0 < p.1} := by
  have hopen : IsOpen {p : ℝ × Space | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have hcongr : ∀ p ∈ {p : ℝ × Space | 0 < p.1}, xKer ν μ p.1 p.2 M =
      (-(Real.exp (-(p.1 / 2) * (2 * μ + 3)) - Real.exp (-(p.1 / 2) * (2 * μ + 5)))) •
      ((ν * (1 - Real.exp (-p.1))) ^ 2)⁻¹ •
        gradKCon 1 ((Real.sqrt (ν * (1 - Real.exp (-p.1))))⁻¹ • p.2) M :=
    fun p hp => xKer_eq_scaled ν μ p.1 hν hp p.2 M
  refine ContDiffOn.congr ?_ hcongr
  have hc : ContDiff ℝ 2 (fun p : ℝ × Space =>
      -(Real.exp (-(p.1 / 2) * (2 * μ + 3)) - Real.exp (-(p.1 / 2) * (2 * μ + 5)))) := by
    refine ContDiff.neg (ContDiff.sub ?_ ?_)
    · exact Real.contDiff_exp.comp (((contDiff_fst.div_const 2).neg).mul contDiff_const)
    · exact Real.contDiff_exp.comp (((contDiff_fst.div_const 2).neg).mul contDiff_const)
  have hT : ContDiff ℝ 2 (fun p : ℝ × Space => ν * (1 - Real.exp (-p.1))) :=
    contDiff_const.mul (contDiff_const.sub (Real.contDiff_exp.comp contDiff_fst.neg))
  have hTpos : ∀ p ∈ {p : ℝ × Space | 0 < p.1}, 0 < ν * (1 - Real.exp (-p.1)) := by
    intro p hp
    have : Real.exp (-p.1) < 1 := by
      have := Real.exp_lt_exp.2 (show -p.1 < 0 by have : 0 < p.1 := hp; linarith)
      simpa using this
    exact mul_pos hν (by linarith)
  refine hc.contDiffOn.smul ?_
  have hinv : ContDiffOn ℝ 2 (fun p : ℝ × Space => ((ν * (1 - Real.exp (-p.1))) ^ 2)⁻¹)
      {p : ℝ × Space | 0 < p.1} := by
    refine ContDiffOn.inv ((hT.pow 2).contDiffOn) (fun p hp => ?_)
    exact (pow_pos (hTpos p hp) 2).ne'
  refine hinv.smul ?_
  have hsq : ContDiffOn ℝ 2 (fun p : ℝ × Space => (Real.sqrt (ν * (1 - Real.exp (-p.1))))⁻¹)
      {p : ℝ × Space | 0 < p.1} := by
    refine ContDiffOn.inv ?_ (fun p hp => (Real.sqrt_pos.2 (hTpos p hp)).ne')
    exact ContDiffOn.sqrt hT.contDiffOn (fun p hp => (hTpos p hp).ne')
  exact (gradK1_contDiff M).comp_contDiffOn (hsq.smul contDiff_snd.contDiffOn)

end UnforcedLeray.Short.PartIIIb.Concrete

end
