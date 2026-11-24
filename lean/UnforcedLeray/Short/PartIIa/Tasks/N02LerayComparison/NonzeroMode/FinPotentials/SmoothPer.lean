import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N02_4_4

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- The mode factor `e^{2π i n q / c}` is `c`-periodic in `q`. -/
theorem nzfp_exp_qperiod (c : ℝ) (hc : 0 < c) (n : ℤ) (q : ℝ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((q + c : ℝ) : ℂ) / (c : ℂ)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ)) := by
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have h : 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((q + c : ℝ) : ℂ) / (c : ℂ) =
      2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ) +
        (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    field_simp
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem nzFpSmoothPer : NzFpSmoothPer := by
  intro c hc M g hg
  constructor
  · unfold nzModeSum
    apply ContDiff.sum
    intro n hn
    have hgn := hg n hn
    have hq : ContDiff ℝ ∞ (fun x : Profile => ((x.2.1 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_fst.comp contDiff_snd)
    have hgq : ContDiff ℝ ∞ (fun x : Profile => g n (x.1, x.2.2)) :=
      hgn.comp (contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd))
    have hE : ContDiff ℝ ∞ (fun x : Profile =>
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((x.2.1 : ℝ) : ℂ) / (c : ℂ))) := by
      fun_prop
    simp only [smul_eq_mul]
    exact ContDiff.mul hE hgq
  · intro p
    unfold nzModeSum
    dsimp only
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [nzfp_exp_qperiod c hc n p.2.1]

end UnforcedLeray.Short.PartIIa
