import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_5

/-!
# Lemma `/1` of `PartIII-a:T21/3/5`: the train vorticity is smooth and `c`-periodic.

`Ec tr r = Cyl.curl (tr.v r)` for `r ≥ 0`; `tr.v r` is `C^∞` (`B0238.contDiff_Vc`) and
`c`-periodic (`IsTrain.periodic_v`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

theorem ecSmoothPeriodic_all : ∀ (ν c : ℝ) [Fact (0 < c)] (tr : UnforcedLeray.B0140.TrainSol ν c), UnforcedLeray.Short.IIIa.Exist.EcSmoothPeriodic (c := c) tr := by
  intro ν c _ tr r hr
  have hv : ContDiff ℝ ∞ (tr.v r) := UnforcedLeray.B0238.contDiff_Vc tr hr
  have hper : UnforcedLeray.Cyl.IsPeriodic c (tr.v r) := tr.isTrain.periodic_v r hr
  constructor
  · have h1 : ContDiff ℝ ∞ (fun z => fderiv ℝ (fun w => tr.v r w 1) z (1, 0)) :=
      ((UnforcedLeray.B0238.contDiff_comp_apply hv 1).fderiv_right (m := ∞) (by simp)).clm_apply
        contDiff_const
    have h0 : ContDiff ℝ ∞ (fun z => fderiv ℝ (fun w => tr.v r w 0) z (0, 1)) :=
      ((UnforcedLeray.B0238.contDiff_comp_apply hv 0).fderiv_right (m := ∞) (by simp)).clm_apply
        contDiff_const
    have hEq : UnforcedLeray.B0238.Ec tr r = fun z =>
        fderiv ℝ (fun w => tr.v r w 1) z (1, 0) - fderiv ℝ (fun w => tr.v r w 0) z (0, 1) :=
      funext (UnforcedLeray.B0238.curl_eq_fderiv (hv.of_le (by exact_mod_cast le_top)))
    rw [hEq]
    exact h1.sub h0
  · intro x
    have hA : UnforcedLeray.Cyl.IsPeriodic c (UnforcedLeray.Cyl.partialQ (fun w => tr.v r w 1)) :=
      (hper.fun_comp (fun e : UnforcedLeray.Cyl.Vec2 => e 1)).partialQ
    have hB : UnforcedLeray.Cyl.IsPeriodic c (UnforcedLeray.Cyl.partialEta (fun w => tr.v r w 0)) :=
      (hper.fun_comp (fun e : UnforcedLeray.Cyl.Vec2 => e 0)).partialEta
    show UnforcedLeray.Cyl.curl (tr.v r) (x.1 + c, x.2) = UnforcedLeray.Cyl.curl (tr.v r) x
    unfold UnforcedLeray.Cyl.curl
    rw [hA x, hB x]

end
