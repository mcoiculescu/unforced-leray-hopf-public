import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGrad.Sub.PartIIIb_C_rep_8_2_pres_5_3

/-!
# `ScLap`: Laplacian of the scaled field (`PartIII-b:C/rep/8/2/pres/5/3/6`)

Source of record: `shorter-proof-2026-11-02.tex` lines 4784, 5455, 5267-5268.
`D(ΔF)(v) = ε⁵ D(Δ X)(εv)` (`JetClockCore.fderiv_vecLap_Xsc`), and
`‖D(ΔX)(w)‖ ≤ 3‖D³X(w)‖` (`StreamThird.fderiv_vecLap_apply`, `StreamThird.third_le`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open MeanScaleSub

theorem scLap : MeanScaleSub.ScLap := by
  unfold MeanScaleSub.ScLap
  intro X ε v hX hε
  have hdiff : ∀ w : Vec3, ‖fderiv ℝ (vecLap X) w‖ ≤ 3 * ‖iteratedFDeriv ℝ 3 X w‖ := by
    intro w
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
    rw [StreamThird.fderiv_vecLap_apply (hX.contDiffAt : ContDiffAt ℝ 3 X w) u]
    have hpos : 0 ≤ ‖iteratedFDeriv ℝ 3 X w‖ * ‖u‖ := by positivity
    calc ‖∑ j : Fin 3, fderiv ℝ (fderiv ℝ (fderiv ℝ X)) w u (Pi.single j 1) (Pi.single j 1)‖
        ≤ ∑ j : Fin 3, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ X)) w u (Pi.single j 1) (Pi.single j 1)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _j : Fin 3, ‖iteratedFDeriv ℝ 3 X w‖ * ‖u‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          refine (StreamThird.third_le X w u (Pi.single j 1 : Vec3) (Pi.single j 1 : Vec3)).trans ?_
          have hb : ‖(Pi.single j 1 : Vec3)‖ ≤ 1 := StreamThird.norm_single_le j
          calc ‖iteratedFDeriv ℝ 3 X w‖ * ‖u‖ * ‖(Pi.single j 1 : Vec3)‖ * ‖(Pi.single j 1 : Vec3)‖
              ≤ ‖iteratedFDeriv ℝ 3 X w‖ * ‖u‖ * 1 * 1 := by gcongr
            _ = ‖iteratedFDeriv ℝ 3 X w‖ * ‖u‖ := by ring
      _ = 3 * ‖iteratedFDeriv ℝ 3 X w‖ * ‖u‖ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  rw [JetClockCore.fderiv_vecLap_Xsc hX ε v, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < ε ^ 5)]
  calc ε ^ 5 * ‖fderiv ℝ (vecLap X) (ε • v)‖ ≤ ε ^ 5 * (3 * ‖iteratedFDeriv ℝ 3 X (ε • v)‖) :=
        mul_le_mul_of_nonneg_left (hdiff _) (by positivity)
    _ = 3 * ε ^ 5 * ‖iteratedFDeriv ℝ 3 X (ε • v)‖ := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
