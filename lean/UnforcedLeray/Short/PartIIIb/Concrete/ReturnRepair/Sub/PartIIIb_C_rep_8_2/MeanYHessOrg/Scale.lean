import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.MeanYHessOrg.Calc

/-!
# `PartIII-b:C/rep/8/2/2/2/org`: scaling of iterated derivatives

Source `the November 2 reference manuscript`
4784, 5455: `X^mt_ε(y) = ε²X^mt_1(εy)`, hence `‖D^kX^mt_ε(y)‖ ≤ ε^{2+k}‖D^kX^mt_1(εy)‖`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace MeanYHessCalc

theorem iter_Xsc {X : Vec3 → Vec3} (hX : ContDiff ℝ 4 X) {ε : ℝ} (hε : 0 ≤ ε) (k : ℕ)
    (hk : k ≤ 4) (v : Vec3) :
    ‖iteratedFDeriv ℝ k (JetClockCore.Xsc X ε) v‖ ≤ ε ^ (2 + k) * ‖iteratedFDeriv ℝ k X (ε • v)‖ := by
  set g : Vec3 →L[ℝ] Vec3 := ε • ContinuousLinearMap.id ℝ Vec3 with hg
  have hX' : ContDiff ℝ (k : WithTop ℕ∞) X := hX.of_le (by exact_mod_cast hk)
  have e : JetClockCore.Xsc X ε = fun y => (ε ^ 2) • (X ∘ g) y := by
    funext y; simp [JetClockCore.Xsc, g]
  have hcomp : ContDiffAt ℝ (k : WithTop ℕ∞) (X ∘ g) v := (hX'.comp g.contDiff).contDiffAt
  rw [e, iteratedFDeriv_const_smul_apply' hcomp, g.iteratedFDeriv_comp_right hX' v le_rfl,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hgv : g v = ε • v := by simp [g]
  have hgn : ‖g‖ ≤ ε := by
    calc ‖g‖ ≤ ‖ε‖ * ‖ContinuousLinearMap.id ℝ Vec3‖ := by
          rw [hg]; exact norm_smul_le ε (ContinuousLinearMap.id ℝ Vec3)
      _ ≤ ε * 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg hε]; gcongr; exact ContinuousLinearMap.norm_id_le
      _ = ε := mul_one _
  have h1 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ k X (g v)) (fun _ : Fin k => g)
  have h2 : ∏ _i : Fin k, ‖g‖ ≤ ε ^ k := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_pow_left₀ (norm_nonneg _) hgn k
  rw [hgv] at h1
  calc ε ^ 2 * ‖(iteratedFDeriv ℝ k X (ε • v)).compContinuousLinearMap fun _ => g‖
      ≤ ε ^ 2 * (‖iteratedFDeriv ℝ k X (ε • v)‖ * ε ^ k) := by
        gcongr
        exact h1.trans (by gcongr)
    _ = ε ^ (2 + k) * ‖iteratedFDeriv ℝ k X (ε • v)‖ := by ring

end MeanYHessCalc

end UnforcedLeray.Short.PartIIIb.Concrete
end
