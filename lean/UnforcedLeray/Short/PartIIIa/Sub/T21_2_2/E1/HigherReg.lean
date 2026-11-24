import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.HigherReg.Transfer

/-!
# `PartIII-a:T21/2/2/3/4`: weighted `H²`, `H³` regularity of the moving adjoint (SP 3060-3071)

From `IsAdjointFlow.higherCont` (`MemLp` of `∂^wφ(r)` for `|w| ≤ 3`) by the scaling
`x = √a y`: `∂^w(movingPhi)(y) = a⁻¹(√a)^{|w|} (∂^wφ)(√a y)` (`pdCx_movingPhi_two/three`), and
the transfer of the weighted integrability to the moving cell (`transfer_weight_int`).
The age `r = revAge ν s ζ` lies in `[t, s)` by `adjAgeMap`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

theorem movAdjHigherReg (m : ℝ) (hm : 8 < m) : MovAdjHigherReg m := by
  intro ν tr t s φ ζ hF
  obtain ⟨hν, ht, hts, ⟨G, _hG, hflow⟩, hζ⟩ := hF
  have hr : revAge ν s ζ ∈ Ico t s := (adjAgeMap ν t s hν ht hts).2.2 (Ioo_subset_Ioc_self hζ)
  have hm0 : 0 ≤ m := by linarith
  have hc : 0 < ν ^ (-2 : ℝ) := by positivity
  have ha : 0 < clockA ν (revAge ν s ζ) := by
    have h0 : 0 ≤ revAge ν s ζ := ht.trans hr.1
    unfold clockA
    nlinarith [mul_nonneg hν.le h0]
  have hR : 0 < Real.sqrt (clockA ν (revAge ν s ζ)) := Real.sqrt_pos.2 ha
  have hφ : ContDiff ℝ ∞ (φ (revAge ν s ζ)) := hflow.smooth _ hr
  unfold mvPhi mvLen cellLen
  set r := revAge ν s ζ with hr_def
  refine ⟨fun k l => ?_, fun j k l => ?_⟩
  · have hMem : MemLp (pdCx k (pdCx l (φ r))) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
      ((hflow.higherCont r hr [k, l]).1 (by simp)).1
    rw [pdCx_movingPhi_two ν φ r hφ ha k l]
    exact transfer_weight_int m (ν ^ (-2 : ℝ)) (Real.sqrt (clockA ν r)) hm0 hc hR _ hMem
  · have hMem : MemLp (pdCx j (pdCx k (pdCx l (φ r)))) 2
        (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
      ((hflow.higherCont r hr [j, k, l]).1 (by simp)).1
    rw [pdCx_movingPhi_three ν φ r hφ ha j k l]
    have h := (transfer_weight_int m (ν ^ (-2 : ℝ)) (Real.sqrt (clockA ν r)) hm0 hc hR _
      hMem).const_mul ((Real.sqrt (clockA ν r)) ^ 2)
    refine IntegrableOn.congr_fun h (fun y _ => ?_) (B0579.measurableSet_cell _)
    simp only [norm_sq_real_const_mul]
    ring

end UnforcedLeray.Short.IIIa.AdjE1
