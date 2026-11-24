import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_11_2_2_2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L2

/-!
# `HeatLerayKSmoothTop` (`PartIII-b:IIIb-D2/3/2/11/2/2/2/2`, source 3604-3610)

All-order analogue of `heatLerayKSmooth`: `K_t = δ G_t + ∂∂ Ψ(|x|²/4)` with `Ψ = L2hkPsi t 0`.
The derivative tower `L2hkPsi t m` is differentiable for every `m` (`L2_psi_hasDeriv`), so
`Ψ` is `C^∞` by `contDiff_of_differentiable_iteratedDeriv` (no order cut-off at 5).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `Ψ = L2hkPsi t 0` is `C^∞` on `ℝ` for `t > 0`. -/
theorem heatKL2PsiTop (t : ℝ) (ht : 0 < t) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (L2hkPsi t 0) := by
  have hIter : ∀ m : ℕ, iteratedDeriv m (L2hkPsi t 0) = L2hkPsi t m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [iteratedDeriv_succ, ih]
      funext r
      exact (L2_psi_hasDeriv t ht m r).deriv
  apply contDiff_of_differentiable_iteratedDeriv
  intro m _
  rw [hIter m]
  intro r
  exact (L2_psi_hasDeriv t ht m r).differentiableAt

/-- **`HeatLerayKSmoothTop`**: `K_t` is `C^∞` on `ℝ³` for `t > 0`. -/
theorem heatLerayKSmoothTop : HeatLerayKSmoothTop := by
  intro t ht i j
  have hT : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (UnforcedLeray.Short.IIIa.heatTail t) := by
    have hfun : UnforcedLeray.Short.IIIa.heatTail t =
        fun x => L2hkPsi t 0 (‖x‖ ^ 2 / 4) := by
      funext x
      unfold UnforcedLeray.Short.IIIa.heatTail L2hkPsi
      congr 1
      funext a
      unfold UnforcedLeray.Short.IIIa.heatG L2hkG
      have e : -‖x‖ ^ 2 / (4 * a) = -(‖x‖ ^ 2 / 4) / a := by ring
      simp only [pow_zero, one_mul]
      rw [e]
    rw [hfun]
    exact (heatKL2PsiTop t ht).comp (ContDiff.div_const (contDiff_norm_sq ℝ) 4)
  have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => UnforcedLeray.Short.IIIa.heatG t x) := by
    unfold UnforcedLeray.Short.IIIa.heatG
    exact contDiff_const.mul
      (Real.contDiff_exp.comp (ContDiff.div_const (ContDiff.neg (contDiff_norm_sq ℝ)) _))
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => fderiv ℝ (UnforcedLeray.Short.IIIa.heatTail t) y (coordinateVector j)) :=
    (contDiff_infty_iff_fderiv.1 hT).2.clm_apply contDiff_const
  have hp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => UnforcedLeray.Short.IIIa.part2
      (UnforcedLeray.Short.IIIa.heatTail t) i j x) := by
    unfold UnforcedLeray.Short.IIIa.part2
    exact (contDiff_infty_iff_fderiv.1 hg).2.clm_apply contDiff_const
  unfold UnforcedLeray.Short.IIIa.heatLerayK
  refine ContDiff.add ?_ hp
  by_cases h : i = j
  · simp only [if_pos h]
    exact hG
  · simp only [if_neg h]
    exact contDiff_const

end UnforcedLeray.Short.PartIIIb.Concrete
