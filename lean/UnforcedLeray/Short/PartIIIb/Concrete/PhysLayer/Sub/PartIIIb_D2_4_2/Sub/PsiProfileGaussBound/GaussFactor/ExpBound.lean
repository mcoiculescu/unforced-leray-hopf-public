import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Sub.PsiProfileGaussBound.GaussFactor.ChartBounds

/-!
# Bound for `exp ∘ q` to order 2 (helper of `PsiProfileGaussBound`)

Source of record: `the November 2 reference manuscript` lines 4963-4991 (the
Gaussian factor `e^{-|y|²/(4a)}`).  For `q` of class `C²` on an open set `U` and `p ∈ U`,
`‖D^k e^q(p)‖ ≤ e^{q(p)} (1 + ‖Dq(p)‖ + ‖D²q(p)‖)²` for `k ≤ 2`
(`D e^q = e^q Dq`, `D² e^q = e^q (D²q + Dq ⊗ Dq)`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem exp_comp_bound {U : Set Chart} (hU : IsOpen U) {q : Chart → ℝ}
    (hq : ContDiffOn ℝ 2 q U) {p : Chart} (hp : p ∈ U) (k : ℕ) (hk : k ≤ 2) :
    ‖iteratedFDeriv ℝ k (fun x => Real.exp (q x)) p‖ ≤
      Real.exp (q p) * (1 + ‖iteratedFDeriv ℝ 1 q p‖ + ‖iteratedFDeriv ℝ 2 q p‖) ^ 2 := by
  have hE := Real.exp_pos (q p)
  set a := ‖iteratedFDeriv ℝ 1 q p‖ with ha
  set b := ‖iteratedFDeriv ℝ 2 q p‖ with hb
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hnh : U ∈ 𝓝 p := hU.mem_nhds hp
  have hdiff : ∀ x ∈ U, DifferentiableAt ℝ q x := fun x hx =>
    (hq.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hfd : ∀ x ∈ U, fderiv ℝ (fun y => Real.exp (q y)) x = Real.exp (q x) • fderiv ℝ q x :=
    fun x hx => (hdiff x hx).hasFDerivAt.exp.fderiv
  have ha' : ‖fderiv ℝ q p‖ = a := by rw [ha, norm_iteratedFDeriv_one]
  interval_cases k
  · simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_pos hE]
    have h1 : (1 : ℝ) ≤ (1 + a + b) ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left h1 hE.le
    linarith
  · rw [norm_iteratedFDeriv_one, hfd p hp, norm_smul, Real.norm_eq_abs, abs_of_pos hE, ha']
    have : a ≤ (1 + a + b) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this hE.le
  · have hq1 : ContDiffOn ℝ 1 (fderiv ℝ q) U :=
      hq.fderiv_of_isOpen hU (by norm_num)
    have hdq : DifferentiableAt ℝ (fderiv ℝ q) p :=
      (hq1.contDiffAt hnh).differentiableAt (by norm_num)
    have hdE : DifferentiableAt ℝ (fun y => Real.exp (q y)) p := (hdiff p hp).exp
    have hev : fderiv ℝ (fun y => Real.exp (q y)) =ᶠ[𝓝 p]
        fun x => Real.exp (q x) • fderiv ℝ q x :=
      Filter.eventuallyEq_of_mem hnh (fun x hx => hfd x hx)
    have h2 : ‖iteratedFDeriv ℝ 2 (fun x => Real.exp (q x)) p‖ =
        ‖fderiv ℝ (fun x => Real.exp (q x) • fderiv ℝ q x) p‖ := by
      rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one, hev.fderiv_eq]
    have hs : fderiv ℝ (fun x => Real.exp (q x) • fderiv ℝ q x) p =
        Real.exp (q p) • fderiv ℝ (fderiv ℝ q) p +
          (fderiv ℝ (fun y => Real.exp (q y)) p).smulRight (fderiv ℝ q p) :=
      fderiv_smul hdE hdq
    rw [h2, hs]
    have hb' : ‖fderiv ℝ (fderiv ℝ q) p‖ = b := by
      rw [hb, ← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
    have hE' : ‖fderiv ℝ (fun y => Real.exp (q y)) p‖ = Real.exp (q p) * a := by
      rw [hfd p hp, norm_smul, Real.norm_eq_abs, abs_of_pos hE, ha']
    refine (norm_add_le (Real.exp (q p) • fderiv ℝ (fderiv ℝ q) p)
      ((fderiv ℝ (fun y => Real.exp (q y)) p).smulRight (fderiv ℝ q p))).trans ?_
    have n1 : ‖Real.exp (q p) • fderiv ℝ (fderiv ℝ q) p‖ ≤ Real.exp (q p) * b := by
      refine (ContinuousLinearMap.opNorm_smul_le (Real.exp (q p)) (fderiv ℝ (fderiv ℝ q) p)).trans ?_
      rw [Real.norm_eq_abs, abs_of_pos hE, hb']
    have n2 : ‖(fderiv ℝ (fun y => Real.exp (q y)) p).smulRight (fderiv ℝ q p)‖ =
        (Real.exp (q p) * a) * a := by
      rw [ContinuousLinearMap.norm_smulRight_apply, hE', ha']
    rw [n2] at *
    refine (add_le_add n1 le_rfl).trans ?_
    nlinarith [mul_nonneg hE.le ha0, mul_nonneg hE.le hb0,
      mul_nonneg hE.le (mul_nonneg ha0 hb0), mul_nonneg hE.le (mul_nonneg ha0 ha0),
      mul_nonneg hE.le (mul_nonneg hb0 hb0)]

end UnforcedLeray.Short.PartIIIb.Concrete
