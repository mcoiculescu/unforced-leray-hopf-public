import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_3.Bound.Est2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.RingSubst.Term2D2

/-!
# Identification of the leading terms and of the weight
(`PartIII-b:C/rep/8/2/1/3/b`, helper 7)

Source lines 5463, 5464-5465.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2BoundAux

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Axi
open UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2FormulaAux (merSpL merSpL_apply)

theorem norm_merSp (m : Merid) : ‖merSp m‖ = ‖m‖ := by
  simp [merSp, vecSp, EuclideanSpace.norm_eq, Fin.sum_univ_three, Fin.sum_univ_two]

theorem merSp_smul (c : ℝ) (m : Merid) : merSp (c • m) = c • merSp m := by
  rw [← merSpL_apply, ← merSpL_apply, map_smul]

theorem merSp_sub (m m' : Merid) : merSp (m - m') = merSp m - merSp m' := by
  rw [← merSpL_apply, ← merSpL_apply, ← merSpL_apply, map_sub]

theorem norm_vecSp_le (a c : ℝ) : ‖vecSp ![a, 0, c]‖ ≤ |a| + |c| := by
  simp only [vecSp, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp only [WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Real.norm_eq_abs, sq_abs, abs_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_add, Matrix.head_cons, Matrix.tail_cons]
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg a, abs_nonneg c, sq_abs a, sq_abs c]

theorem norm_vecSp_mid (b : ℝ) : ‖vecSp ![0, b, 0]‖ = |b| := by
  simp [vecSp, EuclideanSpace.norm_eq, Fin.sum_univ_three, Real.sqrt_sq_eq_abs]

theorem phi_log {p : Chart} (hp : 0 < p.1) : phi (Real.log p.1, p.2) = p := by
  simp [phi, Real.exp_log hp]

theorem wt_three_half (z : Zc) : wt (3 / 2) z = (Real.exp z.1) ^ (3 / 2 : ℝ) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, wt]; ring_nf

theorem wt_one (z : Zc) : wt 1 z = Real.exp z.1 := by simp [wt]

theorem wt_half (z : Zc) : wt (1 / 2) z = Real.sqrt (Real.exp z.1) := by
  rw [wt, exp_half_eq]

theorem wt_pos (α : ℝ) (z : Zc) : 0 < wt α z := Real.exp_pos _

/-- `vecSp (flatD2 …)` is `merSp` of the second derivative of `ṽ`. -/
theorem vecSp_flatD2 (L : ReturnLevel) (z : Zc) (j l : Fin 3) :
    vecSp (flatD2 L (Real.exp z.1) z.2 j l) =
      merSp (fderiv ℝ (fderiv ℝ (trainFv L)) z ((0 : ℝ), flatDir j) ((0 : ℝ), flatDir l)) := by
  have hs : 0 < Real.exp z.1 := Real.exp_pos _
  have h := fderiv_fderiv_trainV_ring L hs z.2 (flatDir j) (flatDir l)
  rw [Real.log_exp] at h
  have hinr : ∀ w : ℝ × ℝ, ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) w = ((0 : ℝ), w) := fun w => by simp
  rw [hinr, hinr] at h
  unfold flatD2
  rw [h]
  rfl

theorem dir_eq_Dq (F : Zc → Merid) : Gop 1 0 0 0 0 F = fun z => fderiv ℝ F z ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) := by
  funext z; simp [Gop]

theorem dir_eq_Zo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Zc → E) :
    Zo F = fun z => fderiv ℝ F z ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) := by
  funext z; simp [Zo, Gop]

theorem fderiv_dir_dir {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Zc → E}
    (hF : ContDiff ℝ ∞ F) (d d' z : Zc) :
    fderiv ℝ (fun z' => fderiv ℝ F z' d) z d' = fderiv ℝ (fderiv ℝ F) z d' d := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hc : DifferentiableAt ℝ (fderiv ℝ F) z := (h1.differentiable (by simp)) z
  have h := hc.hasFDerivAt.clm_apply (hasFDerivAt_const d z)
  have : fderiv ℝ (fun z' => fderiv ℝ F z' d) z = _ := h.fderiv
  rw [this]
  simp

/-- The weight comparison: `ω³ (J₂ ṽ + J₃ ψ̃) ≤ 𝔴₃`. -/
theorem weight_ge (L : ReturnLevel) {p : Chart} :
    (1 + |p.2.2|) ^ 3 * (J 2 (trainFv L) (Real.log p.1, p.2) + J 3 (trainFpsi L) (Real.log p.1, p.2)) ≤
      trainWeight 3 L p := by
  unfold trainWeight J
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 : ∑ k ∈ Finset.range 3, ‖iteratedFDeriv ℝ k (trainFv L) (Real.log p.1, p.2)‖ ≤
      ∑ k ∈ Finset.range 5, ‖iteratedFDeriv ℝ k (trainFv L) (Real.log p.1, p.2)‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by norm_num))
      (fun k _ _ => norm_nonneg _)
  have h3 : ∑ k ∈ Finset.range 4, ‖iteratedFDeriv ℝ k (trainFpsi L) (Real.log p.1, p.2)‖ ≤
      ∑ k ∈ Finset.range 5, ‖iteratedFDeriv ℝ k (trainFpsi L) (Real.log p.1, p.2)‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by norm_num))
      (fun k _ _ => norm_nonneg _)
  have h2 : 0 ≤ ∑ k ∈ Finset.range 5, ‖iteratedFDeriv ℝ k (trainFp L) (Real.log p.1, p.2)‖ :=
    Finset.sum_nonneg fun k _ => norm_nonneg _
  simp only [Finset.sum_add_distrib]
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2BoundAux
