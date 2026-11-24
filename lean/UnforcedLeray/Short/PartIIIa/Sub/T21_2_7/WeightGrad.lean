import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.AdjWeakDefs

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.B0579

/-- The derivative of `jb` at `x`, as a continuous linear map. -/
theorem wg_hasFDerivAt_jb (x : ℝ × ℝ) :
    HasFDerivAt B0579.jb
      ((2 * x.1) • ContinuousLinearMap.fst ℝ ℝ ℝ + (2 * x.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
  have h1 : HasFDerivAt (fun y : ℝ × ℝ => y.1 * y.1)
      (x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) x :=
    (hasFDerivAt_fst (𝕜 := ℝ) (p := x)).mul (hasFDerivAt_fst (𝕜 := ℝ) (p := x))
  have h2 : HasFDerivAt (fun y : ℝ × ℝ => y.2 * y.2)
      (x.2 • ContinuousLinearMap.snd ℝ ℝ ℝ + x.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
    (hasFDerivAt_snd (𝕜 := ℝ) (p := x)).mul (hasFDerivAt_snd (𝕜 := ℝ) (p := x))
  have h : HasFDerivAt (fun y : ℝ × ℝ => (1 + y.1 * y.1) + y.2 * y.2)
      ((x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) +
        (x.2 • ContinuousLinearMap.snd ℝ ℝ ℝ + x.2 • ContinuousLinearMap.snd ℝ ℝ ℝ)) x :=
    (h1.const_add 1).add h2
  have hjb : B0579.jb = fun y : ℝ × ℝ => (1 + y.1 * y.1) + y.2 * y.2 := by
    funext y
    simp [B0579.jb, sq]
  rw [hjb]
  convert h using 1
  refine ContinuousLinearMap.ext fun v => ?_
  simp <;> ring

/-- Key bound: `|(-m) jb^{-m-1} (2t)| ≤ 2|m| jb^{-m}` when `2|t| ≤ jb x`. -/
theorem wg_key (m : ℝ) (x : ℝ × ℝ) (t : ℝ) (ht : 2 * |t| ≤ B0579.jb x) :
    |(-m) * B0579.jb x ^ (-m - 1) * (2 * t)| ≤ 2 * |m| * B0579.jb x ^ (-m) := by
  have hJpos : 0 < B0579.jb x ^ (-m - 1) := Real.rpow_pos_of_pos (B0579.jb_pos x) _
  have hP : 0 < B0579.jb x ^ (-m) := Real.rpow_pos_of_pos (B0579.jb_pos x) _
  have hJ : B0579.jb x ^ (-m - 1) * B0579.jb x = B0579.jb x ^ (-m) := by
    rw [← Real.rpow_add_one (B0579.jb_pos x).ne']
    congr 1
    ring
  have habs : |(-m) * B0579.jb x ^ (-m - 1) * (2 * t)| =
      |m| * B0579.jb x ^ (-m - 1) * (2 * |t|) := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos hJpos, abs_mul]
    norm_num
  rw [habs]
  have hm : 0 ≤ |m| * B0579.jb x ^ (-m - 1) := by positivity
  calc |m| * B0579.jb x ^ (-m - 1) * (2 * |t|)
      ≤ |m| * B0579.jb x ^ (-m - 1) * B0579.jb x := mul_le_mul_of_nonneg_left ht hm
    _ = |m| * B0579.jb x ^ (-m) := by rw [mul_assoc, hJ]
    _ ≤ 2 * |m| * B0579.jb x ^ (-m) := by
      have : 0 ≤ |m| * B0579.jb x ^ (-m) := by positivity
      linarith

theorem wg_two_abs_le (x : ℝ × ℝ) (k : Fin 2) :
    2 * |(if k = 0 then x.1 else x.2)| ≤ B0579.jb x := by
  unfold B0579.jb
  split_ifs
  · nlinarith [sq_abs x.1, abs_nonneg x.1, sq_nonneg (|x.1| - 1), sq_nonneg x.2]
  · nlinarith [sq_abs x.2, abs_nonneg x.2, sq_nonneg (|x.2| - 1), sq_nonneg x.1]

/-- **(a) The weight error** (SP 3044-3050): `|∂_k ⟨x⟩^{-2m}| ≤ 2|m| ⟨x⟩^{-2m}`. -/
theorem adjWeightGrad : AdjWeightGrad := by
  intro m x k
  have hg := (wg_hasFDerivAt_jb x).rpow_const (p := -m) (Or.inl (B0579.jb_pos x).ne')
  unfold B0579.pd
  rw [hg.fderiv]
  fin_cases k
  · have := wg_key m x x.1 (by simpa using wg_two_abs_le x 0)
    simpa [B0579.dir] using this
  · have := wg_key m x x.2 (by simpa using wg_two_abs_le x 1)
    simpa [B0579.dir] using this

end UnforcedLeray.Short.IIIa
