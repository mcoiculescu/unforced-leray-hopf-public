import UnforcedLeray.Short.PartIIb.Sub.T12_2_5

/-!
# Part II-b, task `PartII-b:T12/2/5/2`: derivatives commute with the periodization

Source of record: `the November 2 reference manuscript` (SP 1923-1926). Proves the Prop
`SlicePerFDeriv` of `Sub/T12_2_5.lean`. Near `z` only the finite window `n ∈ Icc (-N) N` of the
periodization contributes (as in `pcellPer_contDiff`), and `Dφ` vanishes off `tsupport φ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.LerayLiftSub

theorem slicePerFDeriv_proof : UnforcedLeray.Short.IIb.LerayLiftSub.SlicePerFDeriv := by
  intro c φ hc hφ hcs s z v
  -- bound on the `η`-coordinate of the support, for points of `tsupport φ`
  obtain ⟨R, hRt⟩ : ∃ R : ℝ, ∀ y ∈ tsupport φ, |y.2.1| ≤ R := by
    obtain ⟨R, hR⟩ := hcs.isCompact.exists_bound_of_continuousOn
      (f := fun y : Coord => y.2.1) (by fun_prop : Continuous fun y : Coord => y.2.1).continuousOn
    exact ⟨R, fun y hy => by simpa [Real.norm_eq_abs] using hR y hy⟩
  have hR' : ∀ y : Coord, φ y ≠ 0 → |y.2.1| ≤ R := fun y hy => hRt y (subset_tsupport _ hy)
  set W : Finset ℤ := Finset.Icc (-⌈(R + |z.1| + c) / c⌉) ⌈(R + |z.1| + c) / c⌉ with hWdef
  -- integers outside the window have `|n| c > R + |z.1| + c`
  have hmem : ∀ n : ℤ, n ∉ W → R + |z.1| + c < |(n : ℝ)| * c := by
    intro n hn
    by_contra h
    push_neg at h
    exact hn (pcell_mem_window hc h)
  -- the periodization is a finite sum on a neighbourhood of `z`
  have hout : ∀ n : ℤ, n ∉ W → ∀ w : ℝ × ℝ, |w.1 - z.1| < c →
      φ (s, (w.1 - n * c, w.2)) = 0 := by
    intro n hn w hw
    by_contra hne
    have h1 : |w.1 - n * c| ≤ R := hR' _ hne
    have h2 : |w.1| - |z.1| ≤ |w.1 - z.1| := abs_sub_abs_le_abs_sub w.1 z.1
    have h3 : |(n : ℝ) * c| - |w.1| ≤ |(n : ℝ) * c - w.1| := abs_sub_abs_le_abs_sub _ _
    have h4 : |(n : ℝ) * c - w.1| = |w.1 - n * c| := abs_sub_comm _ _
    rw [abs_mul, abs_of_pos hc] at h3
    have h5 := hmem n hn
    linarith
  have hW : ∀ w : ℝ × ℝ, |w.1 - z.1| < c →
      pcellPer c φ (s, w) = ∑ n ∈ W, φ (s, (w.1 - n * c, w.2)) := by
    intro w hw
    unfold pcellPer
    apply tsum_eq_sum
    intro n hn
    exact hout n hn w hw
  -- the derivative of `φ` vanishes at the points of the window complement
  have hfz : ∀ n : ℤ, n ∉ W → fderiv ℝ φ (s, (z.1 - n * c, z.2)) = 0 := by
    intro n hn
    have hnot : (s, (z.1 - n * c, z.2)) ∉ tsupport φ := by
      intro ht
      have h1 : |z.1 - n * c| ≤ R := hRt _ ht
      have h2 := abs_sub_abs_le_abs_sub ((n : ℝ) * c) z.1
      have h3 : |z.1 - (n : ℝ) * c| = |(n : ℝ) * c - z.1| := abs_sub_comm _ _
      rw [abs_mul, abs_of_pos hc] at h2
      have h5 := hmem n hn
      linarith
    by_contra hne
    exact hnot (support_fderiv_subset (𝕜 := ℝ) (Function.mem_support.2 hne))
  -- right-hand side as a finite sum
  have hRHS : pcellPer c (fun x => fderiv ℝ φ x (0, v)) (s, z) =
      ∑ n ∈ W, fderiv ℝ φ (s, (z.1 - n * c, z.2)) (0, v) := by
    unfold pcellPer
    apply tsum_eq_sum
    intro n hn
    show fderiv ℝ φ (s, (z.1 - n * c, z.2)) (0, v) = 0
    rw [hfz n hn]
    rfl
  -- the derivative of each term of the finite sum
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hg : ∀ n : ℤ, HasFDerivAt (fun w : ℝ × ℝ => ((s, (w.1 - n * c, w.2)) : Coord))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ))) z := by
    intro n
    have h1 : HasFDerivAt (fun w : ℝ × ℝ => w.1 - (n : ℝ) * c) (ContinuousLinearMap.fst ℝ ℝ ℝ) z :=
      (hasFDerivAt_fst).sub_const _
    have h2 : HasFDerivAt (fun w : ℝ × ℝ => (w.1 - (n : ℝ) * c, w.2))
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) z :=
      h1.prodMk hasFDerivAt_snd
    exact (hasFDerivAt_const s z).prodMk h2
  have hcomp : ∀ n : ℤ, HasFDerivAt (fun w : ℝ × ℝ => φ (s, (w.1 - n * c, w.2)))
      ((fderiv ℝ φ (s, (z.1 - n * c, z.2))).comp
        ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)))) z := by
    intro n
    exact (hφd (s, (z.1 - n * c, z.2))).hasFDerivAt.comp z (hg n)
  have hF := HasFDerivAt.fun_sum (u := W) (fun n _ => hcomp n)
  -- the neighbourhood identity
  have hopen : IsOpen {w : ℝ × ℝ | |w.1 - z.1| < c} :=
    isOpen_lt (by fun_prop) continuous_const
  have hmemN : {w : ℝ × ℝ | |w.1 - z.1| < c} ∈ 𝓝 z :=
    hopen.mem_nhds (by simpa using hc)
  have hEq : (fun w : ℝ × ℝ => pcellPer c φ (s, w)) =ᶠ[𝓝 z]
      (fun w : ℝ × ℝ => ∑ n ∈ W, φ (s, (w.1 - n * c, w.2))) := by
    filter_upwards [hmemN] with w hw
    exact hW w hw
  rw [hRHS, hEq.fderiv_eq, hF.fderiv]
  simp

end UnforcedLeray.Short.IIb.LerayLiftSub
