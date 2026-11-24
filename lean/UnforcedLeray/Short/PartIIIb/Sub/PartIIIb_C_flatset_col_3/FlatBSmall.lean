import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_3

/-!
# `flatBSmall : FlatBSmall` (decomposition of `PartIII-b:C/flatset/col/3`, leaf 1)

Source of record `the November 2 reference manuscript` lines 4610, 4614-4615, 4957-4958.
`B = Bmat ν μ χf A = deriv (Ay ν χf A) + (μ/s) Ay`, `Ay s = χf(νs) A s`.
Route: entrywise bounds `|A s i j| ≤ K s^{5/2}` and `|deriv A s i j| ≤ K s^{3/2}` on `(0,1]`
from `IsAffElem.bdd` (the `j = 0, 1` terms of `affSum 6`); the product rule
`deriv (Ay) s = (χf'(νs) ν) • A s + χf(νs) • deriv A s`; `χf'` bounded on `[0, ν]`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem fbs_frob_nonneg (M : Mat3) : 0 ≤ frob M := by
  unfold frob
  exact Real.sqrt_nonneg _

theorem fbs_abs_le_frob (M : Mat3) (i j : Fin 3) : |M i j| ≤ frob M := by
  unfold frob
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  have h1 : M i j ^ 2 ≤ ∑ j', M i j' ^ 2 :=
    Finset.single_le_sum (f := fun j' => M i j' ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', M i j' ^ 2 ≤ ∑ i', ∑ j', M i' j' ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', M i' j' ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  linarith

/-- The `j = 0, 1` terms of `affSum 6` dominate `frob (A s) + frob (s ∂_s A s)`. -/
theorem fbs_two_le (A : ℝ → Mat3) (s : ℝ) :
    frob (A s) + frob (s • deriv A s) ≤ affSum 6 A s := by
  have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range (6 + 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun i _ _ => fbs_frob_nonneg (sDerivIter i A s))
  rw [Finset.sum_pair (by norm_num)] at h
  have e0 : sDerivIter 0 A s = A s := rfl
  have e1 : sDerivIter 1 A s = s • deriv A s := rfl
  rw [e0, e1] at h
  unfold affSum
  exact h

/-- Entrywise bounds for an affine element on `(0,1]`. -/
theorem fbs_affBound (as : ℝ) (A : ℝ → Mat3) (hA : IsAffElem as A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ i j,
      |A s i j| ≤ K * s ^ (5 / 2 : ℝ) ∧ |deriv A s i j| ≤ K * s ^ (3 / 2 : ℝ) := by
  obtain ⟨M0, hM0⟩ := hA.bdd
  refine ⟨Real.exp |as| * |M0|, by positivity, ?_⟩
  intro s hs hs1 i j
  have hT : affTerm as 6 A s ≤ M0 := hM0 ⟨s, hs, rfl⟩
  have hp : 0 < s ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
  have hr : s ^ (-(5 / 2 : ℝ)) * s ^ (5 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hs]; norm_num
  have he : Real.exp (-as * s) * Real.exp (as * s) = 1 := by
    rw [← Real.exp_add]; simp
  have hS : affSum 6 A s ≤ Real.exp |as| * |M0| * s ^ (5 / 2 : ℝ) := by
    have hX : Real.exp (-as * s) * s ^ (-(5 / 2 : ℝ)) * affSum 6 A s ≤ M0 := hT
    have key : affSum 6 A s =
        (Real.exp (-as * s) * s ^ (-(5 / 2 : ℝ)) * affSum 6 A s) *
          (Real.exp (as * s) * s ^ (5 / 2 : ℝ)) := by
      have : (Real.exp (-as * s) * s ^ (-(5 / 2 : ℝ)) * affSum 6 A s) *
          (Real.exp (as * s) * s ^ (5 / 2 : ℝ)) =
          (Real.exp (-as * s) * Real.exp (as * s)) *
            (s ^ (-(5 / 2 : ℝ)) * s ^ (5 / 2 : ℝ)) * affSum 6 A s := by ring
      rw [this, he, hr, one_mul, one_mul]
    have hY : 0 ≤ Real.exp (as * s) * s ^ (5 / 2 : ℝ) := by positivity
    have hx : as * s ≤ |as| := by
      calc as * s ≤ |as| * s := mul_le_mul_of_nonneg_right (le_abs_self as) hs.le
        _ ≤ |as| := mul_le_of_le_one_right (abs_nonneg as) hs1
    have hYY : Real.exp (as * s) * s ^ (5 / 2 : ℝ) ≤ Real.exp |as| * s ^ (5 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hx) hp.le
    calc affSum 6 A s
        = (Real.exp (-as * s) * s ^ (-(5 / 2 : ℝ)) * affSum 6 A s) *
          (Real.exp (as * s) * s ^ (5 / 2 : ℝ)) := key
      _ ≤ M0 * (Real.exp (as * s) * s ^ (5 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hX hY
      _ ≤ |M0| * (Real.exp (as * s) * s ^ (5 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_abs_self M0) hY
      _ ≤ |M0| * (Real.exp |as| * s ^ (5 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hYY (abs_nonneg _)
      _ = Real.exp |as| * |M0| * s ^ (5 / 2 : ℝ) := by ring
  have hp5 : s ^ (5 / 2 : ℝ) = s ^ (3 / 2 : ℝ) * s := by
    rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.rpow_add hs, Real.rpow_one]
  have hsum := fbs_two_le A s
  have hfA : |A s i j| ≤ Real.exp |as| * |M0| * s ^ (5 / 2 : ℝ) := by
    refine le_trans (fbs_abs_le_frob _ i j) (le_trans ?_ hS)
    linarith [fbs_frob_nonneg (s • deriv A s)]
  refine ⟨hfA, ?_⟩
  have h1 : s * |deriv A s i j| ≤ Real.exp |as| * |M0| * s ^ (5 / 2 : ℝ) := by
    have e : |(s • deriv A s) i j| = s * |deriv A s i j| := by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hs]
    rw [← e]
    refine le_trans (fbs_abs_le_frob _ i j) (le_trans ?_ hS)
    linarith [fbs_frob_nonneg (A s)]
  have h2 : s * |deriv A s i j| ≤ s * (Real.exp |as| * |M0| * s ^ (3 / 2 : ℝ)) := by
    calc s * |deriv A s i j| ≤ Real.exp |as| * |M0| * s ^ (5 / 2 : ℝ) := h1
      _ = s * (Real.exp |as| * |M0| * s ^ (3 / 2 : ℝ)) := by rw [hp5]; ring
  exact le_of_mul_le_mul_left h2 hs

theorem flatBSmall : FlatBSmall := by
  intro ν μ as χf A hν hχ hA
  obtain ⟨K, hK0, hKb⟩ := fbs_affBound as A hA
  have hχc := hχ.smooth
  have hcd : Continuous (deriv χf) := hχc.continuous_deriv (by simp)
  obtain ⟨D, hD⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := ν)).exists_bound_of_continuousOn
    hcd.continuousOn
  have hD' : ∀ t ∈ Icc (0 : ℝ) ν, |deriv χf t| ≤ D := fun t ht => by
    simpa [Real.norm_eq_abs] using hD t ht
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (hD' 0 ⟨le_refl _, hν.le⟩)
  have hcdiff : Differentiable ℝ χf := hχc.differentiable (by simp)
  refine ⟨D * ν * K + K + |μ| * K, ?_⟩
  intro s hs i j
  have hs0 : 0 < s := hs.1
  have hs1 : s ≤ 1 := hs.2
  obtain ⟨hA1, hA2⟩ := hKb s hs0 hs1 i j
  have hp : 0 ≤ s ^ (3 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
  have hp5 : s ^ (5 / 2 : ℝ) = s ^ (3 / 2 : ℝ) * s := by
    rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.rpow_add hs0, Real.rpow_one]
  have hs52 : s ^ (5 / 2 : ℝ) ≤ s ^ (3 / 2 : ℝ) := by
    rw [hp5]; exact mul_le_of_le_one_right hp hs1
  have hAdiff : DifferentiableAt ℝ A s :=
    (hA.smooth.contDiffAt (Ioi_mem_nhds hs0)).differentiableAt (by norm_num)
  have hcomp : HasDerivAt (fun t => χf (ν * t)) (deriv χf (ν * s) * ν) s := by
    have h2 : HasDerivAt (fun t => ν * t) ν s := by
      simpa using (hasDerivAt_id s).const_mul ν
    exact (hcdiff (ν * s)).hasDerivAt.comp s h2
  have hYd : HasDerivAt (Ay ν χf A)
      ((deriv χf (ν * s) * ν) • A s + χf (ν * s) • deriv A s) s := by
    have h := hcomp.smul hAdiff.hasDerivAt
    rw [add_comm] at h
    exact h
  have hdY : deriv (Ay ν χf A) s = (deriv χf (ν * s) * ν) • A s + χf (ν * s) • deriv A s :=
    hYd.deriv
  have hBentry : Bmat ν μ χf A s i j =
      deriv χf (ν * s) * ν * A s i j + χf (ν * s) * deriv A s i j +
        μ / s * (χf (ν * s) * A s i j) := by
    show (deriv (Ay ν χf A) s + (μ / s) • Ay ν χf A s) i j = _
    rw [hdY]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Ay]
  have hχr := hχ.range (ν * s)
  have hχabs : |χf (ν * s)| ≤ 1 := abs_le.mpr ⟨by linarith [hχr.1], hχr.2⟩
  have hDχ : |deriv χf (ν * s)| ≤ D := hD' (ν * s) ⟨by nlinarith, by nlinarith⟩
  -- term 1
  have h_a : |deriv χf (ν * s) * ν * A s i j| ≤ D * ν * (K * s ^ (5 / 2 : ℝ)) := by
    rw [abs_mul, abs_mul, abs_of_pos hν]
    calc |deriv χf (ν * s)| * ν * |A s i j|
        ≤ D * ν * |A s i j| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDχ hν.le) (abs_nonneg _)
      _ ≤ D * ν * (K * s ^ (5 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hA1 (mul_nonneg hD0 hν.le)
  -- term 2
  have h_b : |χf (ν * s) * deriv A s i j| ≤ K * s ^ (3 / 2 : ℝ) := by
    rw [abs_mul]
    calc |χf (ν * s)| * |deriv A s i j| ≤ 1 * (K * s ^ (3 / 2 : ℝ)) :=
          mul_le_mul hχabs hA2 (abs_nonneg _) zero_le_one
      _ = K * s ^ (3 / 2 : ℝ) := one_mul _
  -- term 3
  have h_c : |μ / s * (χf (ν * s) * A s i j)| ≤ |μ| * K * s ^ (3 / 2 : ℝ) := by
    have hχA : |χf (ν * s) * A s i j| ≤ K * s ^ (5 / 2 : ℝ) := by
      rw [abs_mul]
      calc |χf (ν * s)| * |A s i j| ≤ 1 * (K * s ^ (5 / 2 : ℝ)) :=
            mul_le_mul hχabs hA1 (abs_nonneg _) zero_le_one
        _ = K * s ^ (5 / 2 : ℝ) := one_mul _
    rw [abs_mul, abs_div, abs_of_pos hs0]
    calc |μ| / s * |χf (ν * s) * A s i j| ≤ |μ| / s * (K * s ^ (5 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hχA (div_nonneg (abs_nonneg _) hs0.le)
      _ = |μ| * K * s ^ (3 / 2 : ℝ) := by
          rw [hp5]; field_simp
  have h_a' : D * ν * (K * s ^ (5 / 2 : ℝ)) ≤ D * ν * K * s ^ (3 / 2 : ℝ) := by
    have := mul_le_mul_of_nonneg_left hs52 hK0
    have h3 := mul_le_mul_of_nonneg_left this (mul_nonneg hD0 hν.le)
    linarith
  have htri : |deriv χf (ν * s) * ν * A s i j + χf (ν * s) * deriv A s i j +
      μ / s * (χf (ν * s) * A s i j)| ≤
      |deriv χf (ν * s) * ν * A s i j| + |χf (ν * s) * deriv A s i j| +
        |μ / s * (χf (ν * s) * A s i j)| :=
    le_trans (abs_add_le _ _) (add_le_add (abs_add_le _ _) le_rfl)
  rw [hBentry]
  have e : (D * ν * K + K + |μ| * K) * s ^ (3 / 2 : ℝ) =
      D * ν * K * s ^ (3 / 2 : ℝ) + K * s ^ (3 / 2 : ℝ) + |μ| * K * s ^ (3 / 2 : ℝ) := by ring
  rw [e]
  linarith [htri, h_a, h_a', h_b, h_c]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
