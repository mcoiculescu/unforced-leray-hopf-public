import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_9_2
import UnforcedLeray.Short.PartIIIb.Concrete.AffineEnvelope.SDerivIterDiffOn
import UnforcedLeray.Short.PartIIIb.Concrete.AffineEnvelope.SDerivIterLeibniz

/-!


Source `the November 2 reference manuscript` lines 4953-4962 (`M(A)` as a supremum
over `0 < s ≤ 1.1/ν`), 5063-5071.

For `0 < s ≤ 1.1/ν` the entry `|(s∂_s)^i A^y (s)|` is at most `affSum 6 A^y (s) ≤ s^{5/2} M(A)`,
the supremum being bounded by `aySumBdd_of`.  For `νs ≥ 1.1` all `(s∂_s)^i A^y` vanish: `A^y = 0`
on `(1.1/ν, ∞)` and the derivatives vanish there by induction; at `s = 1.1/ν` they vanish by
continuity of the `C^{6-i}` function `(s∂_s)^i A^y` on `(0,∞)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

private lemma t7_frob_nonneg (M : Mat3) : 0 ≤ frob M := Real.sqrt_nonneg _

private lemma t7_abs_le_frob (M : Mat3) (a b : Fin 3) : |M a b| ≤ frob M := by
  have h1 : M a b ^ 2 ≤ ∑ j, M a j ^ 2 :=
    Finset.single_le_sum (f := fun j => M a j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ b)
  have h2 : ∑ j, M a j ^ 2 ≤ ∑ i, ∑ j, M i j ^ 2 :=
    Finset.single_le_sum (f := fun i => ∑ j, M i j ^ 2)
      (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ a)
  exact Real.abs_le_sqrt (h1.trans h2)

private lemma t7_affM_nonneg (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) : 0 ≤ affM ν χ A := by
  unfold affM
  apply Real.sSup_nonneg
  rintro _ ⟨t, ht, rfl⟩
  show 0 ≤ t ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χ A) t
  refine mul_nonneg (Real.rpow_nonneg (le_of_lt ht.1) _) ?_
  unfold affSum
  exact Finset.sum_nonneg fun j _ => t7_frob_nonneg _

/-- If `f` vanishes on `(c, ∞)` then so does every `(s∂_s)^k f`. -/
private lemma t7_iter_zero_right (f : ℝ → Mat3) (c : ℝ) (hf : ∀ t, c < t → f t = 0) :
    ∀ k : ℕ, ∀ t, c < t → sDerivIter k f t = 0 := by
  intro k
  induction k with
  | zero => intro t ht; simpa [sDerivIter] using hf t ht
  | succ k ih =>
    intro t ht
    have hev : sDerivIter k f =ᶠ[𝓝 t] fun _ => (0 : Mat3) := by
      filter_upwards [Ioi_mem_nhds ht] with u hu
      exact ih u hu
    have hd : deriv (sDerivIter k f) t = 0 := by
      rw [hev.deriv_eq]; simp
    simp only [sDerivIter, sDeriv, hd, smul_zero]

/-- A function continuous at `s0` and vanishing on `(s0, ∞)` vanishes at `s0`. -/
private lemma t7_zero_of_right {f : ℝ → Mat3} {s0 : ℝ} (hc : ContinuousAt f s0)
    (h : ∀ t, s0 < t → f t = 0) : f s0 = 0 := by
  have h1 : Tendsto f (𝓝[>] s0) (𝓝 (f s0)) := hc.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto f (𝓝[>] s0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (h t ht).symm
  exact tendsto_nhds_unique h1 h2

theorem ayEntryBound (as : ℝ) (χf : ℝ → ℝ) : IsSourceCutoffC χf → ∀ ν : ℝ, 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A → ∀ s : ℝ, 0 < s → ∀ i : ℕ, i ≤ 6 → ∀ a b : Fin 3, (|sDerivIter i (Ay ν χf A) s a b| ≤ affM ν χf A * s ^ (5 / 2 : ℝ)) ∧ ((11 / 10 : ℝ) ≤ ν * s → sDerivIter i (Ay ν χf A) s a b = 0) := by
  intro hχ ν hν A hA s hs i hi a b
  have hc0 : (0 : ℝ) < (11 / 10) / ν := by positivity
  -- smoothness of `A^y`
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => χf (ν * t)) :=
    hχ.smooth.comp (contDiff_const.mul contDiff_id)
  have hcut : ContDiffOn ℝ 6 (fun t : ℝ => χf (ν * t)) (Ioi 0) :=
    hc.contDiffOn.of_le (by norm_num)
  have hAy6 : ContDiffOn ℝ 6 (Ay ν χf A) (Ioi 0) := by
    unfold Ay
    exact hcut.smul hA.smooth
  have h6 : ContDiffOn ℝ ((i + (6 - i) : ℕ) : WithTop ℕ∞) (Ay ν χf A) (Ioi 0) := by
    have e : i + (6 - i) = 6 := by omega
    rw [e]
    exact_mod_cast hAy6
  have hdiff := sDerivIter_contDiffOn_aux (Ay ν χf A) i (6 - i) h6
  have hcont : ContinuousAt (sDerivIter i (Ay ν χf A)) ((11 / 10) / ν) :=
    hdiff.continuousOn.continuousAt (Ioi_mem_nhds hc0)
  -- `A^y` vanishes on `(1.1/ν, ∞)`
  have hzero : ∀ t : ℝ, (11 / 10) / ν < t → Ay ν χf A t = 0 := by
    intro t ht
    have hνt : (11 / 10 : ℝ) ≤ ν * t := by
      have h1 : ν * ((11 / 10) / ν) < ν * t := mul_lt_mul_of_pos_left ht hν
      have e : ν * ((11 / 10) / ν) = 11 / 10 := by field_simp
      linarith
    unfold Ay
    simp [hχ.zero (ν * t) hνt]
  -- vanishing of `(s∂_s)^i A^y` for `νs ≥ 1.1`
  have hvan : ∀ t : ℝ, (11 / 10 : ℝ) ≤ ν * t → sDerivIter i (Ay ν χf A) t = 0 := by
    intro t ht
    have hct : (11 / 10) / ν ≤ t := by
      rw [div_le_iff₀ hν, mul_comm]
      exact ht
    rcases eq_or_lt_of_le hct with h | h
    · rw [← h]
      exact t7_zero_of_right hcont (fun u hu => t7_iter_zero_right (Ay ν χf A) ((11 / 10) / ν) hzero i u hu)
    · exact t7_iter_zero_right (Ay ν χf A) ((11 / 10) / ν) hzero i t h
  refine ⟨?_, fun hs' => ?_⟩
  · by_cases hsc : (11 / 10 : ℝ) ≤ ν * s
    · rw [hvan s hsc]
      simp only [Pi.zero_apply, abs_zero]
      exact mul_nonneg (t7_affM_nonneg ν χf A) (Real.rpow_nonneg hs.le _)
    · rw [not_le] at hsc
      have hsle : s ≤ (11 / 10) / ν := by
        rw [le_div_iff₀ hν, mul_comm]
        exact hsc.le
      have hbdd := aySumBdd_of sDerivIterDiffOn sDerivIterLeibniz as χf hχ ν hν A hA
      have hle : s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χf A) s ≤
          sSup ((fun s => s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χf A) s) '' Ioc 0 ((11 / 10) / ν)) :=
        le_csSup hbdd (Set.mem_image_of_mem _ ⟨hs, hsle⟩)
      have hsup : s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χf A) s ≤ affM ν χf A := hle
      have hterm : frob (sDerivIter i (Ay ν χf A) s) ≤ affSum 6 (Ay ν χf A) s := by
        unfold affSum
        exact Finset.single_le_sum (f := fun j => frob (sDerivIter j (Ay ν χf A) s))
          (fun j _ => t7_frob_nonneg _) (Finset.mem_range.2 (by omega))
      have hinv : s ^ (5 / 2 : ℝ) * s ^ (-(5 / 2 : ℝ)) = 1 := by
        rw [← Real.rpow_add hs]; norm_num
      have hq : 0 ≤ s ^ (5 / 2 : ℝ) := Real.rpow_nonneg hs.le _
      have hS : affSum 6 (Ay ν χf A) s ≤ s ^ (5 / 2 : ℝ) * affM ν χf A := by
        calc affSum 6 (Ay ν χf A) s
            = s ^ (5 / 2 : ℝ) * (s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χf A) s) := by
              rw [← mul_assoc, hinv, one_mul]
          _ ≤ s ^ (5 / 2 : ℝ) * affM ν χf A := mul_le_mul_of_nonneg_left hsup hq
      calc |sDerivIter i (Ay ν χf A) s a b|
          ≤ frob (sDerivIter i (Ay ν χf A) s) := t7_abs_le_frob _ a b
        _ ≤ affSum 6 (Ay ν χf A) s := hterm
        _ ≤ s ^ (5 / 2 : ℝ) * affM ν χf A := hS
        _ = affM ν χf A * s ^ (5 / 2 : ℝ) := mul_comm _ _
  · rw [hvan s hs']
    simp

end UnforcedLeray.Short.PartIIIb.Concrete
