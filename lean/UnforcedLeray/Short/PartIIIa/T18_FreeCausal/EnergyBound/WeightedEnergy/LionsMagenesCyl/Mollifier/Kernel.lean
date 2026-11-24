import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.Mollifier.Unfold

/-!
# Part III-a, `PartIII-a:T18/3/1/3/1`: the periodized kernel

Source of record: `the November 2 reference manuscript` lines 3427-3440 and
3541-3552. Smoothness, partial derivatives, evenness and unit mass of the periodized kernel
`lmK c k`, and the fact that `y ↦ K_k(x - y)` is a test function on the cylinder.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff Convolution

namespace UnforcedLeray.Short.IIIa

/-- Near each point the periodized kernel is one translate of the bump. -/
theorem lmK_eventuallyEq {c : ℝ} (hc : 0 < c) (k : ℕ) (z : ℝ × ℝ) :
    ∃ n : ℤ, lmPer c z = (z.1 - n * c, z.2) ∧
      ∀ᶠ w in 𝓝 z, lmK c k w = lmRho c k (w.1 - n * c, w.2) := by
  obtain ⟨n, hn⟩ := lmPer1_sub_self hc.ne' z.1
  have hmem := lmPer1_mem hc z.1
  rw [hn] at hmem
  refine ⟨n, by simp [lmPer, hn], ?_⟩
  have hnear : ∀ᶠ w : ℝ × ℝ in 𝓝 z, w.1 ∈ Ioo (z.1 - c / 8) (z.1 + c / 8) :=
    continuous_fst.tendsto z |>.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  filter_upwards [hnear] with w hw
  by_cases h1 : w.1 - n * c < -(c / 2)
  · have hlow : -(c / 2) ≤ w.1 - ((n - 1 : ℤ) : ℝ) * c ∧ w.1 - ((n - 1 : ℤ) : ℝ) * c < c / 2 := by
      push_cast
      constructor <;> nlinarith [hw.1, hw.2, hmem.1, hmem.2]
    have hper := lmPer1_eq_sub_int hc (t := w.1) (n - 1) hlow
    have hL : lmK c k w = 0 := by
      show lmRho c k (lmPer1 c w.1, w.2) = 0
      refine lmRho_eq_zero hc k (Or.inl ?_)
      show c / 4 ≤ |lmPer1 c w.1|
      rw [hper]
      push_cast
      rw [abs_of_nonneg (by nlinarith [hw.1, hmem.1])]
      nlinarith [hw.1, hmem.1]
    have hR : lmRho c k (w.1 - n * c, w.2) = 0 := by
      refine lmRho_eq_zero hc k (Or.inl ?_)
      show c / 4 ≤ |w.1 - n * c|
      rw [abs_of_neg (by linarith)]
      linarith
    rw [hL, hR]
  · push Not at h1
    by_cases h2 : w.1 - n * c < c / 2
    · have hper := lmPer1_eq_sub_int hc (t := w.1) n ⟨h1, h2⟩
      show lmRho c k (lmPer1 c w.1, w.2) = _
      rw [hper]
    · push Not at h2
      have hhigh : -(c / 2) ≤ w.1 - ((n + 1 : ℤ) : ℝ) * c ∧ w.1 - ((n + 1 : ℤ) : ℝ) * c < c / 2 := by
        push_cast
        constructor <;> nlinarith [hw.1, hw.2, hmem.1, hmem.2]
      have hper := lmPer1_eq_sub_int hc (t := w.1) (n + 1) hhigh
      have hL : lmK c k w = 0 := by
        show lmRho c k (lmPer1 c w.1, w.2) = 0
        refine lmRho_eq_zero hc k (Or.inl ?_)
        show c / 4 ≤ |lmPer1 c w.1|
        rw [hper]
        push_cast
        rw [abs_of_nonpos (by nlinarith [hw.2, hmem.2])]
        nlinarith [hw.2, hmem.2]
      have hR : lmRho c k (w.1 - n * c, w.2) = 0 := by
        refine lmRho_eq_zero hc k (Or.inl ?_)
        show c / 4 ≤ |w.1 - n * c|
        rw [abs_of_nonneg (by linarith)]
        linarith
      rw [hL, hR]

theorem lmK_contDiff {c : ℝ} (hc : 0 < c) (k : ℕ) : ContDiff ℝ ∞ (lmK c k) := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  obtain ⟨n, -, hn⟩ := lmK_eventuallyEq hc k z
  have hs : ContDiff ℝ ∞ (fun w : ℝ × ℝ => lmRho c k (w.1 - n * c, w.2)) :=
    (lmRho_contDiff c k).comp (by fun_prop)
  exact hs.contDiffAt.congr_of_eventuallyEq hn

theorem lmK_pd {c : ℝ} (hc : 0 < c) (k : ℕ) (j : Fin 2) (z : ℝ × ℝ) :
    B0579.pd j (lmK c k) z = B0579.pd j (lmRho c k) (lmPer c z) := by
  obtain ⟨n, hz, hn⟩ := lmK_eventuallyEq hc k z
  have heq : (fun w : ℝ × ℝ => lmRho c k (w.1 - n * c, w.2)) =
      fun w => lmRho c k (w + ((-(n * c), 0) : ℝ × ℝ)) := by
    funext w
    congr 1
    ext <;> simp [sub_eq_add_neg]
  have hz' : z + ((-(n * c), 0) : ℝ × ℝ) = lmPer c z := by
    rw [hz]
    ext <;> simp [sub_eq_add_neg]
  unfold B0579.pd
  rw [Filter.EventuallyEq.fderiv_eq hn, heq, fderiv_comp_add_right, hz']

theorem lmK_neg {c : ℝ} (hc : 0 < c) (k : ℕ) (z : ℝ × ℝ) : lmK c k (-z) = lmK c k z := by
  obtain ⟨n, hn⟩ := lmPer1_sub_self hc.ne' z.1
  have hmem := lmPer1_mem hc z.1
  by_cases hend : lmPer1 c z.1 = -(c / 2)
  · -- the seam: both values vanish
    have hL : lmK c k z = 0 := by
      show lmRho c k (lmPer1 c z.1, z.2) = 0
      refine lmRho_eq_zero hc k (Or.inl ?_)
      show c / 4 ≤ |lmPer1 c z.1|
      rw [hend, abs_neg, abs_of_pos (by positivity)]
      linarith
    have hR : lmK c k (-z) = 0 := by
      show lmRho c k (lmPer1 c (-z).1, (-z).2) = 0
      refine lmRho_eq_zero hc k (Or.inl ?_)
      show c / 4 ≤ |lmPer1 c (-z).1|
      have hval : z.1 - n * c = -(c / 2) := by rw [← hn, hend]
      have hper := lmPer1_eq_sub_int hc (t := (-z).1) (1 - n) (by
        rw [Prod.fst_neg]
        push_cast
        constructor <;> nlinarith)
      rw [hper, Prod.fst_neg]
      push_cast
      have : -z.1 - (1 - (n : ℝ)) * c = -(c / 2) := by nlinarith
      rw [this, abs_neg, abs_of_pos (by positivity)]
      linarith
    rw [hL, hR]
  · have hgt : -(c / 2) < lmPer1 c z.1 := lt_of_le_of_ne hmem.1 (Ne.symm hend)
    have hper := lmPer1_eq_sub_int hc (t := (-z).1) (-n) (by
      rw [Prod.fst_neg, hn] at *
      push_cast
      constructor <;> nlinarith [hmem.1, hmem.2])
    have hP : lmPer c (-z) = -lmPer c z := by
      ext
      · show lmPer1 c (-z).1 = -lmPer1 c z.1
        rw [hper, hn, Prod.fst_neg]
        push_cast
        ring
      · rfl
    show lmRho c k (lmPer c (-z)) = lmRho c k (lmPer c z)
    rw [hP, lmRho_neg]

theorem lmK_integral_cell {c : ℝ} (hc : 0 < c) (k : ℕ) (x : ℝ × ℝ) :
    ∫ y in B0579.cell c, lmK c k (x - y) = 1 := by
  have hh : ∀ z : ℝ × ℝ, c / 3 ≤ |z.1| → lmRho c k z = 0 := fun z hz =>
    lmRho_eq_zero hc k (Or.inl (by linarith))
  have h := lm_cell_unfold hc hh (g := fun _ => (1 : ℂ)) (fun _ => rfl) x
  simp only [mul_one] at h
  rw [integral_complex_ofReal, integral_complex_ofReal] at h
  have h1 : ∫ y, lmRho c k (x - y) = 1 := by
    rw [integral_sub_left_eq_self (lmRho c k) volume x, lmRho_integral]
  rw [h1] at h
  have h2 : (((∫ y in B0579.cell c, lmRho c k (lmPer c (x - y)) : ℝ)) : ℂ) = ((1 : ℝ) : ℂ) := h
  exact Complex.ofReal_inj.mp h2

/-- `y ↦ K_k(x - y)` is a test function on the cylinder, with derivative `-∂_j K_k (x - y)`. -/
theorem lmK_test {c : ℝ} (hc : 0 < c) (k : ℕ) (x : ℝ × ℝ) :
    B0579.IsCylTest c (fun y => lmK c k (x - y)) ∧
      ∀ (j : Fin 2) (y : ℝ × ℝ),
        B0579.pd j (fun y => lmK c k (x - y)) y = -B0579.pd j (lmK c k) (x - y) := by
  refine ⟨⟨(lmK_contDiff hc k).comp (by fun_prop), fun y => ?_, ⟨|x.2| + c / 4, fun y hy => ?_⟩⟩,
    fun j y => ?_⟩
  · have h2 : x - (y.1 + c, y.2) = ((x - y).1 - c, (x - y).2) := by
      ext <;> simp
      ring
    simp only [lmK]
    rw [h2]
    simp only [lmPer, lmPer1_sub hc.ne']
  · refine lmK_eq_zero_of_snd hc k ?_
    rw [Prod.snd_sub]
    have h1 : |y.2| ≤ |x.2| + |x.2 - y.2| := by
      have := abs_sub_abs_le_abs_sub y.2 x.2
      rw [abs_sub_comm y.2 x.2] at this
      linarith
    linarith
  · have hd : DifferentiableAt ℝ (lmK c k) (x - y) :=
      ((lmK_contDiff hc k).differentiable (by simp)) _
    have h := (hd.hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x)).fderiv
    have h' : fderiv ℝ (fun y => lmK c k (x - y)) y = (fderiv ℝ (lmK c k) (x - y)).comp
        (-ContinuousLinearMap.id ℝ (ℝ × ℝ)) := h
    unfold B0579.pd
    rw [h']
    simp
end UnforcedLeray.Short.IIIa
