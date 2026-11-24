import UnforcedLeray.Short.PartIIIb.Tasks

/-!
# Proof of `T_mixedReturn` (target `mixedReturn`; source: `the November 2 reference manuscript`, lines 5744-5774)

`T_mixedReturn = MR_Reduce → MR_Crossing → T_schurContinuity → MixedReturnLemma`.
Given the three helpers, we prove `MixedReturnLemma` (statement 5717-5742):

* suprema over `Icc (-1) 1` of the continuous norms are attained bounds (`mr_le_iSup`);
* `d n := 1 - ℓ n (w n)`, `w n = schurSol …`, is continuous for `n ≥ N` (`T_schurContinuity`)
  and converges uniformly to `1 - e^{-z}` (`MR_Reduce` deviation bound, `r n + h n → 0`);
  for `n < N` it is replaced by `1 - e^{-z}`;
* `MR_Crossing` gives zeros `z n → 0`; at a zero `ℓ w = 1` and `MR_Reduce` gives the nonzero
  block solution `(w, (I - C)⁻¹ B w)`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set

namespace UnforcedLeray.Short.PartIIIb

/-- A continuous real function on `Icc (-1) 1` is bounded by its supremum over the interval
(the interval is compact, so the supremum is finite). -/
theorem mr_le_iSup (g : ℝ → ℝ) (hg : ContinuousOn g (Icc (-1 : ℝ) 1)) :
    ∀ z ∈ Icc (-1 : ℝ) 1, g z ≤ ⨆ w : Icc (-1 : ℝ) 1, g w := by
  intro z hz
  have hbdd : BddAbove (Set.range fun w : Icc (-1 : ℝ) 1 => g w) := by
    obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hg).bddAbove
    refine ⟨M, ?_⟩
    rintro _ ⟨w, rfl⟩
    exact (mem_upperBounds.1 hM) (g w) ⟨(w : ℝ), w.2, rfl⟩
  exact le_ciSup hbdd ⟨z, hz⟩

/-- `MixedReturnLemma` (lines 5717-5742) from the three helper statements, with the suprema
`c n`, `r n`, `h n` given as abstract real sequences satisfying their defining bounds. -/
theorem mr_core (E X : ℕ → Type)
    [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)] [∀ n, CompleteSpace (E n)]
    [∀ n, NormedAddCommGroup (X n)] [∀ n, NormedSpace ℝ (X n)] [∀ n, CompleteSpace (X n)]
    (K : ∀ n, ℝ → E n →L[ℝ] E n) (A : ∀ n, ℝ → X n →L[ℝ] E n)
    (B : ∀ n, ℝ → E n →L[ℝ] X n) (C : ∀ n, ℝ → X n →L[ℝ] X n)
    (a : ∀ n, ℝ → E n) (ℓ : ∀ n, ℝ → E n →L[ℝ] ℝ) (R : ∀ n, ℝ → E n →L[ℝ] E n) (M : ℝ)
    (c r h : ℕ → ℝ)
    (hA : ∀ n, ContinuousOn (A n) (Icc (-1 : ℝ) 1))
    (hB : ∀ n, ContinuousOn (B n) (Icc (-1 : ℝ) 1))
    (hC : ∀ n, ContinuousOn (C n) (Icc (-1 : ℝ) 1))
    (ha : ∀ n, ContinuousOn (a n) (Icc (-1 : ℝ) 1))
    (hℓ : ∀ n, ContinuousOn (ℓ n) (Icc (-1 : ℝ) 1))
    (hR : ∀ n, ContinuousOn (R n) (Icc (-1 : ℝ) 1))
    (hKdef : ∀ n, ∀ z ∈ Icc (-1 : ℝ) 1, K n z = (ℓ n z).smulRight (a n z) + R n z)
    (hM : ∀ n, ∀ z ∈ Icc (-1 : ℝ) 1, ‖a n z‖ * ‖ℓ n z‖ ≤ M)
    (hcC : ∀ n, ∀ z ∈ Icc (-1 : ℝ) 1, ‖C n z‖ ≤ c n)
    (hc1 : ∀ n, c n < 1)
    (hrR : ∀ n, ∀ z ∈ Icc (-1 : ℝ) 1, ‖R n z‖ ≤ r n)
    (hhAB : ∀ n, ∀ z ∈ Icc (-1 : ℝ) 1, ‖A n z‖ * ‖B n z‖ / (1 - c n) ≤ h n)
    (hsum : Tendsto (fun n => r n + h n) atTop (𝓝 0))
    (hunif : TendstoUniformlyOn (fun n z => ℓ n z (a n z)) (fun z => Real.exp (-z)) atTop
      (Icc (-1 : ℝ) 1))
    (mrReduce : MR_Reduce) (mrCrossing : MR_Crossing) (schurCont : T_schurContinuity) :
    ∃ z : ℕ → ℝ, Tendsto z atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, z n ∈ Ioo (-1 : ℝ) 1 ∧
        ∃ x : E n, x ≠ 0 ∧ ∃ y : X n,
          x = K n (z n) x + A n (z n) y ∧ y = B n (z n) x + C n (z n) y := by
  have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hr0 : ∀ n, 0 ≤ r n := fun n => le_trans (norm_nonneg _) (hrR n 0 h0)
  have hh0 : ∀ n, 0 ≤ h n := by
    intro n
    have hpos : (0 : ℝ) ≤ 1 - c n := by linarith [hc1 n]
    have hnn : 0 ≤ ‖A n 0‖ * ‖B n 0‖ / (1 - c n) :=
      div_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hpos
    exact le_trans hnn (hhAB n 0 h0)
  -- eventually `r n + h n < 1/2`
  have hq : ∀ᶠ n in atTop, r n + h n < 1 / 2 :=
    hsum.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hq
  have hlt : ∀ n, N ≤ n → r n + h n < 1 := fun n hn => by linarith [hN n hn]
  -- the deviation coefficient tends to zero
  have hcont0 : ContinuousAt (fun t : ℝ => M * (t / (1 - t))) 0 := by
    apply ContinuousAt.mul continuousAt_const
    apply ContinuousAt.div continuousAt_id (continuousAt_const.sub continuousAt_id)
    norm_num
  have he : Tendsto (fun n => M * ((r n + h n) / (1 - (r n + h n)))) atTop (𝓝 0) := by
    have hcomp := hcont0.tendsto.comp hsum
    have hval : M * ((0 : ℝ) / (1 - 0)) = 0 := by simp
    rw [hval] at hcomp
    exact hcomp
  -- the continuous family `d n`, replaced by `1 - e^{-z}` for `n < N`
  obtain ⟨d, hdN, hdlt⟩ : ∃ d : ℕ → ℝ → ℝ,
      (∀ n, N ≤ n → ∀ z, d n z = 1 - ℓ n z (schurSol (A n z) (B n z) (C n z) (R n z) (a n z))) ∧
      (∀ n, n < N → ∀ z, d n z = 1 - Real.exp (-z)) :=
    ⟨fun n z => if N ≤ n then 1 - ℓ n z (schurSol (A n z) (B n z) (C n z) (R n z) (a n z))
        else 1 - Real.exp (-z),
      fun n hn z => by simp [hn],
      fun n hn z => by simp [not_le.2 hn]⟩
  have hdcont : ∀ n, ContinuousOn (d n) (Icc (-1 : ℝ) 1) := by
    intro n
    by_cases hn : N ≤ n
    · have hfun : d n = fun z => 1 - ℓ n z (schurSol (A n z) (B n z) (C n z) (R n z) (a n z)) :=
        funext (hdN n hn)
      rw [hfun]
      have hq1 : ∀ z ∈ Icc (-1 : ℝ) 1,
          ‖schurTilde (A n z) (B n z) (C n z) (R n z)‖ ≤ r n + h n := fun z hz =>
        (mrReduce (A n z) (B n z) (C n z) (R n z) (a n z) (ℓ n z) (c n) (r n) (h n)
          (hcC n z hz) (hc1 n) (hrR n z hz) (hhAB n z hz) (hlt n hn)).1
      exact continuousOn_const.sub
        (schurCont (A n) (B n) (C n) (R n) (a n) (ℓ n) (c n) (r n + h n)
          (hA n) (hB n) (hC n) (hR n) (ha n) (hℓ n) (hcC n) (hc1 n) hq1 (hlt n hn))
    · have hfun : d n = fun z => 1 - Real.exp (-z) := funext (hdlt n (not_le.1 hn))
      rw [hfun]
      exact (by fun_prop : Continuous fun z : ℝ => 1 - Real.exp (-z)).continuousOn
  -- uniform convergence of `d n` to `1 - e^{-z}` on `[-1,1]`
  have hdunif : TendstoUniformlyOn d (fun z => 1 - Real.exp (-z)) atTop (Icc (-1 : ℝ) 1) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have h1 : ∀ᶠ n in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
        dist (Real.exp (-z)) (ℓ n z (a n z)) < ε / 2 :=
      Metric.tendstoUniformlyOn_iff.1 hunif (ε / 2) (half_pos hε)
    have h2 : ∀ᶠ n in atTop, M * ((r n + h n) / (1 - (r n + h n))) < ε / 2 :=
      he.eventually (gt_mem_nhds (half_pos hε))
    filter_upwards [h1, h2, eventually_ge_atTop N] with n hn1 hn2 hnN
    intro z hz
    have hA1 : |Real.exp (-z) - ℓ n z (a n z)| < ε / 2 := by
      have := hn1 z hz
      rwa [Real.dist_eq] at this
    have hbound := (mrReduce (A n z) (B n z) (C n z) (R n z) (a n z) (ℓ n z) (c n) (r n) (h n)
      (hcC n z hz) (hc1 n) (hrR n z hz) (hhAB n z hz) (hlt n hnN)).2.1
    have hLa : ‖ℓ n z‖ * ‖a n z‖ ≤ M := (mul_comm _ _).trans_le (hM n z hz)
    have hq0 : 0 ≤ (r n + h n) / (1 - (r n + h n)) :=
      div_nonneg (add_nonneg (hr0 n) (hh0 n)) (by linarith [hlt n hnN])
    have hbd := mul_le_mul_of_nonneg_right hLa hq0
    have hB' := abs_le.1 (hbound.trans hbd)
    have hA' := abs_lt.1 hA1
    have key : |1 - Real.exp (-z) - (1 - ℓ n z (schurSol (A n z) (B n z) (C n z) (R n z)
        (a n z)))| < ε := by
      apply abs_lt.2
      constructor <;> linarith [hB'.1, hB'.2, hA'.1, hA'.2, hn2]
    rw [hdN n hnN z, Real.dist_eq]
    exact key
  -- zeros of `d n` and the block solution
  obtain ⟨z, hz0, hzev⟩ := mrCrossing d hdcont hdunif
  refine ⟨z, hz0, ?_⟩
  filter_upwards [hzev, eventually_ge_atTop N] with n hn hnN
  obtain ⟨hzn, hdz⟩ := hn
  have hzI : z n ∈ Icc (-1 : ℝ) 1 := Ioo_subset_Icc_self hzn
  have hl1 : ℓ n (z n) (schurSol (A n (z n)) (B n (z n)) (C n (z n)) (R n (z n))
      (a n (z n))) = 1 := by
    rw [hdN n hnN (z n)] at hdz
    linarith
  obtain ⟨-, -, hz3⟩ := mrReduce (A n (z n)) (B n (z n)) (C n (z n)) (R n (z n)) (a n (z n))
    (ℓ n (z n)) (c n) (r n) (h n) (hcC n (z n) hzI) (hc1 n) (hrR n (z n) hzI)
    (hhAB n (z n) hzI) (hlt n hnN)
  obtain ⟨hw0, hwe, hye⟩ := hz3 hl1
  refine ⟨hzn, schurSol (A n (z n)) (B n (z n)) (C n (z n)) (R n (z n)) (a n (z n)), hw0,
    Ring.inverse (1 - C n (z n))
      (B n (z n) (schurSol (A n (z n)) (B n (z n)) (C n (z n)) (R n (z n)) (a n (z n)))),
    ?_, hye⟩
  rw [hKdef n (z n) hzI, add_apply, ContinuousLinearMap.smulRight_apply]
  exact hwe

/-- `T_mixedReturn`: the implication `MR_Reduce → MR_Crossing → T_schurContinuity →
MixedReturnLemma` (source lines 5744-5774). -/
theorem mixedReturn : UnforcedLeray.Short.PartIIIb.T_mixedReturn := by
  unfold T_mixedReturn
  intro mrReduce mrCrossing schurCont
  unfold MixedReturnLemma
  intro E X _ _ _ _ _ _ K A B C a ℓ R M _hK hA hB hC ha hℓ hR hKdef hM hc hlim hunif
  exact mr_core E X K A B C a ℓ R M
    (fun n => ⨆ z : Icc (-1 : ℝ) 1, ‖C n z‖)
    (fun n => ⨆ z : Icc (-1 : ℝ) 1, ‖R n z‖)
    (fun n => (⨆ z : Icc (-1 : ℝ) 1, ‖A n z‖ * ‖B n z‖) / (1 - ⨆ z : Icc (-1 : ℝ) 1, ‖C n z‖))
    hA hB hC ha hℓ hR hKdef hM
    (fun n z hz => mr_le_iSup _ (hC n).norm z hz)
    hc
    (fun n z hz => mr_le_iSup _ (hR n).norm z hz)
    (fun n z hz => div_le_div_of_nonneg_right
      (mr_le_iSup _ ((hA n).norm.mul (hB n).norm) z hz)
      (by linarith [hc n]))
    hlim hunif mrReduce mrCrossing schurCont

end UnforcedLeray.Short.PartIIIb
