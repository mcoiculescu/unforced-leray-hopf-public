import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlanePeriodicLimit.Sequence.AvgDual

/-!
# Part II-b, task `PartII-b:T12/1/4/1/6` (`PPLDualLimit`): the Riemann-sum limit

Source of record: `the November 2 reference manuscript` lines 1933-1935.

Let `supp Ψ ⊆ closedBall 0 R` and `K` with `R ≤ K c`. The translate pairings
`T_j(N) = ∫ F_N(z)·Ψ(z - jc e_q)` are: `0` for `j ≤ -K-1` (the cut is zero on the support),
`∫ F·Ψ` for `K ≤ j ≤ N-K-1` (periodicity inside the cut), and bounded uniformly in `N, j`
otherwise. Since `∫ F_N·ppDual Ψ = N⁻¹ Σ_{|j|≤N} T_j(N)`, only `O(K)` terms are not exact, so the
average tends to `∫ F·Ψ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Integer multiples of the period in `q`. -/
theorem dl_periodic_int {c : ℝ} {F : ℝ × ℝ → CMerid} (hF : ∀ z : ℝ × ℝ, F (z.1 + c, z.2) = F z)
    (n : ℤ) (z : ℝ × ℝ) : F (z.1 + (n : ℝ) * c, z.2) = F z := by
  have hp : Function.Periodic (fun t : ℝ => F (t, z.2)) c := fun t => hF (t, z.2)
  exact hp.int_mul n z.1

/-- Points of a closed ball have bounded first coordinate. -/
theorem dl_ball_abs {R : ℝ} {w : ℝ × ℝ} (hw : w ∈ Metric.closedBall (0 : ℝ × ℝ) R) :
    |w.1| ≤ R := by
  have h1 : ‖w‖ ≤ R := mem_closedBall_zero_iff.1 hw
  have h2 := norm_fst_le w
  rw [Real.norm_eq_abs] at h2
  linarith

/-- A natural multiple `K c` of the period dominates the first coordinate on the ball. -/
theorem dl_K (c R : ℝ) (hc : 0 < c) :
    ∃ K : ℕ, ∀ w : ℝ × ℝ, w ∈ Metric.closedBall (0 : ℝ × ℝ) R → |w.1| ≤ (K : ℝ) * c := by
  refine ⟨⌈R / c⌉₊, fun w hw => ?_⟩
  have h1 := dl_ball_abs hw
  have h2 : R / c ≤ (⌈R / c⌉₊ : ℝ) := Nat.le_ceil _
  have h3 : R ≤ (⌈R / c⌉₊ : ℝ) * c := (div_le_iff₀ hc).1 h2
  linarith

/-- A planar solenoidal test vanishes outside a fixed ball. -/
theorem dl_support (Ψ : ℝ × ℝ → Fin 2 → ℝ) (hΨ : PlaneSolTest Ψ) :
    ∃ R : ℝ, ∀ w : ℝ × ℝ, w ∉ Metric.closedBall (0 : ℝ × ℝ) R → Ψ w = 0 := by
  obtain ⟨R0, h0⟩ := ((hΨ.comp 0).compact.isCompact).isBounded.subset_closedBall (0 : ℝ × ℝ)
  obtain ⟨R1, h1⟩ := ((hΨ.comp 1).compact.isCompact).isBounded.subset_closedBall (0 : ℝ × ℝ)
  refine ⟨max R0 R1, fun w hw => ?_⟩
  have key0 : Ψ w 0 = 0 := image_eq_zero_of_notMem_tsupport (f := fun z => Ψ z 0)
    (fun hmem => hw (Metric.closedBall_subset_closedBall (le_max_left _ _) (h0 hmem)))
  have key1 : Ψ w 1 = 0 := image_eq_zero_of_notMem_tsupport (f := fun z => Ψ z 1)
    (fun hmem => hw (Metric.closedBall_subset_closedBall (le_max_right _ _) (h1 hmem)))
  funext i
  fin_cases i
  · exact key0
  · exact key1

/-- The `j`-th translate pairing of the cut `F_N` with `Ψ(· - jc e_q)`. -/
def dlT (c : ℝ) (N : ℕ) (F : ℝ × ℝ → CMerid) (Ψ : ℝ × ℝ → Fin 2 → ℝ) (j : ℤ) : ℂ :=
  ∫ z, ∑ i : Fin 2, ppCut c N F z i * (Ψ (z.1 - (j : ℝ) * c, z.2) i : ℂ)

/-- Translation to the cell variable: `T_j = ∫ F_N(w + jc e_q)·Ψ(w)`. -/
theorem dl_translate (c : ℝ) (N : ℕ) (F : ℝ × ℝ → CMerid) (Ψ : ℝ × ℝ → Fin 2 → ℝ) (j : ℤ) :
    dlT c N F Ψ j = ∫ w : ℝ × ℝ,
      ∑ i : Fin 2, ppCut c N F (w + ((j : ℝ) * c, (0 : ℝ))) i * (Ψ w i : ℂ) := by
  unfold dlT
  rw [← integral_sub_right_eq_self (fun w : ℝ × ℝ => ∑ i : Fin 2,
    ppCut c N F (w + ((j : ℝ) * c, (0 : ℝ))) i * (Ψ w i : ℂ)) ((j : ℝ) * c, (0 : ℝ))]
  congr 1
  funext z
  have hv : z - ((j : ℝ) * c, (0 : ℝ)) = (z.1 - (j : ℝ) * c, z.2) := by
    ext <;> simp
  simp only [sub_add_cancel]
  rw [hv]

/-- Translates with `j ≤ -K-1` vanish: the cut is zero where the test is supported. -/
theorem dl_zero_low (c : ℝ) (hc : 0 < c) (N : ℕ) (F : ℝ × ℝ → CMerid) (Ψ : ℝ × ℝ → Fin 2 → ℝ)
    (R : ℝ) (hR : ∀ w : ℝ × ℝ, w ∉ Metric.closedBall (0 : ℝ × ℝ) R → Ψ w = 0) (K : ℕ)
    (hK : ∀ w : ℝ × ℝ, w ∈ Metric.closedBall (0 : ℝ × ℝ) R → |w.1| ≤ (K : ℝ) * c) (j : ℤ)
    (hj : j ≤ -(K : ℤ) - 1) : dlT c N F Ψ j = 0 := by
  unfold dlT
  have hz : ∀ z : ℝ × ℝ,
      ∑ i : Fin 2, ppCut c N F z i * (Ψ (z.1 - (j : ℝ) * c, z.2) i : ℂ) = 0 := by
    intro z
    by_cases hz1 : 0 ≤ z.1
    · have hnot : (z.1 - (j : ℝ) * c, z.2) ∉ Metric.closedBall (0 : ℝ × ℝ) R := by
        intro hmem
        have h1 := (abs_le.1 (hK _ hmem)).2
        have hjc : (j : ℝ) ≤ -(K : ℝ) - 1 := by exact_mod_cast hj
        have h2 : (j : ℝ) * c ≤ (-(K : ℝ) - 1) * c := mul_le_mul_of_nonneg_right hjc hc.le
        have h3 : (-(K : ℝ) - 1) * c = -((K : ℝ) * c) - c := by ring
        simp only at h1
        linarith
      rw [hR _ hnot]
      simp
    · have hz0 : ppCut c N F z = 0 := by
        simp [ppCut, Set.indicator_apply, hz1]
      simp [hz0]
  simp only [hz, integral_zero]

/-- Translates with `K ≤ j ≤ N-K-1` equal the full pairing `∫ F·Ψ`. -/
theorem dl_good (c : ℝ) (hc : 0 < c) (N : ℕ) (F : ℝ × ℝ → CMerid)
    (hF : ∀ z : ℝ × ℝ, F (z.1 + c, z.2) = F z) (Ψ : ℝ × ℝ → Fin 2 → ℝ) (R : ℝ)
    (hR : ∀ w : ℝ × ℝ, w ∉ Metric.closedBall (0 : ℝ × ℝ) R → Ψ w = 0) (K : ℕ)
    (hK : ∀ w : ℝ × ℝ, w ∈ Metric.closedBall (0 : ℝ × ℝ) R → |w.1| ≤ (K : ℝ) * c) (j : ℤ)
    (hjK : (K : ℤ) ≤ j) (hjN : j ≤ (N : ℤ) - K - 1) :
    dlT c N F Ψ j = ∫ z, ∑ i : Fin 2, F z i * (Ψ z i : ℂ) := by
  rw [dl_translate]
  congr 1
  funext w
  by_cases hw : w ∈ Metric.closedBall (0 : ℝ × ℝ) R
  · have habs := abs_le.1 (hK w hw)
    have hjK' : (K : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjK
    have hjN' : (j : ℝ) ≤ (N : ℝ) - K - 1 := by
      have h := (show (j : ℝ) ≤ (((N : ℤ) - K - 1 : ℤ) : ℝ) by exact_mod_cast hjN)
      push_cast at h
      linarith
    have hc1 : (K : ℝ) * c ≤ (j : ℝ) * c := mul_le_mul_of_nonneg_right hjK' hc.le
    have hc2 : (j : ℝ) * c ≤ ((N : ℝ) - K - 1) * c := mul_le_mul_of_nonneg_right hjN' hc.le
    have hexp : ((N : ℝ) - K - 1) * c = (N : ℝ) * c - K * c - c := by ring
    have hmem : (w.1 + (j : ℝ) * c, w.2) ∈ {z : ℝ × ℝ | 0 ≤ z.1 ∧ z.1 < (N : ℝ) * c} :=
      ⟨by show (0 : ℝ) ≤ w.1 + (j : ℝ) * c; linarith [habs.1],
        by show w.1 + (j : ℝ) * c < (N : ℝ) * c; linarith [habs.2]⟩
    have hpc : ppCut c N F (w + ((j : ℝ) * c, (0 : ℝ))) = F w := by
      have hw2 : w + ((j : ℝ) * c, (0 : ℝ)) = (w.1 + (j : ℝ) * c, w.2) := by ext <;> simp
      rw [hw2]
      unfold ppCut
      rw [Set.indicator_of_mem hmem]
      exact dl_periodic_int hF j w
    simp only [hpc]
  · rw [hR w hw]
    simp

/-- Uniform bound on the translate pairings. -/
theorem dl_bound (c : ℝ) (hc : 0 < c) (N : ℕ) (F : ℝ × ℝ → CMerid)
    (hF : ∀ z : ℝ × ℝ, F (z.1 + c, z.2) = F z)
    (hFl : ∀ R : ℝ, IntegrableOn F (Metric.closedBall (0 : ℝ × ℝ) R) volume)
    (Ψ : ℝ × ℝ → Fin 2 → ℝ) (R : ℝ)
    (hR : ∀ w : ℝ × ℝ, w ∉ Metric.closedBall (0 : ℝ × ℝ) R → Ψ w = 0) (M : ℝ)
    (hM : ∀ w : ℝ × ℝ, ‖Ψ w‖ ≤ M) (j : ℤ) :
    ‖dlT c N F Ψ j‖ ≤
      ∫ w, (Metric.closedBall (0 : ℝ × ℝ) R).indicator (fun w => 2 * M * ‖F w‖) w := by
  classical
  rw [dl_translate]
  refine norm_integral_le_of_norm_le ?_ (Eventually.of_forall fun w => ?_)
  · exact (integrable_indicator_iff measurableSet_closedBall).2
      ((hFl R).norm.const_mul (2 * M))
  · by_cases hw : w ∈ Metric.closedBall (0 : ℝ × ℝ) R
    · rw [Set.indicator_of_mem hw]
      have hwv : w + ((j : ℝ) * c, (0 : ℝ)) = (w.1 + (j : ℝ) * c, w.2) := by ext <;> simp
      have hp : ‖ppCut c N F (w + ((j : ℝ) * c, (0 : ℝ)))‖ ≤ ‖F w‖ := by
        rw [hwv]
        unfold ppCut
        refine (norm_indicator_le_norm_self F _).trans (le_of_eq ?_)
        exact congrArg norm (dl_periodic_int hF j w)
      calc ‖∑ i : Fin 2, ppCut c N F (w + ((j : ℝ) * c, (0 : ℝ))) i * (Ψ w i : ℂ)‖
          ≤ ∑ i : Fin 2, ‖ppCut c N F (w + ((j : ℝ) * c, (0 : ℝ))) i * (Ψ w i : ℂ)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _i : Fin 2, ‖F w‖ * M := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            rw [norm_mul, Complex.norm_real]
            have h1 : ‖ppCut c N F (w + ((j : ℝ) * c, (0 : ℝ))) i‖ ≤ ‖F w‖ :=
              (PiLp.norm_apply_le _ i).trans hp
            have h2 : ‖Ψ w i‖ ≤ M := (norm_le_pi_norm (Ψ w) i).trans (hM w)
            exact mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
        _ = 2 * M * ‖F w‖ := by
            simp [Fin.sum_univ_two]
            ring
    · rw [Set.indicator_apply, if_neg hw, hR w hw]
      simp

/-- The sum formula `∫ F_N·ppDual Ψ = N⁻¹ Σ_{|j|≤N} T_j`. -/
theorem dl_sum_eq (c : ℝ) (hc : 0 < c) (N : ℕ) (F : ℝ × ℝ → CMerid) (Ψ : ℝ × ℝ → Fin 2 → ℝ)
    (hF : CylLp c 2 F) (hΨ : PlaneSolTest Ψ) :
    ∫ z, ∑ i : Fin 2, ppCut c N F z i * (ppDual c N Ψ z i : ℂ) =
      (N : ℂ)⁻¹ * ∑ j ∈ Finset.Icc (-(N : ℤ)) N, dlT c N F Ψ j := by
  have hS : MeasurableSet {z : ℝ × ℝ | 0 ≤ z.1 ∧ z.1 < (N : ℝ) * c} :=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_const)
  have hFNl : ∀ R : ℝ, IntegrableOn (ppCut c N F) (Metric.closedBall (0 : ℝ × ℝ) R) volume :=
    fun R => (avd_integrableOn_ball hc hF 0 R).indicator hS
  have hY : ∀ j : ℤ, Integrable (fun z : ℝ × ℝ =>
      ∑ i : Fin 2, ppCut c N F z i * (Ψ (z.1 - (j : ℝ) * c, z.2) i : ℂ)) volume :=
    fun j => avd_sum_integrable hFNl (fun i => (avd_planeSolTest_shift hΨ ((j : ℝ) * c)).comp i)
  have K3 : ∀ z : ℝ × ℝ, ∑ i : Fin 2, ppCut c N F z i * (ppDual c N Ψ z i : ℂ) =
      (N : ℂ)⁻¹ * ∑ j ∈ Finset.Icc (-(N : ℤ)) N,
        ∑ i : Fin 2, ppCut c N F z i * (Ψ (z.1 - (j : ℝ) * c, z.2) i : ℂ) := by
    intro z
    simp only [ppDual, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_inv,
      Complex.ofReal_natCast, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by ring))
  calc ∫ z, ∑ i : Fin 2, ppCut c N F z i * (ppDual c N Ψ z i : ℂ)
      = ∫ z, (N : ℂ)⁻¹ * ∑ j ∈ Finset.Icc (-(N : ℤ)) N,
          ∑ i : Fin 2, ppCut c N F z i * (Ψ (z.1 - (j : ℝ) * c, z.2) i : ℂ) := by
        congr 1
        funext z
        exact K3 z
    _ = (N : ℂ)⁻¹ * ∫ z, ∑ j ∈ Finset.Icc (-(N : ℤ)) N,
          ∑ i : Fin 2, ppCut c N F z i * (Ψ (z.1 - (j : ℝ) * c, z.2) i : ℂ) :=
        integral_const_mul _ _
    _ = (N : ℂ)⁻¹ * ∑ j ∈ Finset.Icc (-(N : ℤ)) N,
          ∫ z, ∑ i : Fin 2, ppCut c N F z i * (Ψ (z.1 - (j : ℝ) * c, z.2) i : ℂ) := by
        rw [integral_finsetSum (f := fun (j : ℤ) z => ∑ i : Fin 2,
          ppCut c N F z i * (Ψ (z.1 - (j : ℝ) * c, z.2) i : ℂ)) _ (fun j _ => hY j)]
    _ = (N : ℂ)⁻¹ * ∑ j ∈ Finset.Icc (-(N : ℤ)) N, dlT c N F Ψ j := rfl

/-- **Leaf `PartII-b:T12/1/4/1/6`** (SP 1933-1935): the Riemann-sum limit. -/
theorem ppl_dual_limit : UnforcedLeray.Short.IIb.PPLDualLimit := by
  intro c hc F Ψ hF hΨ
  have hFl : ∀ R : ℝ, IntegrableOn F (Metric.closedBall (0 : ℝ × ℝ) R) volume :=
    fun R => avd_integrableOn_ball hc hF 0 R
  have hper : ∀ z : ℝ × ℝ, F (z.1 + c, z.2) = F z := hF.1
  obtain ⟨R, hR⟩ := dl_support Ψ hΨ
  obtain ⟨K, hK⟩ := dl_K c R hc
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ w : ℝ × ℝ, ‖Ψ w‖ ≤ M := by
    obtain ⟨M0, hM0⟩ := (isCompact_closedBall (0 : ℝ × ℝ) R).exists_bound_of_continuousOn
      (continuous_pi fun i => (hΨ.comp i).smooth.continuous).continuousOn
    refine ⟨max M0 0, fun w => ?_⟩
    by_cases hw : w ∈ Metric.closedBall (0 : ℝ × ℝ) R
    · exact (hM0 w hw).trans (le_max_left _ _)
    · rw [hR w hw, norm_zero]
      exact le_max_right _ _
  obtain ⟨C0, hC0⟩ : ∃ C0 : ℝ, ∀ (N : ℕ) (j : ℤ), ‖dlT c N F Ψ j‖ ≤ C0 :=
    ⟨_, fun N j => dl_bound c hc N F hper hFl Ψ R hR M hM j⟩
  have hC0nn : 0 ≤ C0 := (norm_nonneg _).trans (hC0 0 0)
  set A : ℂ := ∫ z, ∑ i : Fin 2, F z i * (Ψ z i : ℂ) with hA
  have hcard : ∀ N : ℕ, 2 * K ≤ N →
      ((Finset.Icc (K : ℤ) ((N : ℤ) - K - 1)).card : ℂ) = (N : ℂ) - 2 * K := by
    intro N hN
    rw [Int.card_Icc]
    have h1 : ((((N : ℤ) - K - 1 + 1 - K).toNat : ℕ) : ℤ) = (N : ℤ) - 2 * K := by
      rw [Int.toNat_of_nonneg (by omega)]
      ring
    have h2 : ((((N : ℤ) - K - 1 + 1 - K).toNat : ℕ) : ℂ) = (N : ℂ) - 2 * K := by
      exact_mod_cast h1
    exact h2
  have hsplit : ∀ N : ℕ, 2 * K ≤ N → ∃ E : ℂ,
      ∑ j ∈ Finset.Icc (-(N : ℤ)) N, dlT c N F Ψ j =
        ((Finset.Icc (K : ℤ) ((N : ℤ) - K - 1)).card : ℂ) * A + E ∧
      ‖E‖ ≤ (3 * K + 1) * C0 := by
    intro N hN
    have hsub1 : Finset.Icc (-(K : ℤ)) N ⊆ Finset.Icc (-(N : ℤ)) N :=
      Finset.Icc_subset_Icc (by omega) le_rfl
    have hz : ∀ x ∈ Finset.Icc (-(N : ℤ)) N, x ∉ Finset.Icc (-(K : ℤ)) N →
        dlT c N F Ψ x = 0 := by
      intro x hx hx'
      rw [Finset.mem_Icc] at hx hx'
      exact dl_zero_low c hc N F Ψ R hR K hK x (by omega)
    have hs : Finset.Icc (-(K : ℤ)) N = (Finset.Icc (-(K : ℤ)) ((K : ℤ) - 1) ∪
        Finset.Icc (K : ℤ) ((N : ℤ) - K - 1)) ∪ Finset.Icc ((N : ℤ) - K) N := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_union]
      omega
    have d1 : Disjoint (Finset.Icc (-(K : ℤ)) ((K : ℤ) - 1))
        (Finset.Icc (K : ℤ) ((N : ℤ) - K - 1)) := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      simp only [Finset.mem_Icc] at h1 h2
      omega
    have d2 : Disjoint (Finset.Icc (-(K : ℤ)) ((K : ℤ) - 1) ∪
        Finset.Icc (K : ℤ) ((N : ℤ) - K - 1)) (Finset.Icc ((N : ℤ) - K) N) := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      simp only [Finset.mem_union, Finset.mem_Icc] at h1 h2
      omega
    have hgood : ∑ j ∈ Finset.Icc (K : ℤ) ((N : ℤ) - K - 1), dlT c N F Ψ j =
        ((Finset.Icc (K : ℤ) ((N : ℤ) - K - 1)).card : ℂ) * A := by
      rw [Finset.sum_congr rfl (fun j hj => dl_good c hc N F hper Ψ R hR K hK j
        (by rw [Finset.mem_Icc] at hj; omega) (by rw [Finset.mem_Icc] at hj; omega))]
      rw [Finset.sum_const, nsmul_eq_mul]
    refine ⟨∑ j ∈ Finset.Icc (-(K : ℤ)) ((K : ℤ) - 1), dlT c N F Ψ j +
      ∑ j ∈ Finset.Icc ((N : ℤ) - K) N, dlT c N F Ψ j, ?_, ?_⟩
    · rw [(Finset.sum_subset hsub1 hz).symm, hs, Finset.sum_union d2, Finset.sum_union d1, hgood]
      ring
    · have hLo : ‖∑ j ∈ Finset.Icc (-(K : ℤ)) ((K : ℤ) - 1), dlT c N F Ψ j‖ ≤ 2 * K * C0 := by
        refine (norm_sum_le _ _).trans ?_
        refine (Finset.sum_le_card_nsmul _ _ C0 (fun j _ => hC0 N j)).trans ?_
        rw [nsmul_eq_mul]
        have hc' : (Finset.Icc (-(K : ℤ)) ((K : ℤ) - 1)).card ≤ 2 * K := by
          rw [Int.card_Icc]
          exact Int.toNat_le.2 (by omega)
        have hc'' : ((Finset.Icc (-(K : ℤ)) ((K : ℤ) - 1)).card : ℝ) ≤ 2 * K := by
          exact_mod_cast hc'
        exact mul_le_mul_of_nonneg_right hc'' hC0nn
      have hHi : ‖∑ j ∈ Finset.Icc ((N : ℤ) - K) N, dlT c N F Ψ j‖ ≤ ((K : ℝ) + 1) * C0 := by
        refine (norm_sum_le _ _).trans ?_
        refine (Finset.sum_le_card_nsmul _ _ C0 (fun j _ => hC0 N j)).trans ?_
        rw [nsmul_eq_mul]
        have hc' : (Finset.Icc ((N : ℤ) - K) N).card ≤ K + 1 := by
          rw [Int.card_Icc]
          exact Int.toNat_le.2 (by omega)
        have hc'' : ((Finset.Icc ((N : ℤ) - K) N).card : ℝ) ≤ (K : ℝ) + 1 := by
          exact_mod_cast hc'
        exact mul_le_mul_of_nonneg_right hc'' hC0nn
      calc ‖∑ j ∈ Finset.Icc (-(K : ℤ)) ((K : ℤ) - 1), dlT c N F Ψ j +
            ∑ j ∈ Finset.Icc ((N : ℤ) - K) N, dlT c N F Ψ j‖
          ≤ ‖∑ j ∈ Finset.Icc (-(K : ℤ)) ((K : ℤ) - 1), dlT c N F Ψ j‖ +
            ‖∑ j ∈ Finset.Icc ((N : ℤ) - K) N, dlT c N F Ψ j‖ := norm_add_le _ _
        _ ≤ 2 * K * C0 + ((K : ℝ) + 1) * C0 := add_le_add hLo hHi
        _ = (3 * K + 1) * C0 := by ring
  have hfinal : ∀ᶠ N : ℕ in atTop,
      ‖(∫ z, ∑ i : Fin 2, ppCut c N F z i * (ppDual c N Ψ z i : ℂ)) - A‖ ≤
        (2 * K * ‖A‖ + (3 * K + 1) * C0) / (N : ℝ) := by
    filter_upwards [eventually_ge_atTop (2 * K + 1)] with N hN
    obtain ⟨E, hE, hEb⟩ := hsplit N (by omega)
    rw [dl_sum_eq c hc N F Ψ hF hΨ, hE, hcard N (by omega)]
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have halg : (N : ℂ)⁻¹ * (((N : ℂ) - 2 * K) * A + E) - A =
        (N : ℂ)⁻¹ * E - (2 * K : ℂ) * (N : ℂ)⁻¹ * A := by
      field_simp
      ring
    rw [halg]
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    calc ‖(N : ℂ)⁻¹ * E - (2 * K : ℂ) * (N : ℂ)⁻¹ * A‖
        ≤ ‖(N : ℂ)⁻¹ * E‖ + ‖(2 * K : ℂ) * (N : ℂ)⁻¹ * A‖ := norm_sub_le _ _
      _ = (N : ℝ)⁻¹ * ‖E‖ + 2 * K * (N : ℝ)⁻¹ * ‖A‖ := by
          simp [norm_mul, norm_inv, Complex.norm_natCast]
      _ ≤ (N : ℝ)⁻¹ * ((3 * K + 1) * C0) + 2 * K * (N : ℝ)⁻¹ * ‖A‖ := by
          gcongr
      _ = (2 * K * ‖A‖ + (3 * K + 1) * C0) / (N : ℝ) := by ring
  have hlim := tendsto_const_div_atTop_nhds_zero_nat (2 * K * ‖A‖ + (3 * K + 1) * C0)
  exact tendsto_sub_nhds_zero_iff.1 (squeeze_zero_norm' hfinal hlim)

end UnforcedLeray.Short.IIb
