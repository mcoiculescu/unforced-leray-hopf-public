import UnforcedLeray.Short.PartIIb.Sub.G4_2_3_4

/-!
# Part II-b, item `PartII-b:G4/2/3/4/2/3/4`: `PerSmoothSum`

Source of record: `the November 2 reference manuscript`, lines 2349-2358.

Termwise differentiation of the periodization `perC c G`. Localization is done with a
translated bump `ψ = pSBump (· - x₀)` (support in `closedBall x₀ 2`, equal to `1` on
`closedBall x₀ 1`). The product `ψ • G(· + kc, ·)` has a uniform-in-`x` summable majorant,
so `contDiff_tsum` applies. The derivative bound uses the `1`-separation of the nodes
`x₁ + kc` (`uniform_sum`), giving a constant independent of `c ≥ 1` and `x`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Finset
open scoped ContDiff

namespace UnforcedLeray.Short.IIb.PerSmoothSumAux

/-- The plane. -/
abbrev E2 := ℝ × ℝ

lemma natCast_le_top (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by
  exact_mod_cast le_top

/-- Summable majorant over `ℤ`. -/
lemma summable_inv_sq_int : Summable (fun m : ℤ => 1 / (1 + |(m : ℝ)|) ^ 2) := by
  rw [summable_int_iff_summable_nat_and_neg]
  have h0 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.2 (by norm_num)
  have h : Summable (fun n : ℕ => 1 / (1 + |((n : ℤ) : ℝ)|) ^ 2) := by
    refine ((summable_nat_add_iff 1).2 h0).congr (fun n => ?_)
    push_cast
    rw [abs_of_nonneg (Nat.cast_nonneg n)]
    ring_nf
  exact ⟨h, h.congr (fun n => by simp)⟩

/-- Local majorant: for `|t| ≤ R`, the node `t + k c` is far from the origin in proportion
to `|k|`, uniformly in `c ≥ 1`. -/
lemma local_bound (c R t : ℝ) (hc : 1 ≤ c) (hR : 0 ≤ R) (ht : |t| ≤ R) (k : ℤ) :
    1 / (1 + |t + (k : ℝ) * c|) ^ 2 ≤ (1 + R) ^ 2 * (1 / (1 + |(k : ℝ)|) ^ 2) := by
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have h1 : |(k : ℝ)| ≤ |(k : ℝ) * c| := by
    rw [abs_mul, abs_of_nonneg hc0]
    nlinarith [abs_nonneg (k : ℝ)]
  have h2 : |(k : ℝ) * c| ≤ |t + (k : ℝ) * c| + |t| := by
    have h := abs_sub (t + (k : ℝ) * c) t
    rwa [show t + (k : ℝ) * c - t = (k : ℝ) * c by ring] at h
  have hA : 0 ≤ |t + (k : ℝ) * c| := abs_nonneg _
  have hk1 : 1 + |(k : ℝ)| ≤ (1 + R) * (1 + |t + (k : ℝ) * c|) := by
    nlinarith [mul_nonneg hR hA]
  have hpos : 0 < 1 + |(k : ℝ)| := by positivity
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  calc (1 + |(k : ℝ)|) ^ 2 ≤ ((1 + R) * (1 + |t + (k : ℝ) * c|)) ^ 2 := by gcongr
    _ = (1 + R) ^ 2 * (1 + |t + (k : ℝ) * c|) ^ 2 := by ring

/-- Uniform lattice sum: for `c ≥ 1` and every `t`, the series `Σ_k 1/(1+|t+kc|)²` is
summable and bounded by a constant independent of `t` and `c`. -/
lemma uniform_sum (c : ℝ) (hc : 1 ≤ c) (t : ℝ) :
    Summable (fun k : ℤ => 1 / (1 + |t + (k : ℝ) * c|) ^ 2) ∧
      ∑' k : ℤ, 1 / (1 + |t + (k : ℝ) * c|) ^ 2 ≤ 4 * ∑' m : ℤ, 1 / (1 + |(m : ℝ)|) ^ 2 := by
  have hc0 : (0 : ℝ) < c := by linarith
  obtain ⟨k0, hr0, hr1⟩ : ∃ k0 : ℤ, 0 ≤ t + (k0 : ℝ) * c ∧ t + (k0 : ℝ) * c < c := by
    refine ⟨⌈-t / c⌉, ?_, ?_⟩
    · have h1 : -t / c ≤ ((⌈-t / c⌉ : ℤ) : ℝ) := Int.le_ceil _
      have h2 : -t ≤ ((⌈-t / c⌉ : ℤ) : ℝ) * c := by
        have h3 := mul_le_mul_of_nonneg_right h1 hc0.le
        rwa [div_mul_cancel₀ _ hc0.ne'] at h3
      linarith
    · have h1 : ((⌈-t / c⌉ : ℤ) : ℝ) < -t / c + 1 := Int.ceil_lt_add_one _
      have h2 := mul_lt_mul_of_pos_right h1 hc0
      have h3 : (-t / c + 1) * c = -t + c := by
        rw [add_mul, div_mul_cancel₀ _ hc0.ne', one_mul]
      linarith
  have key : ∀ m : ℤ, (1 + |(m : ℝ)|) / 2 ≤ 1 + |(t + (k0 : ℝ) * c) + (m : ℝ) * c| := by
    intro m
    rcases le_or_gt 0 m with hm | hm
    · have hm' : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hr : 0 ≤ (t + (k0 : ℝ) * c) + (m : ℝ) * c := by
        nlinarith [mul_le_mul_of_nonneg_left hc hm']
      rw [abs_of_nonneg hm', abs_of_nonneg hr]
      nlinarith [mul_le_mul_of_nonneg_left hc hm']
    · have hm' : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
      have hmc : (m : ℝ) * c ≤ -1 * c := mul_le_mul_of_nonneg_right hm' hc0.le
      have hr : (t + (k0 : ℝ) * c) + (m : ℝ) * c < 0 := by linarith
      rw [abs_of_neg (by linarith : (m : ℝ) < 0), abs_of_neg hr]
      nlinarith [mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ -(m : ℝ) - 1 by linarith)]
  have hsum4 : Summable (fun m : ℤ => 4 * (1 / (1 + |(m : ℝ)|) ^ 2)) :=
    summable_inv_sq_int.mul_left 4
  have hbound : ∀ m : ℤ, 1 / (1 + |t + ((m + k0 : ℤ) : ℝ) * c|) ^ 2
      ≤ 4 * (1 / (1 + |(m : ℝ)|) ^ 2) := by
    intro m
    have e : t + ((m + k0 : ℤ) : ℝ) * c = (t + (k0 : ℝ) * c) + (m : ℝ) * c := by
      push_cast; ring
    rw [e]
    have hp : (0 : ℝ) < (1 + |(m : ℝ)|) / 2 := by positivity
    have h1 := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < ((1 + |(m : ℝ)|) / 2) ^ 2)
      (pow_le_pow_left₀ hp.le (key m) 2)
    calc 1 / (1 + |(t + (k0 : ℝ) * c) + (m : ℝ) * c|) ^ 2
        ≤ 1 / (((1 + |(m : ℝ)|) / 2) ^ 2) := h1
      _ = 4 * (1 / (1 + |(m : ℝ)|) ^ 2) := by
        field_simp
        ring
  have hsk : Summable (fun m : ℤ => 1 / (1 + |t + ((m + k0 : ℤ) : ℝ) * c|) ^ 2) :=
    Summable.of_nonneg_of_le (fun m => by positivity) hbound hsum4
  have hsf : Summable (fun k : ℤ => 1 / (1 + |t + (k : ℝ) * c|) ^ 2) := by
    have e := (Equiv.addRight k0).summable_iff
      (f := fun k : ℤ => 1 / (1 + |t + (k : ℝ) * c|) ^ 2)
    exact e.mp hsk
  refine ⟨hsf, ?_⟩
  calc ∑' k : ℤ, 1 / (1 + |t + (k : ℝ) * c|) ^ 2
      = ∑' m : ℤ, 1 / (1 + |t + ((m + k0 : ℤ) : ℝ) * c|) ^ 2 :=
        ((Equiv.addRight k0).tsum_eq (fun k : ℤ => 1 / (1 + |t + (k : ℝ) * c|) ^ 2)).symm
    _ ≤ ∑' m : ℤ, 4 * (1 / (1 + |(m : ℝ)|) ^ 2) := hsk.tsum_le_tsum hbound hsum4
    _ = 4 * ∑' m : ℤ, 1 / (1 + |(m : ℝ)|) ^ 2 := tsum_mul_left

/-- The fixed bump: `1` on the unit ball, supported in the ball of radius `2`. -/
def pSBump : ContDiffBump (0 : E2) where
  rIn := 1
  rOut := 2
  rIn_pos := one_pos
  rIn_lt_rOut := one_lt_two

lemma pSBump_contDiff : ContDiff ℝ ∞ pSBump := pSBump.contDiff

lemma pSBump_deriv_bound (i : ℕ) : ∃ M : ℝ, ∀ y : E2, ‖iteratedFDeriv ℝ i pSBump y‖ ≤ M := by
  have hc : Continuous (fun y => iteratedFDeriv ℝ i pSBump y) :=
    ContDiff.continuous_iteratedFDeriv (natCast_le_top i) pSBump_contDiff
  exact hc.bounded_above_of_compact_support (pSBump.hasCompactSupport.iteratedFDeriv i)

lemma pSBump_one {w : E2} (hw : ‖w‖ ≤ 1) : pSBump w = 1 := by
  apply pSBump.one_of_mem_closedBall
  rw [mem_closedBall_zero_iff]
  exact hw

lemma pSBump_zero {w : E2} (hw : 2 ≤ ‖w‖) : pSBump w = 0 := by
  apply pSBump.zero_of_le_dist
  rw [dist_zero_right]
  exact hw

/-- Coefficient of the Leibniz bound. -/
def pSK (M B : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * M i * B (n - i)

lemma pSK_nonneg (M B : ℕ → ℝ) (hM : ∀ i, 0 ≤ M i) (hB : ∀ j, 0 ≤ B j) (n : ℕ) :
    0 ≤ pSK M B n :=
  Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hM i)) (hB _)

lemma prod_bound (c M B q na nb : ℝ) (hc : 0 ≤ c) (hna : 0 ≤ na) (hnaM : na ≤ M)
    (hnb : 0 ≤ nb) (hnbB : nb ≤ B * q) :
    c * na * nb ≤ c * (M * (B * q)) := by
  have h : na * nb ≤ M * (B * q) := mul_le_mul hnaM hnbB hnb (hna.trans hnaM)
  calc c * na * nb = c * (na * nb) := by ring
    _ ≤ c * (M * (B * q)) := mul_le_mul_of_nonneg_left h hc

/-- Leibniz bound for a product `ψ • F`, at a fixed point. -/
lemma term_leibniz {ψ : E2 → ℝ} {F : E2 → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hF : ContDiff ℝ ∞ F)
    (n : ℕ) (y : E2) (M B : ℕ → ℝ) (q : ℝ)
    (hM : ∀ i, ‖iteratedFDeriv ℝ i ψ y‖ ≤ M i)
    (hq : ∀ m, ‖iteratedFDeriv ℝ m F y‖ ≤ B m * q)
    (hM0 : ∀ i, 0 ≤ M i) (hB0 : ∀ m, 0 ≤ B m) :
    ‖iteratedFDeriv ℝ n (fun z => ψ z • F z) y‖ ≤ pSK M B n * q := by
  refine (norm_iteratedFDeriv_smul_le hψ hF y (natCast_le_top n)).trans ?_
  calc _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (M i * (B (n - i) * q)) :=
        Finset.sum_le_sum fun i _ => by
          have := prod_bound (n.choose i : ℝ) (M i) (B (n - i)) q _ _ (Nat.cast_nonneg _)
            (norm_nonneg _) (hM i) (norm_nonneg _) (hq (n - i))
          linarith [this]
    _ = pSK M B n * q := by
        unfold pSK
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- Translate bound for the `k`-th term. -/
lemma translate_bound (G : E2 → ℂ) (B : ℕ → ℝ)
    (hB : ∀ j (y : E2), ‖iteratedFDeriv ℝ j G y‖ ≤ B j / (1 + |y.1|) ^ 2)
    (c : ℝ) (k : ℤ) (j : ℕ) (x : E2) :
    ‖iteratedFDeriv ℝ j (fun y : E2 => G (y.1 + (k : ℝ) * c, y.2)) x‖
      ≤ B j * (1 / (1 + |x.1 + (k : ℝ) * c|) ^ 2) := by
  have e : (fun y : E2 => G (y.1 + (k : ℝ) * c, y.2)) = fun z => G (z + ((k : ℝ) * c, 0)) := by
    funext y
    show G (y.1 + (k : ℝ) * c, y.2) = G (y + ((k : ℝ) * c, 0))
    congr 1
    exact Prod.ext rfl (by simp)
  rw [e, iteratedFDeriv_comp_add_right, ← div_eq_mul_one_div]
  have h := hB j (x + ((k : ℝ) * c, 0))
  simpa using h

lemma term_hF (G : E2 → ℂ) (hG : ContDiff ℝ ∞ G) (c : ℝ) (k : ℤ) :
    ContDiff ℝ ∞ (fun y : E2 => G (y.1 + (k : ℝ) * c, y.2)) :=
  hG.comp (ContDiff.prodMk ((contDiff_fst).add contDiff_const) contDiff_snd)

lemma term_hψ (x0 : E2) : ContDiff ℝ ∞ (fun z : E2 => pSBump (z - x0)) :=
  pSBump_contDiff.comp (contDiff_id.sub contDiff_const)

/-- Summable periodization at each point (part one of the statement). -/
lemma summable_terms (G : E2 → ℂ)
    (B : ℕ → ℝ) (hB : ∀ j (y : E2), ‖iteratedFDeriv ℝ j G y‖ ≤ B j / (1 + |y.1|) ^ 2)
    (c : ℝ) (hc : 1 ≤ c) (x : E2) :
    Summable (fun k : ℤ => G (x.1 + (k : ℝ) * c, x.2)) := by
  refine Summable.of_norm_bounded ((uniform_sum c hc x.1).1.mul_left (B 0)) (fun k => ?_)
  have h := translate_bound G B hB c k 0 x
  rw [norm_iteratedFDeriv_zero] at h
  exact h

lemma hB_nonneg (G : E2 → ℂ) (B : ℕ → ℝ)
    (hB : ∀ j (y : E2), ‖iteratedFDeriv ℝ j G y‖ ≤ B j / (1 + |y.1|) ^ 2) (j : ℕ) :
    0 ≤ B j := by
  have h := hB j 0
  have hn := norm_nonneg (iteratedFDeriv ℝ j G 0)
  simp only [Prod.fst_zero, abs_zero, add_zero, one_pow, div_one] at h
  linarith

/-- Local data: the localized term `ψ • G(·+kc)` with `ψ` centered at `x₀`. -/
lemma term_bound_local (G : E2 → ℂ) (hG : ContDiff ℝ ∞ G)
    (B : ℕ → ℝ) (hB : ∀ j (y : E2), ‖iteratedFDeriv ℝ j G y‖ ≤ B j / (1 + |y.1|) ^ 2)
    (M : ℕ → ℝ) (hM : ∀ i (y : E2), ‖iteratedFDeriv ℝ i pSBump y‖ ≤ M i)
    (hM0 : ∀ i, 0 ≤ M i) (hB0 : ∀ j, 0 ≤ B j)
    (c : ℝ) (hc : 1 ≤ c) (x0 : E2) (n : ℕ) (k : ℤ) (y : E2) :
    ‖iteratedFDeriv ℝ n (fun z => pSBump (z - x0) • G (z.1 + (k : ℝ) * c, z.2)) y‖
      ≤ pSK M B n * ((1 + (|x0.1| + 2)) ^ 2 * (1 / (1 + |(k : ℝ)|) ^ 2)) := by
  by_cases hy : dist y x0 ≤ 2
  · apply term_leibniz (term_hψ x0) (term_hF G hG c k) n y M B _
    · intro i
      rw [iteratedFDeriv_comp_sub]
      exact hM i _
    · intro m
      have hy1 : |y.1| ≤ |x0.1| + 2 := by
        have h1 : |y.1 - x0.1| ≤ 2 := by
          have h2 : dist y.1 x0.1 ≤ dist y x0 := by
            rw [Prod.dist_eq]; exact le_max_left _ _
          rw [Real.dist_eq] at h2
          linarith
        have := abs_le.mp h1
        rw [abs_le]
        constructor <;> linarith [neg_abs_le x0.1, le_abs_self x0.1]
      have hq := local_bound c (|x0.1| + 2) y.1 hc (by positivity) hy1 k
      have ht := translate_bound G B hB c k m y
      calc _ ≤ B m * (1 / (1 + |y.1 + (k : ℝ) * c|) ^ 2) := ht
        _ ≤ B m * ((1 + (|x0.1| + 2)) ^ 2 * (1 / (1 + |(k : ℝ)|) ^ 2)) :=
          mul_le_mul_of_nonneg_left hq (hB0 m)
    · exact hM0
    · exact hB0
  · push_neg at hy
    have hev : (fun z : E2 => pSBump (z - x0) • G (z.1 + (k : ℝ) * c, z.2))
        =ᶠ[𝓝 y] (fun _ : E2 => (0 : ℂ)) := by
      have hopen : ∀ᶠ z in 𝓝 y, 2 < dist z x0 :=
        (isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds hy
      filter_upwards [hopen] with z hz
      have hz' : 2 ≤ ‖z - x0‖ := by
        rw [← dist_eq_norm]
        exact hz.le
      simp [pSBump_zero hz']
    rw [(hev.iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_fun_zero]
    simp only [Pi.zero_apply, norm_zero]
    apply mul_nonneg (pSK_nonneg M B hM0 hB0 n)
    positivity

/-- Smoothness data for the localized series (for `contDiff_tsum`). -/
lemma term_hyps (G : E2 → ℂ) (hG : ContDiff ℝ ∞ G)
    (B : ℕ → ℝ) (hB : ∀ j (y : E2), ‖iteratedFDeriv ℝ j G y‖ ≤ B j / (1 + |y.1|) ^ 2)
    (M : ℕ → ℝ) (hM : ∀ i (y : E2), ‖iteratedFDeriv ℝ i pSBump y‖ ≤ M i)
    (hM0 : ∀ i, 0 ≤ M i) (hB0 : ∀ j, 0 ≤ B j)
    (c : ℝ) (hc : 1 ≤ c) (x0 : E2) :
    (∀ k : ℤ, ContDiff ℝ ∞ (fun y : E2 => pSBump (y - x0) • G (y.1 + (k : ℝ) * c, y.2))) ∧
    (∀ n : ℕ, Summable (fun k : ℤ =>
      pSK M B n * ((1 + (|x0.1| + 2)) ^ 2 * (1 / (1 + |(k : ℝ)|) ^ 2)))) := by
  refine ⟨fun k => (term_hψ x0).smul (term_hF G hG c k), fun n => ?_⟩
  exact (summable_inv_sq_int.mul_left _).mul_left _

lemma local_repr (G : E2 → ℂ) (hG : ContDiff ℝ ∞ G)
    (B : ℕ → ℝ) (hB : ∀ j (y : E2), ‖iteratedFDeriv ℝ j G y‖ ≤ B j / (1 + |y.1|) ^ 2)
    (M : ℕ → ℝ) (hM : ∀ i (y : E2), ‖iteratedFDeriv ℝ i pSBump y‖ ≤ M i)
    (hM0 : ∀ i, 0 ≤ M i) (hB0 : ∀ j, 0 ≤ B j)
    (c : ℝ) (hc : 1 ≤ c) (x0 : E2) :
    perC c G =ᶠ[𝓝 x0] (fun y => ∑' k : ℤ, pSBump (y - x0) • G (y.1 + (k : ℝ) * c, y.2)) ∧
    ContDiff ℝ ∞ (fun y => ∑' k : ℤ, pSBump (y - x0) • G (y.1 + (k : ℝ) * c, y.2)) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [Metric.ball_mem_nhds x0 one_pos] with y hy
    have hw : ‖y - x0‖ ≤ 1 := by
      rw [← dist_eq_norm]
      exact (Metric.mem_ball.mp hy).le
    show ∑' k : ℤ, G (y.1 + (k : ℝ) * c, y.2) = _
    simp only [pSBump_one hw, one_smul]
  · obtain ⟨hf, hv⟩ := term_hyps G hG B hB M hM hM0 hB0 c hc x0
    exact contDiff_tsum (f := fun (k : ℤ) (y : E2) => pSBump (y - x0) • G (y.1 + (k : ℝ) * c, y.2))
      (v := fun n k => pSK M B n * ((1 + (|x0.1| + 2)) ^ 2 * (1 / (1 + |(k : ℝ)|) ^ 2)))
      hf (fun n _ => hv n)
      (fun n k y _ => term_bound_local G hG B hB M hM hM0 hB0 c hc x0 n k y)

lemma perC_contDiffAt (G : E2 → ℂ) (hG : ContDiff ℝ ∞ G)
    (B : ℕ → ℝ) (hB : ∀ j (y : E2), ‖iteratedFDeriv ℝ j G y‖ ≤ B j / (1 + |y.1|) ^ 2)
    (M : ℕ → ℝ) (hM : ∀ i (y : E2), ‖iteratedFDeriv ℝ i pSBump y‖ ≤ M i)
    (hM0 : ∀ i, 0 ≤ M i) (hB0 : ∀ j, 0 ≤ B j)
    (c : ℝ) (hc : 1 ≤ c) (x0 : E2) : ContDiffAt ℝ ∞ (perC c G) x0 := by
  obtain ⟨hev, hsm⟩ := local_repr G hG B hB M hM hM0 hB0 c hc x0
  exact hsm.contDiffAt.congr_of_eventuallyEq hev

/-- Pointwise derivative bound, uniform in `x` and `c ≥ 1`. -/
lemma deriv_bound (G : E2 → ℂ) (hG : ContDiff ℝ ∞ G)
    (B : ℕ → ℝ) (hB : ∀ j (y : E2), ‖iteratedFDeriv ℝ j G y‖ ≤ B j / (1 + |y.1|) ^ 2)
    (M : ℕ → ℝ) (hM : ∀ i (y : E2), ‖iteratedFDeriv ℝ i pSBump y‖ ≤ M i)
    (hM0 : ∀ i, 0 ≤ M i) (hB0 : ∀ j, 0 ≤ B j)
    (c : ℝ) (hc : 1 ≤ c) (j : ℕ) (x : E2) :
    ‖iteratedFDeriv ℝ j (perC c G) x‖ ≤ pSK M B j * (4 * ∑' m : ℤ, 1 / (1 + |(m : ℝ)|) ^ 2) := by
  obtain ⟨hev, _⟩ := local_repr G hG B hB M hM hM0 hB0 c hc x
  obtain ⟨hf, hv⟩ := term_hyps G hG B hB M hM hM0 hB0 c hc x
  have hkN : (j : ℕ∞) ≤ ⊤ := le_top
  have e : iteratedFDeriv ℝ j (perC c G) x
      = iteratedFDeriv ℝ j (fun y => ∑' k : ℤ, pSBump (y - x) • G (y.1 + (k : ℝ) * c, y.2)) x :=
    (hev.iteratedFDeriv ℝ j).eq_of_nhds
  rw [e, iteratedFDeriv_tsum_apply (f := fun (k : ℤ) (y : E2) => pSBump (y - x) • G (y.1 + (k : ℝ) * c, y.2))
    (v := fun n k => pSK M B n * ((1 + (|x.1| + 2)) ^ 2 * (1 / (1 + |(k : ℝ)|) ^ 2)))
    hf (fun n _ => hv n)
    (fun n k y _ => term_bound_local G hG B hB M hM hM0 hB0 c hc x n k y) hkN x]
  set u : ℤ → ℝ := fun k => pSK M B j * (1 / (1 + |x.1 + (k : ℝ) * c|) ^ 2) with hu
  have hle : ∀ k : ℤ, ‖iteratedFDeriv ℝ j
      (fun y : E2 => pSBump (y - x) • G (y.1 + (k : ℝ) * c, y.2)) x‖ ≤ u k := by
    intro k
    refine term_leibniz (term_hψ x) (term_hF G hG c k) j x M B _ ?_ ?_ hM0 hB0
    · intro i
      rw [iteratedFDeriv_comp_sub]
      exact hM i _
    · intro m
      exact translate_bound G B hB c k m x
  have hsu : Summable u := (uniform_sum c hc x.1).1.mul_left _
  have hsumn : Summable (fun k : ℤ => ‖iteratedFDeriv ℝ j
      (fun y : E2 => pSBump (y - x) • G (y.1 + (k : ℝ) * c, y.2)) x‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hle hsu
  calc _ ≤ ∑' k : ℤ, ‖iteratedFDeriv ℝ j (fun y : E2 => pSBump (y - x) • G (y.1 + (k : ℝ) * c, y.2)) x‖ :=
        norm_tsum_le_tsum_norm hsumn
    _ ≤ ∑' k : ℤ, u k := hsumn.tsum_le_tsum hle hsu
    _ = pSK M B j * ∑' k : ℤ, 1 / (1 + |x.1 + (k : ℝ) * c|) ^ 2 := by
        rw [hu]
        exact tsum_mul_left
    _ ≤ pSK M B j * (4 * ∑' m : ℤ, 1 / (1 + |(m : ℝ)|) ^ 2) :=
        mul_le_mul_of_nonneg_left (uniform_sum c hc x.1).2 (pSK_nonneg M B hM0 hB0 j)

end UnforcedLeray.Short.IIb.PerSmoothSumAux

open UnforcedLeray.Short.IIb.PerSmoothSumAux in
theorem perSmoothSum : UnforcedLeray.Short.IIb.PerSmoothSum := by
  unfold UnforcedLeray.Short.IIb.PerSmoothSum
  intro G hG hbd
  choose B hB using hbd
  have hB0 : ∀ j, 0 ≤ B j := hB_nonneg G B hB
  choose M hM using pSBump_deriv_bound
  have hM0 : ∀ i, 0 ≤ M i := fun i => (norm_nonneg _).trans (hM i 0)
  refine ⟨fun c hc => ⟨fun x => summable_terms G B hB c hc x,
    contDiff_iff_contDiffAt.2 fun x0 => perC_contDiffAt G hG B hB M hM hM0 hB0 c hc x0⟩,
    fun j => ⟨pSK M B j * (4 * ∑' m : ℤ, 1 / (1 + |(m : ℝ)|) ^ 2),
      fun c hc x => deriv_bound G hG B hB M hM hM0 hB0 c hc j x⟩⟩
