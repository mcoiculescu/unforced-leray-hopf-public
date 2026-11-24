import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_1_2_1

/-!


Source: `the November 2 reference manuscript`, lines 2074-2105.
Pure one-variable calculus: `pou k = σ_k - σ_{k+1}` with `σ_k(r) = smoothTransition((r - a_k)/h + 1/2)`
for `0 < k < K`, `σ_0 = 1`, `σ_k = 0` for `k ≥ K`. The sum telescopes; nonnegativity comes from the
monotonicity of `smoothTransition`; the derivative sum is bounded because at each `r` at most one
`σ_k'` is nonzero (the intervals `(a_k - h/2, a_k + h/2)` are disjoint).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace TdSums

/-! ## The smooth transition -/

theorem pouT_st_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Real.smoothTransition :=
  Real.smoothTransition.contDiff

theorem pouT_st_deriv_continuous : Continuous (deriv Real.smoothTransition) :=
  pouT_st_contDiff.continuous_deriv (by simp)

theorem pouT_st_deriv_of_lt {y : ℝ} (hy : y < 0) : deriv Real.smoothTransition y = 0 := by
  have hev : Real.smoothTransition =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
    filter_upwards [Iio_mem_nhds hy] with z hz
    have hz' : z < 0 := hz
    exact Real.smoothTransition.zero_of_nonpos hz'.le
  rw [hev.deriv_eq, deriv_const]

theorem pouT_st_deriv_of_gt {y : ℝ} (hy : 1 < y) : deriv Real.smoothTransition y = 0 := by
  have hev : Real.smoothTransition =ᶠ[𝓝 y] (fun _ => (1 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hy] with z hz
    have hz' : 1 < z := hz
    exact Real.smoothTransition.one_of_one_le (by linarith)
  rw [hev.deriv_eq, deriv_const]

theorem pouT_st_deriv_zero_of_le {y : ℝ} (hy : y ≤ 0) : deriv Real.smoothTransition y = 0 := by
  have hsub : Iio (0 : ℝ) ⊆ {z : ℝ | deriv Real.smoothTransition z = 0} :=
    fun z hz => pouT_st_deriv_of_lt hz
  have hcl : closure (Iio (0 : ℝ)) ⊆ {z : ℝ | deriv Real.smoothTransition z = 0} :=
    closure_minimal hsub (isClosed_eq pouT_st_deriv_continuous continuous_const)
  rw [closure_Iio' ⟨-1, show (-1 : ℝ) < 0 by norm_num⟩] at hcl
  exact hcl hy

theorem pouT_st_deriv_zero_of_ge {y : ℝ} (hy : 1 ≤ y) : deriv Real.smoothTransition y = 0 := by
  have hsub : Ioi (1 : ℝ) ⊆ {z : ℝ | deriv Real.smoothTransition z = 0} :=
    fun z hz => pouT_st_deriv_of_gt hz
  have hcl : closure (Ioi (1 : ℝ)) ⊆ {z : ℝ | deriv Real.smoothTransition z = 0} :=
    closure_minimal hsub (isClosed_eq pouT_st_deriv_continuous continuous_const)
  rw [closure_Ioi' ⟨2, show (1 : ℝ) < 2 by norm_num⟩] at hcl
  exact hcl hy

theorem pouT_st_deriv_bdd : ∃ D₀ : ℝ, 0 ≤ D₀ ∧ ∀ y : ℝ, |deriv Real.smoothTransition y| ≤ D₀ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    pouT_st_deriv_continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  by_cases hy : y ∈ Icc (0 : ℝ) 1
  · rw [← Real.norm_eq_abs]
    exact le_trans (hC y hy) (le_max_left _ _)
  · rw [Set.mem_Icc, not_and_or, not_le, not_le] at hy
    rcases hy with h | h
    · rw [pouT_st_deriv_of_lt h]; simp
    · rw [pouT_st_deriv_of_gt h]; simp

/-! ## Grid and steps -/

theorem pouT_gridH_pos {t₀ t₁ : ℝ} {K : ℕ} (ht : t₀ < t₁) (hK : 0 < K) :
    0 < gridH t₀ t₁ K := by
  unfold gridH
  apply div_pos (by linarith)
  exact_mod_cast hK

theorem pouT_gridPt_succ (t₀ t₁ : ℝ) (K k : ℕ) :
    gridPt t₀ t₁ K (k + 1) = gridPt t₀ t₁ K k + gridH t₀ t₁ K := by
  unfold gridPt
  push_cast
  ring

theorem pouT_gridPt_zero (t₀ t₁ : ℝ) (K : ℕ) : gridPt t₀ t₁ K 0 = t₀ := by
  simp [gridPt]

theorem pouT_gridPt_K (t₀ t₁ : ℝ) {K : ℕ} (hK : 0 < K) : gridPt t₀ t₁ K K = t₁ := by
  have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  unfold gridPt gridH
  field_simp
  ring

theorem pouT_step_zero (t₀ t₁ : ℝ) (K : ℕ) (r : ℝ) : pouStep t₀ t₁ K 0 r = 1 := by
  simp [pouStep]

theorem pouT_step_of_ge {t₀ t₁ : ℝ} {K k : ℕ} (hk0 : k ≠ 0) (hK : K ≤ k) (r : ℝ) :
    pouStep t₀ t₁ K k r = 0 := by
  simp [pouStep, hk0, hK]

theorem pouT_step_mid {t₀ t₁ : ℝ} {K k : ℕ} (hk0 : k ≠ 0) (hK : k < K) (r : ℝ) :
    pouStep t₀ t₁ K k r =
      Real.smoothTransition ((r - gridPt t₀ t₁ K k) / gridH t₀ t₁ K + 1 / 2) := by
  have hK' : ¬ K ≤ k := not_le.mpr hK
  simp [pouStep, hk0, hK']

theorem pouT_step_bounds (t₀ t₁ : ℝ) (K k : ℕ) (r : ℝ) :
    0 ≤ pouStep t₀ t₁ K k r ∧ pouStep t₀ t₁ K k r ≤ 1 := by
  by_cases hk0 : k = 0
  · subst hk0
    rw [pouT_step_zero]
    norm_num
  by_cases hK : K ≤ k
  · rw [pouT_step_of_ge hk0 hK]
    norm_num
  rw [pouT_step_mid hk0 (not_le.mp hK)]
  exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The steps are nonincreasing in the index. -/
theorem pouT_step_succ_le {t₀ t₁ : ℝ} {K : ℕ} (ht : t₀ < t₁) (k : ℕ) (r : ℝ) :
    pouStep t₀ t₁ K (k + 1) r ≤ pouStep t₀ t₁ K k r := by
  by_cases hk0 : k = 0
  · subst hk0
    rw [pouT_step_zero]
    exact (pouT_step_bounds t₀ t₁ K 1 r).2
  by_cases hK : K ≤ k + 1
  · rw [pouT_step_of_ge (Nat.succ_ne_zero k) hK]
    exact (pouT_step_bounds t₀ t₁ K k r).1
  have hK1 : k + 1 < K := not_le.mp hK
  have hKk : k < K := by omega
  have hKpos : 0 < K := by omega
  have hpos : 0 < gridH t₀ t₁ K := pouT_gridH_pos ht hKpos
  rw [pouT_step_mid (Nat.succ_ne_zero k) hK1, pouT_step_mid hk0 hKk]
  apply Real.smoothTransition.monotone
  rw [pouT_gridPt_succ]
  have e : (r - (gridPt t₀ t₁ K k + gridH t₀ t₁ K)) / gridH t₀ t₁ K =
      (r - gridPt t₀ t₁ K k) / gridH t₀ t₁ K - 1 := by
    rw [show r - (gridPt t₀ t₁ K k + gridH t₀ t₁ K) =
        (r - gridPt t₀ t₁ K k) - gridH t₀ t₁ K by ring, sub_div, div_self hpos.ne']
  linarith

theorem pouT_step_zero_of_le {t₀ t₁ : ℝ} {K : ℕ} (ht : t₀ < t₁) (hK : 0 < K) {k : ℕ}
    (hk0 : k ≠ 0) {r : ℝ} (hr : r ≤ gridPt t₀ t₁ K k - gridH t₀ t₁ K / 2) :
    pouStep t₀ t₁ K k r = 0 := by
  have hpos := pouT_gridH_pos ht hK
  by_cases hKk : K ≤ k
  · exact pouT_step_of_ge hk0 hKk r
  rw [pouT_step_mid hk0 (not_le.mp hKk)]
  apply Real.smoothTransition.zero_of_nonpos
  have h1 : (r - gridPt t₀ t₁ K k) / gridH t₀ t₁ K ≤ -(1 : ℝ) / 2 := by
    rw [div_le_iff₀ hpos]
    linarith
  linarith

theorem pouT_step_one_of_ge {t₀ t₁ : ℝ} {K : ℕ} (ht : t₀ < t₁) (hK : 0 < K) {k : ℕ}
    (hkK : k < K) {r : ℝ} (hr : gridPt t₀ t₁ K k + gridH t₀ t₁ K / 2 ≤ r) :
    pouStep t₀ t₁ K k r = 1 := by
  have hpos := pouT_gridH_pos ht hK
  by_cases hk0 : k = 0
  · subst hk0
    rw [pouT_step_zero]
  rw [pouT_step_mid hk0 hkK]
  apply Real.smoothTransition.one_of_one_le
  have h1 : (1 : ℝ) / 2 ≤ (r - gridPt t₀ t₁ K k) / gridH t₀ t₁ K := by
    rw [le_div_iff₀ hpos]
    linarith
  linarith

/-! ## Partition of unity -/

theorem pouT_step_contDiff (t₀ t₁ : ℝ) (K k : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pouStep t₀ t₁ K k) := by
  by_cases hk0 : k = 0
  · have hf : pouStep t₀ t₁ K k = fun _ => (1 : ℝ) := by
      funext r
      simp [pouStep, hk0]
    rw [hf]
    exact contDiff_const
  by_cases hK : K ≤ k
  · have hf : pouStep t₀ t₁ K k = fun _ => (0 : ℝ) := by
      funext r
      exact pouT_step_of_ge hk0 hK r
    rw [hf]
    exact contDiff_const
  have hf : pouStep t₀ t₁ K k = fun r =>
      Real.smoothTransition ((r - gridPt t₀ t₁ K k) / gridH t₀ t₁ K + 1 / 2) := by
    funext r
    exact pouT_step_mid hk0 (not_le.mp hK) r
  rw [hf]
  exact pouT_st_contDiff.comp
    ((((contDiff_id.sub contDiff_const).div_const (gridH t₀ t₁ K)).add
      (contDiff_const (c := (1 / 2 : ℝ)))))

theorem pou_contDiff_aux (t₀ t₁ : ℝ) (K k : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pou t₀ t₁ K k) :=
  (pouT_step_contDiff t₀ t₁ K k).sub (pouT_step_contDiff t₀ t₁ K (k + 1))

theorem pouT_pou_sum {t₀ t₁ : ℝ} {K : ℕ} (hK : 0 < K) (r : ℝ) :
    ∑ k ∈ Finset.range K, pou t₀ t₁ K k r = 1 := by
  have tele : ∑ k ∈ Finset.range K, (pouStep t₀ t₁ K k r - pouStep t₀ t₁ K (k + 1) r) =
      pouStep t₀ t₁ K 0 r - pouStep t₀ t₁ K K r :=
    Finset.sum_range_sub' (fun k => pouStep t₀ t₁ K k r) K
  unfold pou
  rw [tele, pouT_step_zero, pouT_step_of_ge (t₀ := t₀) (t₁ := t₁) (K := K) (k := K)
    (by omega) le_rfl r]
  norm_num

theorem pouT_pou_nonneg {t₀ t₁ : ℝ} {K : ℕ} (ht : t₀ < t₁) (k : ℕ) (r : ℝ) :
    0 ≤ pou t₀ t₁ K k r := by
  unfold pou
  linarith [pouT_step_succ_le (K := K) ht k r]

/-! ## Derivatives -/

theorem pouT_deriv_mid {t₀ t₁ : ℝ} {K : ℕ} (hpos : 0 < gridH t₀ t₁ K) {k : ℕ} (hk0 : k ≠ 0)
    (hKk : k < K) (r : ℝ) :
    deriv (pouStep t₀ t₁ K k) r =
      deriv Real.smoothTransition ((r - gridPt t₀ t₁ K k) / gridH t₀ t₁ K + 1 / 2) *
        (1 / gridH t₀ t₁ K) := by
  have hf : pouStep t₀ t₁ K k = fun x =>
      Real.smoothTransition ((x - gridPt t₀ t₁ K k) / gridH t₀ t₁ K + 1 / 2) := by
    funext x
    exact pouT_step_mid hk0 hKk x
  have hlin : HasDerivAt (fun x : ℝ => (x - gridPt t₀ t₁ K k) / gridH t₀ t₁ K + 1 / 2)
      (1 / gridH t₀ t₁ K) r :=
    (((hasDerivAt_id r).sub_const (gridPt t₀ t₁ K k)).div_const (gridH t₀ t₁ K)).add_const _
  have hst : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition ((r - gridPt t₀ t₁ K k) / gridH t₀ t₁ K + 1 / 2))
      ((r - gridPt t₀ t₁ K k) / gridH t₀ t₁ K + 1 / 2) :=
    (pouT_st_contDiff.differentiable (by simp) _).hasDerivAt
  have hcomp : HasDerivAt (fun x : ℝ => Real.smoothTransition
      ((x - gridPt t₀ t₁ K k) / gridH t₀ t₁ K + 1 / 2))
      (deriv Real.smoothTransition ((r - gridPt t₀ t₁ K k) / gridH t₀ t₁ K + 1 / 2) *
        (1 / gridH t₀ t₁ K)) r :=
    HasDerivAt.comp (h₂ := Real.smoothTransition)
      (h := fun x : ℝ => (x - gridPt t₀ t₁ K k) / gridH t₀ t₁ K + 1 / 2) r hst hlin
  rw [hf]
  exact hcomp.deriv

theorem pouT_step_deriv_bound {t₀ t₁ : ℝ} {K : ℕ} (ht : t₀ < t₁) (hK : 0 < K) (D₀ : ℝ)
    (hD₀ : 0 ≤ D₀) (hD : ∀ y : ℝ, |deriv Real.smoothTransition y| ≤ D₀) (k : ℕ) (r : ℝ) :
    |deriv (pouStep t₀ t₁ K k) r| ≤ D₀ / gridH t₀ t₁ K := by
  have hpos := pouT_gridH_pos ht hK
  by_cases hk0 : k = 0
  · have hf : pouStep t₀ t₁ K k = fun _ => (1 : ℝ) := by
      funext x
      simp [pouStep, hk0]
    rw [hf, deriv_const]
    simp only [abs_zero]
    exact div_nonneg hD₀ hpos.le
  by_cases hKk : K ≤ k
  · have hf : pouStep t₀ t₁ K k = fun _ => (0 : ℝ) := by
      funext x
      exact pouT_step_of_ge hk0 hKk x
    rw [hf, deriv_const]
    simp only [abs_zero]
    exact div_nonneg hD₀ hpos.le
  rw [pouT_deriv_mid hpos hk0 (not_le.mp hKk) r, abs_mul, abs_of_pos (one_div_pos.mpr hpos),
    div_eq_mul_one_div D₀]
  exact mul_le_mul_of_nonneg_right (hD _) (one_div_pos.mpr hpos).le

theorem pouT_deriv_ne {t₀ t₁ : ℝ} {K : ℕ} (ht : t₀ < t₁) (hK : 0 < K) {k : ℕ} {r : ℝ}
    (hne : deriv (pouStep t₀ t₁ K k) r ≠ 0) :
    k ≠ 0 ∧ k < K ∧ |r - gridPt t₀ t₁ K k| < gridH t₀ t₁ K / 2 := by
  have hpos := pouT_gridH_pos ht hK
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hne
    have hf : pouStep t₀ t₁ K 0 = fun _ => (1 : ℝ) := by
      funext x
      simp [pouStep]
    rw [hf, deriv_const]
  have hKk : k < K := by
    by_contra hc
    apply hne
    have hf : pouStep t₀ t₁ K k = fun _ => (0 : ℝ) := by
      funext x
      exact pouT_step_of_ge hk0 (not_lt.mp hc) x
    rw [hf, deriv_const]
  refine ⟨hk0, hKk, ?_⟩
  by_contra hc
  push_neg at hc
  apply hne
  rw [pouT_deriv_mid hpos hk0 hKk r]
  have hA : deriv Real.smoothTransition ((r - gridPt t₀ t₁ K k) / gridH t₀ t₁ K + 1 / 2) = 0 := by
    rcases le_or_gt 0 (r - gridPt t₀ t₁ K k) with h0 | h0
    · rw [abs_of_nonneg h0] at hc
      apply pouT_st_deriv_zero_of_ge
      have h1 : (1 : ℝ) / 2 ≤ (r - gridPt t₀ t₁ K k) / gridH t₀ t₁ K := by
        rw [le_div_iff₀ hpos]
        linarith
      linarith
    · rw [abs_of_neg h0] at hc
      apply pouT_st_deriv_zero_of_le
      have h1 : (r - gridPt t₀ t₁ K k) / gridH t₀ t₁ K ≤ -(1 : ℝ) / 2 := by
        rw [div_le_iff₀ hpos]
        linarith
      linarith
  rw [hA, zero_mul]

theorem pouT_unique {t₀ t₁ : ℝ} {K : ℕ} (ht : t₀ < t₁) (hK : 0 < K) (r : ℝ) (j j' : ℕ)
    (hj : deriv (pouStep t₀ t₁ K j) r ≠ 0) (hj' : deriv (pouStep t₀ t₁ K j') r ≠ 0) :
    j = j' := by
  have hpos := pouT_gridH_pos ht hK
  obtain ⟨-, -, hb⟩ := pouT_deriv_ne ht hK hj
  obtain ⟨-, -, hb'⟩ := pouT_deriv_ne ht hK hj'
  have hab : |gridPt t₀ t₁ K j - gridPt t₀ t₁ K j'| < gridH t₀ t₁ K := by
    obtain ⟨h1, h2⟩ := abs_lt.mp hb
    obtain ⟨h3, h4⟩ := abs_lt.mp hb'
    rw [abs_lt]
    constructor <;> linarith
  have e : gridPt t₀ t₁ K j - gridPt t₀ t₁ K j' = ((j : ℝ) - (j' : ℝ)) * gridH t₀ t₁ K := by
    unfold gridPt
    ring
  rw [e, abs_mul, abs_of_pos hpos] at hab
  have h1 : |(j : ℝ) - (j' : ℝ)| < 1 := by
    by_contra hc
    push_neg at hc
    nlinarith
  obtain ⟨g1, g2⟩ := abs_lt.mp h1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h2 : (j : ℝ) + 1 ≤ (j' : ℝ) := by exact_mod_cast (show j + 1 ≤ j' from hlt)
    linarith
  · have h2 : (j' : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (show j' + 1 ≤ j from hgt)
    linarith

theorem pouT_sum_le (f : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ j, |f j| ≤ M)
    (hu : ∀ j j' : ℕ, f j ≠ 0 → f j' ≠ 0 → j = j') (s : Finset ℕ) :
    ∑ j ∈ s, |f j| ≤ M := by
  by_cases hex : ∃ j₀, f j₀ ≠ 0
  · obtain ⟨j₀, hj₀⟩ := hex
    calc ∑ j ∈ s, |f j| ≤ ∑ j ∈ s, (if j = j₀ then M else 0) := by
          apply Finset.sum_le_sum
          intro j _
          by_cases hj : j = j₀
          · rw [if_pos hj, hj]
            exact hb j₀
          · rw [if_neg hj]
            have hz : f j = 0 := by
              by_contra hne
              exact hj (hu j j₀ hne hj₀)
            rw [hz, abs_zero]
      _ ≤ M := by
          rw [Finset.sum_ite_eq']
          split_ifs <;> linarith
  · push_neg at hex
    simp only [hex, abs_zero, Finset.sum_const_zero]
    exact hM

theorem pouT_deriv_sum_le {t₀ t₁ : ℝ} {K : ℕ} (ht : t₀ < t₁) (hK : 0 < K) (D₀ : ℝ)
    (hD₀ : 0 ≤ D₀) (hD : ∀ y : ℝ, |deriv Real.smoothTransition y| ≤ D₀) (r : ℝ) :
    ∑ k ∈ Finset.range K, |deriv (pou t₀ t₁ K k) r| ≤ 2 * D₀ / gridH t₀ t₁ K := by
  have hpos := pouT_gridH_pos ht hK
  have hM : 0 ≤ D₀ / gridH t₀ t₁ K := div_nonneg hD₀ hpos.le
  have hsplit : ∀ k, deriv (pou t₀ t₁ K k) r =
      deriv (pouStep t₀ t₁ K k) r - deriv (pouStep t₀ t₁ K (k + 1)) r := by
    intro k
    unfold pou
    exact deriv_sub ((pouT_step_contDiff t₀ t₁ K k).differentiable (by simp) r)
      ((pouT_step_contDiff t₀ t₁ K (k + 1)).differentiable (by simp) r)
  have hB : ∀ j, |deriv (pouStep t₀ t₁ K j) r| ≤ D₀ / gridH t₀ t₁ K :=
    fun j => pouT_step_deriv_bound ht hK D₀ hD₀ hD j r
  have hU : ∀ j j' : ℕ, deriv (pouStep t₀ t₁ K j) r ≠ 0 →
      deriv (pouStep t₀ t₁ K j') r ≠ 0 → j = j' :=
    fun j j' h1 h2 => pouT_unique ht hK r j j' h1 h2
  have hS1 : ∑ k ∈ Finset.range K, |deriv (pouStep t₀ t₁ K k) r| ≤ D₀ / gridH t₀ t₁ K :=
    pouT_sum_le (fun j => deriv (pouStep t₀ t₁ K j) r) _ hM hB hU (Finset.range K)
  have hS2 : ∑ k ∈ Finset.range K, |deriv (pouStep t₀ t₁ K (k + 1)) r| ≤
      D₀ / gridH t₀ t₁ K :=
    pouT_sum_le (fun j => deriv (pouStep t₀ t₁ K (j + 1)) r) _ hM (fun j => hB (j + 1))
      (fun j j' h1 h2 => by
        have := hU (j + 1) (j' + 1) h1 h2
        omega) (Finset.range K)
  calc ∑ k ∈ Finset.range K, |deriv (pou t₀ t₁ K k) r|
      = ∑ k ∈ Finset.range K, |deriv (pouStep t₀ t₁ K k) r -
          deriv (pouStep t₀ t₁ K (k + 1)) r| :=
        Finset.sum_congr rfl (fun k _ => by rw [hsplit k])
    _ ≤ ∑ k ∈ Finset.range K, (|deriv (pouStep t₀ t₁ K k) r| +
          |deriv (pouStep t₀ t₁ K (k + 1)) r|) :=
        Finset.sum_le_sum (fun k _ => abs_sub _ _)
    _ = (∑ k ∈ Finset.range K, |deriv (pouStep t₀ t₁ K k) r|) +
          ∑ k ∈ Finset.range K, |deriv (pouStep t₀ t₁ K (k + 1)) r| :=
        Finset.sum_add_distrib
    _ ≤ D₀ / gridH t₀ t₁ K + D₀ / gridH t₀ t₁ K := add_le_add hS1 hS2
    _ = 2 * D₀ / gridH t₀ t₁ K := by ring

/-! ## Support -/

theorem pouT_pou_support {t₀ t₁ : ℝ} {K : ℕ} (ht : t₀ < t₁) (hK : 0 < K) (k : ℕ) (r : ℝ)
    (hr : r ∈ Icc t₀ t₁) (hne : pou t₀ t₁ K k r ≠ 0 ∨ deriv (pou t₀ t₁ K k) r ≠ 0) :
    gridPt t₀ t₁ K k - gridH t₀ t₁ K / 2 ≤ r ∧
      r ≤ gridPt t₀ t₁ K (k + 1) + gridH t₀ t₁ K / 2 := by
  have hpos := pouT_gridH_pos ht hK
  have hsucc := pouT_gridPt_succ t₀ t₁ K k
  have hKend := pouT_gridPt_K t₀ t₁ hK
  constructor
  · by_contra hlt
    push_neg at hlt
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pouT_gridPt_zero] at hlt
      linarith [hr.1]
    have hz : ∀ z : ℝ, z < gridPt t₀ t₁ K k - gridH t₀ t₁ K / 2 → pou t₀ t₁ K k z = 0 := by
      intro z hz
      have e1 : pouStep t₀ t₁ K k z = 0 :=
        pouT_step_zero_of_le ht hK hk0 (r := z) hz.le
      have e2 : pouStep t₀ t₁ K (k + 1) z = 0 :=
        pouT_step_zero_of_le ht hK (Nat.succ_ne_zero k) (r := z) (by rw [hsucc]; linarith)
      unfold pou
      linarith
    have hd : deriv (pou t₀ t₁ K k) r = 0 := by
      have hev : pou t₀ t₁ K k =ᶠ[𝓝 r] (fun _ => (0 : ℝ)) := by
        filter_upwards [Iio_mem_nhds hlt] with z hzmem
        exact hz z hzmem
      rw [hev.deriv_eq, deriv_const]
    rcases hne with h | h
    · exact h (hz r hlt)
    · exact h hd
  · by_contra hgt
    push_neg at hgt
    have hk1 : k + 1 < K := by
      by_contra hc
      have hKle : K ≤ k + 1 := not_lt.mp hc
      have hK' : (K : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hKle
      have hle : gridPt t₀ t₁ K K ≤ gridPt t₀ t₁ K (k + 1) := by
        have := mul_le_mul_of_nonneg_right hK' hpos.le
        unfold gridPt
        linarith
      linarith [hr.2]
    have hkK : k < K := by omega
    have hz : ∀ z : ℝ, gridPt t₀ t₁ K (k + 1) + gridH t₀ t₁ K / 2 < z →
        pou t₀ t₁ K k z = 0 := by
      intro z hz
      have e1 : pouStep t₀ t₁ K k z = 1 :=
        pouT_step_one_of_ge ht hK hkK (r := z) (by linarith)
      have e2 : pouStep t₀ t₁ K (k + 1) z = 1 :=
        pouT_step_one_of_ge ht hK hk1 (r := z) hz.le
      unfold pou
      linarith
    have hd : deriv (pou t₀ t₁ K k) r = 0 := by
      have hev : pou t₀ t₁ K k =ᶠ[𝓝 r] (fun _ => (0 : ℝ)) := by
        filter_upwards [Ioi_mem_nhds hgt] with z hzmem
        exact hz z hzmem
      rw [hev.deriv_eq, deriv_const]
    rcases hne with h | h
    · exact h (hz r hgt)
    · exact h hd

/-! ## Assembly -/

/-- **Leaf `/3`: the partition of unity in age.** -/
theorem pouProps : UnforcedLeray.Short.IIb.TdSums.PouProps := by
  obtain ⟨D₀, hD₀, hD⟩ := pouT_st_deriv_bdd
  refine ⟨fun t₀ t₁ K k => pou_contDiff_aux t₀ t₁ K k,
    fun t₀ t₁ K hK r => pouT_pou_sum hK r, 2 * D₀, by linarith, ?_⟩
  intro t₀ t₁ K ht hK
  exact ⟨fun k r => pouT_pou_nonneg ht k r,
    fun r => pouT_deriv_sum_le ht hK D₀ hD₀ hD r,
    fun k r hr hne => pouT_pou_support ht hK k r hr hne⟩

end TdSums

end UnforcedLeray.Short.IIb
