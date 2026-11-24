import UnforcedLeray.Infra.VolterraEvolution
import UnforcedLeray.Infra.EvolutionContinuity

/-!
# L3 helper: abstract consequences of the Volterra construction

Step L3 (`EvolutionStep`, `paper/main.tex` lines 299–306, blueprint unit B0713) is proved by
instantiating `UnforcedLeray.Infra.VolterraEvolution` twice (on `X = H¹_div` and on
`Z = H²_div`). This file proves, for an abstract `VolterraData ℝ U W`, the facts the
manuscript uses beyond the infrastructure:

* `global_duhamel`: the Duhamel formula `E(τ,s) = S₀(τ-s) + ∫_s^τ S(τ-r) B(r) E(r,s) dr`
  for every `s ≤ τ`, not only on unit strips (line 299), when the free family is a semigroup
  compatible with the smoothing family for all elapsed times;
* `smoothing_bound`: the short-time smoothing `‖E(τ,s) x‖ ≤ K (τ-s)^{-1/2} ‖ι x‖` on strips of
  bounded length (lines 302–303, "with `L² → X` and `X → Z` norms `C(τ-s)^{-1/2}` at short
  times"), when `S₀(t) = S(t) ι` for a weaker norm `ι`; the proof is a singular Gronwall
  argument with the Beta integral `∫_s^τ (τ-r)^{-1/2} (r-s)^{-1/2} dr = π` (line 304,
  "the integrable convolution of two square-root kernels");
* `intertwine`: two Volterra evolutions intertwined by `J` on the data are intertwined by `J`
  (used for `Z ⊂ X`);
* `exists_norm_le_of_periodic`: continuous periodic coefficients are bounded.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral Real

namespace UnforcedLeray.Loc.L03Evolution

open UnforcedLeray.Infra.VolterraEvolution

/-- A continuous periodic function with nonzero period is bounded. -/
theorem exists_norm_le_of_periodic {E : Type*} [SeminormedAddCommGroup E] {f : ℝ → E} {P : ℝ}
    (hP : P ≠ 0) (hper : Function.Periodic f P) (hf : Continuous f) :
    ∃ β : ℝ, ∀ t, ‖f t‖ ≤ β := by
  obtain ⟨C, hC⟩ :=
    isBounded_iff_forall_norm_le.mp (hper.compact_of_continuous hP hf).isBounded
  exact ⟨C, fun t => hC _ (mem_range_self t)⟩

/-- The Beta integral `∫_s^τ (τ-r)^{-1/2} (r-s)^{-1/2} dr = π` (line 304). -/
theorem integral_beta_half {s τ : ℝ} (h : s < τ) :
    ∫ r in s..τ, (τ - r) ^ (-(1 / 2 : ℝ)) * (r - s) ^ (-(1 / 2 : ℝ)) = π := by
  rw [integral_kernel_mul_rpow_of_lt h (by norm_num)]
  have h1 : (-(1 / 2 : ℝ)) + 1 / 2 = 0 := by norm_num
  have h2 : (-(1 / 2 : ℝ)) + 1 = 1 / 2 := by norm_num
  have h3 : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  rw [h1, h2, h3, rpow_zero, Gamma_one, Gamma_one_half_eq, mul_self_sqrt pi_pos.le]
  ring

theorem intervalIntegrable_beta_half {s τ : ℝ} (h : s < τ) :
    IntervalIntegrable (fun r => (τ - r) ^ (-(1 / 2 : ℝ)) * (r - s) ^ (-(1 / 2 : ℝ)))
      volume s τ :=
  intervalIntegrable_of_integral_ne_zero (by rw [integral_beta_half h]; exact pi_pos.ne')

section Abstract

variable {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **Global Duhamel formula** (line 299) for every `s ≤ τ`, with the integrability of the
integrand, when `S₀` is a semigroup compatible with `S` for all elapsed times. -/
theorem global_duhamel (V : VolterraData ℝ U W) (hV : V.Compatible)
    (hS₀S₀ : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (V.S₀ a).comp (V.S₀ b) = V.S₀ (a + b))
    (hS₀S : ∀ a b : ℝ, 0 ≤ a → 0 < b → (V.S₀ a).comp (V.S b) = V.S (a + b)) :
    ∀ s τ : ℝ, s ≤ τ → ∀ x : U,
      IntervalIntegrable (fun r => V.S (τ - r) (V.B r (V.evolution r s x))) volume s τ ∧
      V.evolution τ s x =
        V.S₀ (τ - s) x + ∫ r in s..τ, V.S (τ - r) (V.B r (V.evolution r s x)) := by
  have hstrip : ∀ s τ : ℝ, s ≤ τ → τ ≤ s + 1 → ∀ x : U,
      IntervalIntegrable (fun r => V.S (τ - r) (V.B r (V.evolution r s x))) volume s τ ∧
      V.evolution τ s x =
        V.S₀ (τ - s) x + ∫ r in s..τ, V.S (τ - r) (V.B r (V.evolution r s x)) := by
    intro s τ h1 h2 x
    exact ⟨V.intervalIntegrable_integrand h1 h2
      ((VolterraData.continuousOn_evolution hV s x).mono fun r hr => hr.1),
      VolterraData.evolution_volterra hV ⟨h1, h2⟩ x⟩
  suffices H : ∀ n : ℕ, ∀ s τ : ℝ, s ≤ τ → τ ≤ s + n + 1 → ∀ x : U,
      IntervalIntegrable (fun r => V.S (τ - r) (V.B r (V.evolution r s x))) volume s τ ∧
      V.evolution τ s x =
        V.S₀ (τ - s) x + ∫ r in s..τ, V.S (τ - r) (V.B r (V.evolution r s x)) by
    intro s τ hsτ x
    exact H ⌊τ - s⌋₊ s τ hsτ (by have := Nat.lt_floor_add_one (τ - s); linarith) x
  intro n
  induction n with
  | zero =>
    intro s τ h1 h2 x
    exact hstrip s τ h1 (by simpa using h2) x
  | succ n ih =>
    intro s τ h1 h2 x
    by_cases h : τ ≤ s + 1
    · exact hstrip s τ h1 h x
    rw [not_le] at h
    obtain ⟨hI1, hE1⟩ := hstrip s (s + 1) (by linarith) le_rfl x
    obtain ⟨hI2, hE2⟩ := ih (s + 1) τ h.le (by push_cast at h2; linarith)
      (V.evolution (s + 1) s x)
    have hEq2 : EqOn
        (fun r => V.S (τ - r) (V.B r (V.evolution r (s + 1) (V.evolution (s + 1) s x))))
        (fun r => V.S (τ - r) (V.B r (V.evolution r s x))) (uIcc (s + 1) τ) := by
      intro r hr
      rw [uIcc_of_le h.le] at hr
      simp only [VolterraData.evolution_apply_comp hV (show s ≤ s + 1 by linarith) hr.1 x]
    have hEq1 : EqOn
        (fun r => V.S₀ (τ - (s + 1)) (V.S (s + 1 - r) (V.B r (V.evolution r s x))))
        (fun r => V.S (τ - r) (V.B r (V.evolution r s x))) (uIoo s (s + 1)) := by
      intro r hr
      rw [uIoo_of_le (by linarith)] at hr
      simp only
      rw [← ContinuousLinearMap.comp_apply, hS₀S _ _ (by linarith) (by linarith [hr.2])]
      congr 2
      ring
    have hI1' : IntervalIntegrable
        (fun r => V.S₀ (τ - (s + 1)) (V.S (s + 1 - r) (V.B r (V.evolution r s x))))
        volume s (s + 1) :=
      ⟨(V.S₀ (τ - (s + 1))).integrable_comp hI1.1, (V.S₀ (τ - (s + 1))).integrable_comp hI1.2⟩
    have hJ1 := hI1'.congr_uIoo hEq1
    have hJ2 : IntervalIntegrable (fun r => V.S (τ - r) (V.B r (V.evolution r s x)))
        volume (s + 1) τ := hI2.congr (hEq2.mono uIoc_subset_uIcc)
    refine ⟨hJ1.trans hJ2, ?_⟩
    have e1 : ∫ r in (s + 1)..τ,
        V.S (τ - r) (V.B r (V.evolution r (s + 1) (V.evolution (s + 1) s x))) =
        ∫ r in (s + 1)..τ, V.S (τ - r) (V.B r (V.evolution r s x)) := integral_congr hEq2
    have e2 : V.S₀ (τ - (s + 1)) (∫ r in s..(s + 1), V.S (s + 1 - r) (V.B r (V.evolution r s x)))
        = ∫ r in s..(s + 1), V.S (τ - r) (V.B r (V.evolution r s x)) := by
      rw [← (V.S₀ (τ - (s + 1))).intervalIntegral_comp_comm hI1]
      exact integral_congr_uIoo hEq1
    have e3 : V.S₀ (τ - (s + 1)) (V.S₀ (s + 1 - s) x) = V.S₀ (τ - s) x := by
      rw [← ContinuousLinearMap.comp_apply, hS₀S₀ _ _ (by linarith) (by linarith)]
      congr 2
      ring
    calc V.evolution τ s x = V.evolution τ (s + 1) (V.evolution (s + 1) s x) :=
          (VolterraData.evolution_apply_comp hV (by linarith) h.le x).symm
      _ = _ := hE2
      _ = V.S₀ (τ - s) x + ((∫ r in s..(s + 1), V.S (τ - r) (V.B r (V.evolution r s x))) +
            ∫ r in (s + 1)..τ, V.S (τ - r) (V.B r (V.evolution r s x))) := by
          rw [e1]
          nth_rewrite 1 [hE1]
          rw [map_add, e3, e2, add_assoc]
      _ = _ := by rw [integral_add_adjacent_intervals hJ1 hJ2]

/-- **Short-time smoothing** (lines 302–304): if `S₀(t) = S(t) ι` for `0 < t ≤ 1`, then
`‖E(τ,s) x‖ ≤ 2 C₀ ‖ι x‖ (τ-s)^{-1/2}` for `0 < τ - s ≤ δ`. Singular Gronwall argument with the
Beta integral. -/
theorem smoothing_short (V : VolterraData ℝ U W) (hV : V.Compatible) (ι : U →L[ℝ] W)
    (hι : ∀ t, 0 < t → t ≤ 1 → V.S₀ t = (V.S t).comp ι) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ s τ : ℝ, s < τ → τ ≤ s + δ → ∀ x : U,
      ‖V.evolution τ s x‖ ≤ 2 * V.C₀ * ‖ι x‖ * (τ - s) ^ (-(1 / 2 : ℝ)) := by
  have hC₀ := V.C₀_nonneg
  have hβ := V.β_nonneg
  have hk0 : 0 ≤ V.C₀ * V.β * π := by positivity
  obtain ⟨k, hk⟩ : ∃ k, k = V.C₀ * V.β * π := ⟨_, rfl⟩
  rw [← hk] at hk0
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = min 1 (1 / (4 * k ^ 2 + 1)) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; exact lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := by rw [hδ]; exact min_le_left _ _
  have hkδ : k * δ ^ (1 / 2 : ℝ) ≤ 1 / 2 := by
    have hsq : (δ ^ (1 / 2 : ℝ)) ^ 2 = δ := by
      rw [← rpow_natCast, ← rpow_mul hδpos.le]
      norm_num
    have hle : k ^ 2 * δ ≤ 1 / 4 := by
      have h1 : δ ≤ 1 / (4 * k ^ 2 + 1) := by rw [hδ]; exact min_le_right _ _
      calc k ^ 2 * δ ≤ k ^ 2 * (1 / (4 * k ^ 2 + 1)) :=
            mul_le_mul_of_nonneg_left h1 (sq_nonneg k)
        _ ≤ 1 / 4 := by
            rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
    by_contra hcon
    push Not at hcon
    have h2 : (1 / 2 : ℝ) ^ 2 < (k * δ ^ (1 / 2 : ℝ)) ^ 2 :=
      pow_lt_pow_left₀ hcon (by norm_num) two_ne_zero
    rw [mul_pow, hsq] at h2
    linarith
  refine ⟨δ, hδpos, hδ1, fun s τ hsτ hτ x => ?_⟩
  obtain ⟨c, hc⟩ : ∃ c, c = V.C₀ * ‖ι x‖ := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = V.stripBound * ‖x‖ := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hA0 : 0 ≤ A := by rw [hA]; exact mul_nonneg V.stripBound_nonneg (norm_nonneg _)
  -- a priori bound on the unit strip
  have hF1 : ∀ r ∈ Icc s (s + 1), ‖V.evolution r s x‖ ≤ A := by
    intro r hr
    rw [VolterraData.evolution_eq_stripEvolution hV hr, hA]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (V.norm_stripEvolution_le r s) (norm_nonneg _))
  -- the Volterra inequality
  have hgi : ∀ t, s < t → t ≤ s + 1 → IntervalIntegrable
      (fun r => (t - r) ^ (-(1 / 2 : ℝ)) * ‖V.evolution r s x‖) volume s t := by
    intro t hst ht1
    have hφc : ContinuousOn (fun r => ‖V.evolution r s x‖) (uIcc s t) := by
      rw [uIcc_of_le hst.le]
      exact ((VolterraData.continuousOn_evolution hV s x).mono fun r hr => hr.1).norm
    exact (intervalIntegrable_kernel t s t).mul_continuousOn hφc
  have hF2 : ∀ t, s < t → t ≤ s + 1 → ‖V.evolution t s x‖ ≤ c * (t - s) ^ (-(1 / 2 : ℝ)) +
      V.C₀ * V.β * ∫ r in s..t, (t - r) ^ (-(1 / 2 : ℝ)) * ‖V.evolution r s x‖ := by
    intro t hst ht1
    rw [VolterraData.evolution_volterra hV ⟨hst.le, ht1⟩ x]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [hι (t - s) (by linarith) (by linarith), ContinuousLinearMap.comp_apply]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      calc ‖V.S (t - s)‖ * ‖ι x‖ ≤ V.C₀ * (t - s) ^ (-(1 / 2 : ℝ)) * ‖ι x‖ :=
            mul_le_mul_of_nonneg_right (V.norm_S_le _ (by linarith) (by linarith))
              (norm_nonneg _)
        _ = c * (t - s) ^ (-(1 / 2 : ℝ)) := by rw [hc]; ring
    · rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.norm_integral_le_of_norm_le hst.le ?_
        ((hgi t hst ht1).const_mul _)
      filter_upwards [ae_ne_real t] with r hrt hr
      have hr' : r ∈ Ico s t := ⟨hr.1.le, lt_of_le_of_ne hr.2 hrt⟩
      refine (V.norm_integrand_le ht1 hr' (fun r => V.evolution r s x)).trans (le_of_eq ?_)
      ring
  -- the iteration
  have hiter : ∀ n : ℕ, ∀ t, s < t → t ≤ s + δ →
      (t - s) ^ (1 / 2 : ℝ) * ‖V.evolution t s x‖ ≤ 2 * c + A / 2 ^ n := by
    intro n
    induction n with
    | zero =>
      intro t hst ht
      have h1 : (t - s) ^ (1 / 2 : ℝ) ≤ 1 := rpow_le_one (by linarith) (by linarith) (by norm_num)
      have h2 : ‖V.evolution t s x‖ ≤ A := hF1 t ⟨hst.le, by linarith⟩
      calc (t - s) ^ (1 / 2 : ℝ) * ‖V.evolution t s x‖ ≤ 1 * A :=
            mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
        _ ≤ 2 * c + A / 2 ^ 0 := by simp only [pow_zero, div_one, one_mul]; linarith
    | succ n ih =>
      intro t hst ht
      obtain ⟨a, ha⟩ : ∃ a, a = 2 * c + A / 2 ^ n := ⟨_, rfl⟩
      have ha0 : 0 ≤ a := by rw [ha]; positivity
      have hpt : ∀ r ∈ Ioo s t, (t - r) ^ (-(1 / 2 : ℝ)) * ‖V.evolution r s x‖ ≤
          (t - r) ^ (-(1 / 2 : ℝ)) * (r - s) ^ (-(1 / 2 : ℝ)) * a := by
        intro r hr
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (rpow_nonneg (by linarith [hr.2]) _)
        have hrs : 0 < r - s := by linarith [hr.1]
        have hih := ih r hr.1 (by linarith [hr.2])
        rw [← ha] at hih
        calc ‖V.evolution r s x‖ = (r - s) ^ (-(1 / 2 : ℝ)) *
              ((r - s) ^ (1 / 2 : ℝ) * ‖V.evolution r s x‖) := by
              rw [← mul_assoc, ← rpow_add hrs]
              norm_num
          _ ≤ (r - s) ^ (-(1 / 2 : ℝ)) * a :=
              mul_le_mul_of_nonneg_left hih (rpow_nonneg hrs.le _)
      have hint : ∫ r in s..t, (t - r) ^ (-(1 / 2 : ℝ)) * ‖V.evolution r s x‖ ≤ π * a := by
        calc _ ≤ ∫ r in s..t, (t - r) ^ (-(1 / 2 : ℝ)) * (r - s) ^ (-(1 / 2 : ℝ)) * a :=
              integral_mono_on_of_le_Ioo hst.le (hgi t hst (by linarith))
                ((intervalIntegrable_beta_half hst).mul_const a) hpt
          _ = π * a := by rw [intervalIntegral.integral_mul_const, integral_beta_half hst]
      have hF := hF2 t hst (by linarith)
      have hq0 : 0 ≤ (t - s) ^ (1 / 2 : ℝ) := rpow_nonneg (by linarith) _
      have hqp : (t - s) ^ (1 / 2 : ℝ) * (t - s) ^ (-(1 / 2 : ℝ)) = 1 := by
        rw [← rpow_add (by linarith)]
        norm_num
      have hqδ : (t - s) ^ (1 / 2 : ℝ) ≤ δ ^ (1 / 2 : ℝ) :=
        rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      have hkq : k * (t - s) ^ (1 / 2 : ℝ) ≤ 1 / 2 :=
        (mul_le_mul_of_nonneg_left hqδ hk0).trans hkδ
      have hCβ : 0 ≤ V.C₀ * V.β := mul_nonneg hC₀ hβ
      calc (t - s) ^ (1 / 2 : ℝ) * ‖V.evolution t s x‖
          ≤ (t - s) ^ (1 / 2 : ℝ) * (c * (t - s) ^ (-(1 / 2 : ℝ)) + V.C₀ * V.β * (π * a)) :=
            mul_le_mul_of_nonneg_left
              (hF.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hint hCβ))) hq0
        _ = c + (k * (t - s) ^ (1 / 2 : ℝ)) * a := by
            rw [hk]
            linear_combination c * hqp
        _ ≤ c + 1 / 2 * a := by gcongr
        _ = 2 * c + A / 2 ^ (n + 1) := by rw [ha, pow_succ]; ring
  -- passage to the limit
  have hlim : Tendsto (fun n : ℕ => 2 * c + A / 2 ^ n) atTop (𝓝 (2 * c + 0)) :=
    tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two))
  have hq : (τ - s) ^ (1 / 2 : ℝ) * ‖V.evolution τ s x‖ ≤ 2 * c := by
    have := ge_of_tendsto' hlim (fun n => hiter n τ hsτ hτ)
    simpa using this
  have hts : 0 < τ - s := by linarith
  calc ‖V.evolution τ s x‖ = (τ - s) ^ (-(1 / 2 : ℝ)) *
        ((τ - s) ^ (1 / 2 : ℝ) * ‖V.evolution τ s x‖) := by
        rw [← mul_assoc, ← rpow_add hts]
        norm_num
    _ ≤ (τ - s) ^ (-(1 / 2 : ℝ)) * (2 * c) :=
        mul_le_mul_of_nonneg_left hq (rpow_nonneg hts.le _)
    _ = 2 * V.C₀ * ‖ι x‖ * (τ - s) ^ (-(1 / 2 : ℝ)) := by rw [hc]; ring

/-- **Smoothing on strips of bounded length** (lines 302–303): for every `L > 0` there is `K`
with `‖E(τ,s) x‖ ≤ K ‖ι x‖ (τ-s)^{-1/2}` for `0 < τ - s ≤ L`. -/
theorem smoothing_bound (V : VolterraData ℝ U W) (hV : V.Compatible) (ι : U →L[ℝ] W)
    (hι : ∀ t, 0 < t → t ≤ 1 → V.S₀ t = (V.S t).comp ι) (L : ℝ) (hL : 0 < L) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s τ : ℝ, s < τ → τ ≤ s + L → ∀ x : U,
      ‖V.evolution τ s x‖ ≤ K * ‖ι x‖ * (τ - s) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨δ, hδ0, -, hshort⟩ := smoothing_short V hV ι hι
  obtain ⟨M, ω, hM, hω, hMω⟩ := V.exists_norm_evolution_le
  have hC₀ := V.C₀_nonneg
  obtain ⟨K₂, hK₂⟩ : ∃ K₂, K₂ = M * exp (ω * L) * (2 * V.C₀ * δ ^ (-(1 / 2 : ℝ))) *
      L ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  have hK₂0 : 0 ≤ K₂ := by
    rw [hK₂]
    have := rpow_nonneg hδ0.le (-(1 / 2 : ℝ))
    have := rpow_nonneg hL.le (1 / 2 : ℝ)
    have : 0 ≤ M := by linarith
    positivity
  refine ⟨2 * V.C₀ + K₂, by positivity, fun s τ hsτ hτ x => ?_⟩
  have hts : 0 < τ - s := by linarith
  have hp0 : 0 ≤ (τ - s) ^ (-(1 / 2 : ℝ)) := rpow_nonneg hts.le _
  have hι0 : 0 ≤ ‖ι x‖ * (τ - s) ^ (-(1 / 2 : ℝ)) := mul_nonneg (norm_nonneg _) hp0
  by_cases hshort' : τ ≤ s + δ
  · refine (hshort s τ hsτ hshort' x).trans ?_
    rw [mul_assoc, mul_assoc (2 * V.C₀ + K₂)]
    exact mul_le_mul_of_nonneg_right (by linarith) hι0
  · push Not at hshort'
    have hlaw := VolterraData.evolution_apply_comp hV (show s ≤ s + δ by linarith) hshort'.le x
    rw [← hlaw]
    have h1 : ‖V.evolution τ (s + δ)‖ ≤ M * exp (ω * L) :=
      (hMω _ _ hshort'.le).trans (mul_le_mul_of_nonneg_left
        (exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) hω)) (by linarith))
    have h2 := hshort s (s + δ) (by linarith) le_rfl x
    rw [add_sub_cancel_left] at h2
    have h3 : 1 ≤ L ^ (1 / 2 : ℝ) * (τ - s) ^ (-(1 / 2 : ℝ)) := by
      have hle : (τ - s) ^ (1 / 2 : ℝ) ≤ L ^ (1 / 2 : ℝ) :=
        rpow_le_rpow hts.le (by linarith) (by norm_num)
      have hqp : (τ - s) ^ (1 / 2 : ℝ) * (τ - s) ^ (-(1 / 2 : ℝ)) = 1 := by
        rw [← rpow_add hts]
        norm_num
      calc (1 : ℝ) = (τ - s) ^ (1 / 2 : ℝ) * (τ - s) ^ (-(1 / 2 : ℝ)) := hqp.symm
        _ ≤ L ^ (1 / 2 : ℝ) * (τ - s) ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hle hp0
    have hM0 : 0 ≤ M * exp (ω * L) := mul_nonneg (by linarith) (exp_pos _).le
    have hX0 : 0 ≤ 2 * V.C₀ * ‖ι x‖ * δ ^ (-(1 / 2 : ℝ)) := by
      have := rpow_nonneg hδ0.le (-(1 / 2 : ℝ))
      positivity
    calc ‖V.evolution τ (s + δ) (V.evolution (s + δ) s x)‖
        ≤ ‖V.evolution τ (s + δ)‖ * ‖V.evolution (s + δ) s x‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * exp (ω * L) * (2 * V.C₀ * ‖ι x‖ * δ ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul h1 h2 (norm_nonneg _) hM0
      _ = M * exp (ω * L) * (2 * V.C₀ * ‖ι x‖ * δ ^ (-(1 / 2 : ℝ))) * 1 := by ring
      _ ≤ M * exp (ω * L) * (2 * V.C₀ * ‖ι x‖ * δ ^ (-(1 / 2 : ℝ))) *
            (L ^ (1 / 2 : ℝ) * (τ - s) ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg hM0 hX0)
      _ = K₂ * ‖ι x‖ * (τ - s) ^ (-(1 / 2 : ℝ)) := by rw [hK₂]; ring
      _ ≤ (2 * V.C₀ + K₂) * ‖ι x‖ * (τ - s) ^ (-(1 / 2 : ℝ)) := by
          rw [mul_assoc, mul_assoc (2 * V.C₀ + K₂)]
          exact mul_le_mul_of_nonneg_right (by linarith) hι0

/-- **Intertwining.** If `J` intertwines the free parts and the perturbations of two Volterra
problems, it intertwines their evolutions (used with `J = ι_Z : Z → X`). -/
theorem intertwine {U₁ W₁ : Type*} [NormedAddCommGroup U₁] [NormedSpace ℝ U₁] [CompleteSpace U₁]
    [NormedAddCommGroup W₁] [NormedSpace ℝ W₁]
    (V₁ : VolterraData ℝ U₁ W₁) (hV₁ : V₁.Compatible) (V₂ : VolterraData ℝ U W)
    (hV₂ : V₂.Compatible) (J : U₁ →L[ℝ] U)
    (hS₀ : ∀ t, 0 ≤ t → t ≤ 1 → ∀ w, J (V₁.S₀ t w) = V₂.S₀ t (J w))
    (hSB : ∀ t r, 0 < t → t ≤ 1 → ∀ w, J (V₁.S t (V₁.B r w)) = V₂.S t (V₂.B r (J w))) :
    ∀ s τ, s ≤ τ → ∀ w, J (V₁.evolution τ s w) = V₂.evolution τ s (J w) := by
  have hstrip : ∀ s τ, τ ∈ Icc s (s + 1) → ∀ w,
      J (V₁.evolution τ s w) = V₂.evolution τ s (J w) := by
    intro s τ hτ w
    have hu : ContinuousOn (fun t => J (V₁.evolution t s w)) (Icc s (s + 1)) :=
      J.continuous.comp_continuousOn
        ((VolterraData.continuousOn_evolution hV₁ s w).mono Icc_subset_Ici_self)
    have heq : ∀ t ∈ Icc s (s + 1), J (V₁.evolution t s w) =
        V₂.S₀ (t - s) (J w) + ∫ r in s..t, V₂.S (t - r) (V₂.B r (J (V₁.evolution r s w))) := by
      intro t ht
      have hint := V₁.intervalIntegrable_integrand ht.1 ht.2
        ((VolterraData.continuousOn_evolution hV₁ s w).mono fun r hr => hr.1)
      rw [VolterraData.evolution_volterra hV₁ ht w, map_add,
        hS₀ _ (by linarith [ht.1]) (by linarith [ht.2]), ← J.intervalIntegral_comp_comm hint]
      congr 1
      refine integral_congr_uIoo fun r hr => ?_
      rw [uIoo_of_le ht.1] at hr
      exact hSB _ _ (by linarith [hr.2]) (by linarith [hr.1, ht.2]) _
    rw [V₂.eqOn_stripEvolution le_rfl hu heq τ hτ,
      ← VolterraData.evolution_eq_stripEvolution hV₂ hτ]
  suffices H : ∀ n : ℕ, ∀ s τ : ℝ, s ≤ τ → τ ≤ s + n + 1 → ∀ w,
      J (V₁.evolution τ s w) = V₂.evolution τ s (J w) by
    intro s τ hsτ w
    exact H ⌊τ - s⌋₊ s τ hsτ (by have := Nat.lt_floor_add_one (τ - s); linarith) w
  intro n
  induction n with
  | zero =>
    intro s τ h1 h2 w
    exact hstrip s τ ⟨h1, by simpa using h2⟩ w
  | succ n ih =>
    intro s τ h1 h2 w
    by_cases h : τ ≤ s + 1
    · exact hstrip s τ ⟨h1, h⟩ w
    · rw [not_le] at h
      rw [← VolterraData.evolution_apply_comp hV₁ (show s ≤ s + 1 by linarith) h.le w,
        ih (s + 1) τ h.le (by push_cast at h2; linarith),
        hstrip s (s + 1) ⟨by linarith, le_rfl⟩ w,
        VolterraData.evolution_apply_comp hV₂ (show s ≤ s + 1 by linarith) h.le]

end Abstract

end UnforcedLeray.Loc.L03Evolution
