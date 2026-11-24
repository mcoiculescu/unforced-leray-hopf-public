import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace L2EnergyAux

/-- Sequence version: pointwise convergence and convergence of the sums of the norms give
convergence of `eLpNorm (G n k - F₀ k)` for each component. Fatou applies to
`2 Σ(|G_n|² + |F₀|²) - Σ|G_n - F₀|² ≥ 0`. -/
lemma core_seq (μ : Measure (ℝ × ℝ)) (G : ℕ → Fin 2 → ℝ × ℝ → ℂ) (F₀ : Fin 2 → ℝ × ℝ → ℂ)
    (hG : ∀ n k, MemLp (G n k) 2 μ) (hF₀ : ∀ k, MemLp (F₀ k) 2 μ)
    (hpt : ∀ k x, Tendsto (fun n => G n k x) atTop (𝓝 (F₀ k x)))
    (hS : Tendsto (fun n => ∑ k, ∫ x, ‖G n k x‖ ^ 2 ∂μ) atTop
      (𝓝 (∑ k, ∫ x, ‖F₀ k x‖ ^ 2 ∂μ))) :
    ∀ k, Tendsto (fun n => eLpNorm (G n k - F₀ k) 2 μ) atTop (𝓝 0) := by
  have hI : ∀ n k, Integrable (fun x => ‖G n k x‖ ^ 2) μ :=
    fun n k => ((hG n k).norm).integrable_sq
  have hI0 : ∀ k, Integrable (fun x => ‖F₀ k x‖ ^ 2) μ :=
    fun k => ((hF₀ k).norm).integrable_sq
  have hD : ∀ n k, Integrable (fun x => ‖G n k x - F₀ k x‖ ^ 2) μ :=
    fun n k => (((hG n k).sub (hF₀ k)).norm).integrable_sq
  obtain ⟨S, hSdef⟩ : ∃ S : ℕ → ℝ, S = fun n => ∑ k, ∫ x, ‖G n k x‖ ^ 2 ∂μ := ⟨_, rfl⟩
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : ℝ, S₀ = ∑ k, ∫ x, ‖F₀ k x‖ ^ 2 ∂μ := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℕ → ℝ, A = fun n => ∑ k, ∫ x, ‖G n k x - F₀ k x‖ ^ 2 ∂μ :=
    ⟨_, rfl⟩
  rw [← hSdef, ← hS₀] at hS
  -- the nonnegative integrand `g n`
  obtain ⟨g, hgdef⟩ : ∃ g : ℕ → ℝ × ℝ → ℝ, g = fun n x => 2 * (∑ k, ‖G n k x‖ ^ 2 +
      ∑ k, ‖F₀ k x‖ ^ 2) - ∑ k, ‖G n k x - F₀ k x‖ ^ 2 := ⟨_, rfl⟩
  have hgI : ∀ n, Integrable (g n) μ := by
    intro n
    rw [hgdef]
    exact (((integrable_finsetSum Finset.univ (fun k _ => hI n k)).add
      (integrable_finsetSum Finset.univ (fun k _ => hI0 k))).const_mul 2).sub
      (integrable_finsetSum Finset.univ (fun k _ => hD n k))
  have hgnn : ∀ n x, 0 ≤ g n x := by
    intro n x
    rw [hgdef]
    have hsum : ∑ k, ‖G n k x - F₀ k x‖ ^ 2 ≤ ∑ k, 2 * (‖G n k x‖ ^ 2 + ‖F₀ k x‖ ^ 2) := by
      refine Finset.sum_le_sum fun k _ => ?_
      have h1 := norm_sub_le (G n k x) (F₀ k x)
      have h2 : ‖G n k x - F₀ k x‖ ^ 2 ≤ (‖G n k x‖ + ‖F₀ k x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [sq_nonneg (‖G n k x‖ - ‖F₀ k x‖)]
    have e : 2 * (∑ k, ‖G n k x‖ ^ 2 + ∑ k, ‖F₀ k x‖ ^ 2) =
        ∑ k, 2 * (‖G n k x‖ ^ 2 + ‖F₀ k x‖ ^ 2) := by
      simp [Finset.sum_add_distrib, mul_add]
    show 0 ≤ 2 * (∑ k, ‖G n k x‖ ^ 2 + ∑ k, ‖F₀ k x‖ ^ 2) - ∑ k, ‖G n k x - F₀ k x‖ ^ 2
    rw [e]
    linarith
  -- pointwise limit of `g n`
  have hlimg : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (4 * ∑ k, ‖F₀ k x‖ ^ 2)) := by
    intro x
    have h1 : ∀ k, Tendsto (fun n => ‖G n k x‖ ^ 2) atTop (𝓝 (‖F₀ k x‖ ^ 2)) :=
      fun k => ((hpt k x).norm).pow 2
    have h2 : ∀ k, Tendsto (fun n => ‖G n k x - F₀ k x‖ ^ 2) atTop (𝓝 0) := fun k => by
      have := (((hpt k x).sub_const (F₀ k x)).norm).pow 2
      simpa using this
    have hsum1 : Tendsto (fun n => ∑ k, ‖G n k x‖ ^ 2) atTop (𝓝 (∑ k, ‖F₀ k x‖ ^ 2)) :=
      tendsto_finsetSum _ fun k _ => h1 k
    have hsum2 : Tendsto (fun n => ∑ k, ‖G n k x - F₀ k x‖ ^ 2) atTop (𝓝 0) := by
      have := tendsto_finsetSum (Finset.univ) fun k (_ : k ∈ Finset.univ) => h2 k
      simpa using this
    have := ((tendsto_const_nhds (x := (2 : ℝ))).mul (hsum1.add
      (tendsto_const_nhds (x := ∑ k, ‖F₀ k x‖ ^ 2)))).sub hsum2
    have e : 4 * (∑ k, ‖F₀ k x‖ ^ 2) = 2 * ((∑ k, ‖F₀ k x‖ ^ 2) + ∑ k, ‖F₀ k x‖ ^ 2) - 0 := by
      ring
    rw [e, hgdef]
    exact this
  -- Fatou
  have hmeasg : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (g n x)) μ :=
    fun n => ENNReal.measurable_ofReal.comp_aemeasurable (hgI n).aestronglyMeasurable.aemeasurable
  have hfat := lintegral_liminf_le' (u := atTop) hmeasg
  have hG4 : Integrable (fun x => 4 * ∑ k, ‖F₀ k x‖ ^ 2) μ :=
    (integrable_finsetSum Finset.univ (fun k _ => hI0 k)).const_mul 4
  have hL : ∫⁻ x, liminf (fun n => ENNReal.ofReal (g n x)) atTop ∂μ = ENNReal.ofReal (4 * S₀) := by
    have e : ∀ x, liminf (fun n => ENNReal.ofReal (g n x)) atTop =
        ENNReal.ofReal (4 * ∑ k, ‖F₀ k x‖ ^ 2) := fun x =>
      (ENNReal.tendsto_ofReal (hlimg x)).liminf_eq
    simp only [e]
    rw [← ofReal_integral_eq_lintegral_ofReal hG4
      (Filter.Eventually.of_forall fun x => by positivity)]
    congr 1
    rw [integral_const_mul, integral_finsetSum Finset.univ (fun k _ => hI0 k), hS₀]
  -- the integrals of `g n`
  have hint : ∀ n, ∫ x, g n x ∂μ = 2 * S n + 2 * S₀ - A n := by
    intro n
    have hA : Integrable (fun x => ∑ k, ‖G n k x‖ ^ 2) μ :=
      integrable_finsetSum Finset.univ (fun k _ => hI n k)
    have hB : Integrable (fun x => ∑ k, ‖F₀ k x‖ ^ 2) μ :=
      integrable_finsetSum Finset.univ (fun k _ => hI0 k)
    have hC : Integrable (fun x => ∑ k, ‖G n k x - F₀ k x‖ ^ 2) μ :=
      integrable_finsetSum Finset.univ (fun k _ => hD n k)
    rw [hgdef]
    show ∫ x, (2 * ((∑ k, ‖G n k x‖ ^ 2) + ∑ k, ‖F₀ k x‖ ^ 2) -
      ∑ k, ‖G n k x - F₀ k x‖ ^ 2) ∂μ = _
    have hf : Integrable (fun x => 2 * ((∑ k, ‖G n k x‖ ^ 2) + ∑ k, ‖F₀ k x‖ ^ 2)) μ :=
      (hA.add hB).const_mul 2
    rw [integral_sub hf hC, integral_const_mul, integral_add hA hB,
      integral_finsetSum Finset.univ (fun k _ => hI n k),
      integral_finsetSum Finset.univ (fun k _ => hI0 k),
      integral_finsetSum Finset.univ (fun k _ => hD n k)]
    rw [hSdef, hS₀, hAdef]
    simp only
    ring
  have hR : (fun n => ∫⁻ x, ENNReal.ofReal (g n x) ∂μ) =
      fun n => ENNReal.ofReal (2 * S n + 2 * S₀ - A n) := by
    funext n
    rw [← hint n, ofReal_integral_eq_lintegral_ofReal (hgI n)
      (Filter.Eventually.of_forall fun x => hgnn n x)]
  have key : ENNReal.ofReal (4 * S₀) ≤
      liminf (fun n => ENNReal.ofReal (2 * S n + 2 * S₀ - A n)) atTop := by
    rw [← hR, ← hL]
    exact hfat
  -- real consequences
  have hA0 : ∀ n, 0 ≤ A n := by
    intro n
    rw [hAdef]
    exact Finset.sum_nonneg fun k _ => integral_nonneg fun x => by positivity
  have hlow : ∀ b, b < 4 * S₀ → ∀ᶠ n in atTop, b < 2 * S n + 2 * S₀ - A n := by
    intro b hb
    by_cases hb0 : b < 0
    · refine Eventually.of_forall fun n => ?_
      have := hgnn n
      have hsn : 0 ≤ 2 * S n + 2 * S₀ - A n := by
        rw [← hint n]
        exact integral_nonneg fun x => hgnn n x
      linarith
    · push_neg at hb0
      have hlt : ENNReal.ofReal b < ENNReal.ofReal (4 * S₀) :=
        (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hb
      have hev := eventually_lt_of_lt_liminf (lt_of_lt_of_le hlt key)
      filter_upwards [hev] with n hn
      by_contra hcn
      push_neg at hcn
      exact absurd hn (not_lt.2 (ENNReal.ofReal_le_ofReal hcn))
  have hTn : Tendsto (fun n => 2 * S n + 2 * S₀) atTop (𝓝 (4 * S₀)) := by
    have := (hS.const_mul 2).add_const (2 * S₀)
    rw [show 2 * S₀ + 2 * S₀ = 4 * S₀ by ring] at this
    exact this
  have hAto : Tendsto A atTop (𝓝 0) := by
    rw [tendsto_order]
    refine ⟨fun a ha => Eventually.of_forall fun n => lt_of_lt_of_le ha (hA0 n), ?_⟩
    intro e he
    have h1 : ∀ᶠ n in atTop, 2 * S n + 2 * S₀ < 4 * S₀ + e / 2 :=
      hTn.eventually (gt_mem_nhds (by linarith))
    have h2 := hlow (4 * S₀ - e / 2) (by linarith)
    filter_upwards [h1, h2] with n h1n h2n
    linarith
  intro k
  have hAk : ∀ n, ∫ x, ‖G n k x - F₀ k x‖ ^ 2 ∂μ ≤ A n := by
    intro n
    rw [hAdef]
    exact Finset.single_le_sum (f := fun j => ∫ x, ‖G n j x - F₀ j x‖ ^ 2 ∂μ)
      (fun j _ => integral_nonneg fun x => by positivity) (Finset.mem_univ k)
  have hint0 : Tendsto (fun n => ∫ x, ‖G n k x - F₀ k x‖ ^ 2 ∂μ) atTop (𝓝 0) :=
    squeeze_zero (fun n => integral_nonneg fun x => by positivity) hAk hAto
  have e : ∀ n, eLpNorm (G n k - F₀ k) 2 μ =
      ENNReal.ofReal ((∫ x, ‖G n k x - F₀ k x‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ)) := by
    intro n
    rw [((hG n k).sub (hF₀ k)).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp [Real.rpow_two]
  have hfin := ENNReal.tendsto_ofReal (hint0.rpow_const (p := 1 / 2) (Or.inr (by norm_num)))
  rw [Real.zero_rpow (by norm_num), ENNReal.ofReal_zero] at hfin
  exact hfin.congr (fun n => (e n).symm)

end L2EnergyAux

theorem l2StrongOfEnergy : UnforcedLeray.Short.IIIa.L2StrongOfEnergy := by
  intro μ l _ F F₀ hF hF₀ hpt hnorm k
  apply Filter.tendsto_of_seq_tendsto
  intro u hu
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hu.eventually hF)
  have hw : Tendsto (fun n => u (n + N)) atTop l := hu.comp (tendsto_add_atTop_nat N)
  have hwM : ∀ n k, MemLp (F (u (n + N)) k) 2 μ := fun n => hN (n + N) (by omega)
  have hcore := L2EnergyAux.core_seq μ (fun n => F (u (n + N))) F₀ hwM hF₀
    (fun k x => (hpt k x).comp hw) (hnorm.comp hw) k
  exact (tendsto_add_atTop_iff_nat N).1 hcore

end UnforcedLeray.Short.IIIa
