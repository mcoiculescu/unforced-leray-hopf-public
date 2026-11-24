import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_1_of
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceApprox.Truncation

/-!
# `sfdTrunc`: truncation of `h ∈ Hsp c` to a compact box (source 1678)

Source of record `the November 2 reference manuscript` 1678, 1684-1689.

For `n : ℕ` the box `truncBox c n` is `s ∈ [1/(n+1), n+1]`, `q ∈ [-c/2 + 1/(n+1), c/2 - 1/(n+1)]`,
`|η| ≤ n+1`. The truncation `h' = 1_{truncBox c n} · h` satisfies `‖h - h'‖² = ∫⁻ 1_{complement} |h|²`,
which tends to `0` by dominated convergence, since the boxes exhaust the set where `s > 0`
and `|q| < c/2` (a.e. for `ageμ c a`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- The truncation box with index `n`. -/
def truncBox (c : ℝ) (n : ℕ) : Set (ℝ × (ℝ × ℝ)) :=
  Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) ×ˢ
    (Icc (-(c / 2) + 1 / ((n : ℝ) + 1)) (c / 2 - 1 / ((n : ℝ) + 1)) ×ˢ
      Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1))

theorem truncBox_measurableSet (c : ℝ) (n : ℕ) : MeasurableSet (truncBox c n) :=
  measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)

/-- Eventually `1/(n+1) < x` for `x > 0`. -/
theorem eventually_one_div_lt {x : ℝ} (hx : 0 < x) :
    ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < x :=
  (tendsto_order.1 tendsto_one_div_add_atTop_nhds_zero_nat).2 x hx

/-- Pointwise, every point with `s > 0` and `|q| < c/2` lies in the box eventually. -/
theorem eventually_mem_truncBox {c : ℝ} (p : ℝ × (ℝ × ℝ)) (hs : 0 < p.1)
    (hq : |p.2.1| < c / 2) : ∀ᶠ n : ℕ in atTop, p ∈ truncBox c n := by
  have hq' := abs_lt.1 hq
  have h1 := eventually_one_div_lt hs
  have h2 := eventually_one_div_lt (show 0 < p.2.1 + c / 2 by linarith)
  have h3 := eventually_one_div_lt (show 0 < c / 2 - p.2.1 by linarith)
  have h4 : ∀ᶠ n : ℕ in atTop, p.1 ≤ (n : ℝ) + 1 := by
    filter_upwards [eventually_ge_atTop (⌈p.1⌉₊)] with n hn
    have : p.1 ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    linarith
  have h5 : ∀ᶠ n : ℕ in atTop, |p.2.2| ≤ (n : ℝ) + 1 := by
    filter_upwards [eventually_ge_atTop (⌈|p.2.2|⌉₊)] with n hn
    have : |p.2.2| ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    linarith
  filter_upwards [h1, h2, h3, h4, h5] with n e1 e2 e3 e4 e5
  have hη := abs_le.1 e5
  refine ⟨⟨e1.le, e4⟩, ⟨?_, ?_⟩, hη.1, hη.2⟩
  · have : 1 / ((n : ℝ) + 1) < p.2.1 + c / 2 := e2
    linarith
  · have : 1 / ((n : ℝ) + 1) < c / 2 - p.2.1 := e3
    linarith

/-- The `ageμ`-a.e. support facts: `s > 0` and `|q| < c/2`. -/
theorem ae_s_pos_and_q (c a : ℝ) :
    ∀ᵐ p ∂(ageμ c a), 0 < p.1 ∧ |p.2.1| < c / 2 :=
  UnforcedLeray.Short.IIIa.niceTr_ae_good c a

theorem sfdTrunc : SFDTrunc := by
  intro c hc h ε hε
  set μ := ageμ c (-3 / 2) with hμ
  set G : ℝ × (ℝ × ℝ) → ℝ≥0∞ := fun p => ‖(h : ℝ × (ℝ × ℝ) → EuclideanSpace ℝ (Fin 2)) p‖ₑ ^ (2 : ℝ)
    with hG
  have hgm : AEMeasurable (fun p => ‖(h : ℝ × (ℝ × ℝ) → EuclideanSpace ℝ (Fin 2)) p‖ₑ) μ :=
    (Lp.aestronglyMeasurable h).aemeasurable.enorm
  have hGm : AEMeasurable G μ := hgm.pow_const (2 : ℝ)
  have hfin : ∫⁻ p, G p ∂μ ≠ ⊤ := by
    have hmem := (Lp.memLp h)
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := (2 : ℝ≥0∞)) (μ := μ)
      (by norm_num) (by simp) hmem.eLpNorm_lt_top
    simpa [hG, ENNReal.toReal_ofNat] using this.ne
  -- dominated convergence for the tails
  have hlim : ∀ᵐ p ∂μ, Tendsto (fun n : ℕ => (truncBox c n)ᶜ.indicator G p) atTop (𝓝 0) := by
    filter_upwards [ae_s_pos_and_q c (-3 / 2)] with p hp
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_mem_truncBox p hp.1 hp.2] with n hn
    simp [Set.indicator_apply, hn]
  have hTend : Tendsto (fun n : ℕ => ∫⁻ p, (truncBox c n)ᶜ.indicator G p ∂μ) atTop (𝓝 0) := by
    have key := tendsto_lintegral_filter_of_dominated_convergence' (l := atTop)
      (F := fun n : ℕ => (truncBox c n)ᶜ.indicator G) (f := fun _ => 0) G
      (Eventually.of_forall fun n => hGm.indicator (truncBox_measurableSet c n).compl)
      (Eventually.of_forall fun n => Eventually.of_forall fun p => Set.indicator_le_self _ _ p)
      hfin hlim
    simpa using key
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (ε ^ 2) := ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨n, hn⟩ := (hTend.eventually (gt_mem_nhds hpos)).exists
  set B := truncBox c n with hB
  set h' : Lp (EuclideanSpace ℝ (Fin 2)) 2 μ :=
    ((Lp.memLp h).indicator (truncBox_measurableSet c n)).toLp _ with hh'
  have hcoe : (h' : ℝ × (ℝ × ℝ) → EuclideanSpace ℝ (Fin 2)) =ᵐ[μ]
      B.indicator (h : ℝ × (ℝ × ℝ) → EuclideanSpace ℝ (Fin 2)) :=
    MemLp.coeFn_toLp _
  refine ⟨1 / ((n : ℝ) + 1), (n : ℝ) + 1, -(c / 2) + 1 / ((n : ℝ) + 1),
    c / 2 - 1 / ((n : ℝ) + 1), (n : ℝ) + 1, h', ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · filter_upwards [hcoe] with p hp hne
    by_cases hpB : p ∈ B
    · exact ⟨hpB.1, hpB.2.1, abs_le.2 hpB.2.2⟩
    · exact (hne (by funext i; simp [NearInst.velC, hp, Set.indicator_of_notMem hpB])).elim
  · -- the difference is the tail indicator
    have hdiff : (⇑(h - h') : ℝ × (ℝ × ℝ) → EuclideanSpace ℝ (Fin 2)) =ᵐ[μ]
        Bᶜ.indicator (h : ℝ × (ℝ × ℝ) → EuclideanSpace ℝ (Fin 2)) := by
      filter_upwards [Lp.coeFn_sub h h', hcoe] with p hp1 hp2
      rw [hp1, Pi.sub_apply, hp2]
      by_cases hpB : p ∈ B <;> simp [Set.indicator_apply, hpB]
    have hlt : eLpNorm (Bᶜ.indicator (h : ℝ × (ℝ × ℝ) → EuclideanSpace ℝ (Fin 2))) 2 μ <
        ENNReal.ofReal ε := by
      rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by simp)]
      simp only [ENNReal.toReal_ofNat]
      have hint : ∫⁻ p, ‖Bᶜ.indicator (h : ℝ × (ℝ × ℝ) → EuclideanSpace ℝ (Fin 2)) p‖ₑ ^ (2 : ℝ)
          ∂μ = ∫⁻ p, Bᶜ.indicator G p ∂μ := by
        refine lintegral_congr fun p => ?_
        by_cases hpB : p ∈ B <;> simp [Set.indicator_apply, hG, hpB]
      rw [hint]
      calc (∫⁻ p, Bᶜ.indicator G p ∂μ) ^ (1 / (2 : ℝ))
          < (ENNReal.ofReal (ε ^ 2)) ^ (1 / (2 : ℝ)) := ENNReal.rpow_lt_rpow hn (by norm_num)
        _ = ENNReal.ofReal ε := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
            ← Real.sqrt_eq_rpow, Real.sqrt_sq hε.le]
    have hnorm : ‖h - h'‖ = (eLpNorm (Bᶜ.indicator (h : ℝ × (ℝ × ℝ) → EuclideanSpace ℝ (Fin 2))) 2 μ).toReal := by
      rw [Lp.norm_def, eLpNorm_congr_ae hdiff]
    rw [hnorm]
    exact ENNReal.toReal_lt_of_lt_ofReal hlt

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
