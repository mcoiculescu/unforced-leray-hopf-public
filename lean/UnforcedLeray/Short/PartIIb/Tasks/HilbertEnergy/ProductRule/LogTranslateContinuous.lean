import UnforcedLeray.Short.PartIIb.Sub.T15_2

/-!
# Part II-b, task `PartII-b:T15/2/7`: continuity of `t`-translation in `L²(logMeas c)`

Source of record: `the November 2 reference manuscript`, lines 1975-1979 (the weak
product rule in the `H_2` measure, log chart `s = e^t`).

This file proves `LogTranslateContinuous` (`Sub/T15_2.lean`) with no extra hypotheses.

Strategy (`ε/3`): `logMeas c` is a locally finite Borel measure on `Coord`, so compactly supported
continuous functions are dense in `L²` (`MemLp.exists_hasCompactSupport_eLpNorm_sub_le`). The
`t`-translation preserves `logMeas c`, so `L²`-distances of translates are translation invariant.
For a continuous compactly supported `g`, uniform continuity gives a uniform sup bound on
`g(· + σ) - g`, and this difference vanishes off a fixed compact set of finite `logMeas c`-measure.

Every auxiliary declaration is prefixed `logTC_` to avoid clashes.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIb

/-! ## Measure facts about `logMeas c` -/

/-- The normalized cell measure is `s`-finite (instance search does not unfold `Cyl.avgμ`). -/
instance logTC_sFinite_avgμ (c : ℝ) : SFinite (Cyl.avgμ c) := by
  unfold Cyl.avgμ
  infer_instance

/-- The normalized cell measure is finite on compact sets. -/
instance logTC_finiteOnCompacts_avgμ (c : ℝ) : IsFiniteMeasureOnCompacts (Cyl.avgμ c) := by
  unfold Cyl.avgμ Cyl.cellμ
  exact IsFiniteMeasureOnCompacts.smul _ ENNReal.ofReal_ne_top

/-- `logMeas c` is finite on compact sets. -/
instance logTC_finiteOnCompacts (c : ℝ) : IsFiniteMeasureOnCompacts (logMeas c) := by
  unfold logMeas
  infer_instance

/-- `logMeas c` is a regular measure (locally finite on a σ-compact metrizable space). -/
instance logTC_regular (c : ℝ) : (logMeas c).Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

/-- The translation `t ↦ t + σ` on the logarithmic chart preserves `logMeas c`. -/
theorem logTC_measurePreserving (c σ : ℝ) :
    MeasurePreserving (fun x : Coord => (x.1 + σ, x.2)) (logMeas c) (logMeas c) := by
  unfold logMeas
  exact (measurePreserving_add_right volume σ).prod (MeasurePreserving.id _)

/-- `t`-translation is continuous on `Coord`. -/
theorem logTC_continuous_shift (σ : ℝ) : Continuous (fun x : Coord => (x.1 + σ, x.2)) := by
  fun_prop

/-! ## Compact sets and translation distances -/

/-- The set `{(x.1 + t, x.2) : x ∈ A, t ∈ [-1, 1]}`. -/
def logTC_K (A : Set Coord) : Set Coord :=
  (fun p : Coord × ℝ => (p.1.1 + p.2, p.1.2)) '' (A ×ˢ Icc (-1 : ℝ) 1)

/-- The set `logTC_K A` is compact when `A` is. -/
theorem logTC_K_isCompact {A : Set Coord} (hA : IsCompact A) : IsCompact (logTC_K A) := by
  unfold logTC_K
  exact (hA.prod (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1))).image (by fun_prop)

/-- The distance of a `t`-translate from its base point. -/
theorem logTC_dist_shift (σ : ℝ) (x : Coord) : dist ((x.1 + σ, x.2) : Coord) x = |σ| := by
  rw [Prod.dist_eq, Real.dist_eq, dist_self, add_sub_cancel_left]
  exact max_eq_left (abs_nonneg σ)

/-- Off `logTC_K (tsupport g)`, the difference `g(· + σ) - g` vanishes for `|σ| ≤ 1`. -/
theorem logTC_supp (g : Coord → ℂ) {σ : ℝ} (hσ : |σ| ≤ 1) (x : Coord)
    (hx : x ∉ logTC_K (tsupport g)) : g (x.1 + σ, x.2) - g x = 0 := by
  by_contra hne
  have hor : g x ≠ 0 ∨ g (x.1 + σ, x.2) ≠ 0 := by
    by_contra hcon
    simp only [not_or, not_not] at hcon
    exact hne (by simp [hcon.1, hcon.2])
  have hσ' := abs_le.1 hσ
  rcases hor with h1 | h1
  · apply hx
    exact ⟨(x, 0), Set.mk_mem_prod (subset_tsupport g (Function.mem_support.2 h1))
      (Set.mem_Icc.2 ⟨by norm_num, by norm_num⟩), by simp⟩
  · apply hx
    exact ⟨((x.1 + σ, x.2), -σ),
      Set.mk_mem_prod (subset_tsupport g (Function.mem_support.2 h1))
        (Set.mem_Icc.2 ⟨by linarith [hσ'.2], by linarith [hσ'.1]⟩), by simp⟩

/-! ## Limit criterion and the continuous case -/

/-- A bound of the form `D σ ≤ ‖s‖ₑ * M` for all small `s > 0`, with `M < ∞`, forces
`D σ → 0`. -/
theorem logTC_tendsto_of_bound {D : ℝ → ℝ≥0∞} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (h : ∀ s : ℝ, 0 < s → ∀ᶠ σ in 𝓝 (0 : ℝ), D σ ≤ ‖s‖ₑ * M) :
    Tendsto D (𝓝 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hlim : Tendsto (fun s : ℝ => ‖s‖ₑ * M) (𝓝 0) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => ‖s‖ₑ) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_enorm.tendsto (0 : ℝ))
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hM)
  obtain ⟨s, hs0, hs⟩ : ∃ s : ℝ, 0 < s ∧ ‖s‖ₑ * M < ε := by
    have hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
    have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), ‖s‖ₑ * M < ε :=
      (hlim.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hε)
    obtain ⟨s, hs1, hs2⟩ := (hpos.and hsmall).exists
    exact ⟨s, hs1, hs2⟩
  filter_upwards [h s hs0] with σ hσ
  exact hσ.trans hs.le

/-- The continuous compactly supported case: `‖g(· + σ) - g‖_{L²(logMeas c)} → 0` as `σ → 0`. -/
theorem logTC_cont (c : ℝ) (g : Coord → ℂ) (hg : HasCompactSupport g) (hgc : Continuous g) :
    Tendsto (fun σ : ℝ => eLpNorm (fun x : Coord => g (x.1 + σ, x.2) - g x) 2 (logMeas c))
      (𝓝 0) (𝓝 0) := by
  have hKc : IsCompact (logTC_K (tsupport g)) := logTC_K_isCompact hg.isCompact
  have hKm : MeasurableSet (logTC_K (tsupport g)) := hKc.isClosed.measurableSet
  have hμK : logMeas c (logTC_K (tsupport g)) ≠ ⊤ := hKc.measure_lt_top.ne
  have hM : logMeas c (logTC_K (tsupport g)) ^ (1 / (2 : ℝ≥0∞).toReal) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) hμK
  have hu : UniformContinuous g := hg.uniformContinuous_of_continuous hgc
  apply logTC_tendsto_of_bound hM
  intro s hs
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuous_iff.1 hu s hs
  have habs : Tendsto (fun σ : ℝ => |σ|) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs.tendsto (0 : ℝ))
  filter_upwards [habs.eventually (gt_mem_nhds hδ), habs.eventually (gt_mem_nhds one_pos)]
    with σ hσδ hσ1
  have hpt : ∀ x : Coord,
      ‖g (x.1 + σ, x.2) - g x‖ ≤ (logTC_K (tsupport g)).indicator (fun _ => s) x := by
    intro x
    by_cases hx : x ∈ logTC_K (tsupport g)
    · rw [Set.indicator_of_mem hx]
      have hd : dist ((x.1 + σ, x.2) : Coord) x < δ := by
        rw [logTC_dist_shift]
        exact hσδ
      have hlt := hδg hd
      rw [dist_eq_norm] at hlt
      exact hlt.le
    · rw [Set.indicator_of_notMem hx, logTC_supp g hσ1.le x hx]
      simp
  calc eLpNorm (fun x : Coord => g (x.1 + σ, x.2) - g x) 2 (logMeas c)
      ≤ eLpNorm ((logTC_K (tsupport g)).indicator (fun _ => s)) 2 (logMeas c) :=
        eLpNorm_mono_real hpt
    _ = ‖s‖ₑ * logMeas c (logTC_K (tsupport g)) ^ (1 / (2 : ℝ≥0∞).toReal) :=
        eLpNorm_indicator_const hKm two_ne_zero (by norm_num)

/-! ## Squared `L²` norms -/

/-- The lintegral of the squared enorm is the square of the `L²` norm. -/
theorem logTC_sq (c : ℝ) (h : Coord → ℂ) :
    ∫⁻ x, ‖h x‖ₑ ^ 2 ∂(logMeas c) = eLpNorm h 2 (logMeas c) ^ 2 := by
  have h1 := eLpNorm_nnreal_pow_eq_lintegral (μ := logMeas c) (f := h) (p := 2) two_ne_zero
  have e2 : ((2 : ℝ≥0) : ℝ≥0∞) = 2 := by simp
  have e3 : ((2 : ℝ≥0) : ℝ) = 2 := by simp
  rw [e2, e3] at h1
  simp only [ENNReal.rpow_two] at h1
  exact h1.symm

/-! ## The main theorem -/

/-- **Leaf `PartII-b:T15/2/7`** (continuity of `t`-translation in `L²(logMeas c)`). -/
theorem logTranslateContinuous : LogTranslateContinuous := by
  unfold LogTranslateContinuous
  intro c f _hc hf
  have hrw : (fun σ : ℝ => ∫⁻ x, ‖f (x.1 + σ, x.2) - f x‖ₑ ^ 2 ∂(logMeas c)) =
      fun σ : ℝ => eLpNorm (fun x : Coord => f (x.1 + σ, x.2) - f x) 2 (logMeas c) ^ 2 :=
    funext fun σ => logTC_sq c (fun x : Coord => f (x.1 + σ, x.2) - f x)
  rw [hrw]
  have hfm : AEStronglyMeasurable f (logMeas c) := hf.aestronglyMeasurable
  have hE : Tendsto (fun σ : ℝ => eLpNorm (fun x : Coord => f (x.1 + σ, x.2) - f x) 2 (logMeas c))
      (𝓝 0) (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨e, hepos, hesum⟩ : ∃ e : ℝ≥0∞, 0 < e ∧ e + e + e ≤ ε := by
      refine ⟨ε / 3, ENNReal.div_pos hε.ne' (by norm_num), ?_⟩
      rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same]
      exact ENNReal.div_le_of_le_mul (le_of_eq (by ring))
    obtain ⟨g, hg_supp, hfg, hg_cont, hg_mem⟩ :=
      hf.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) hepos.ne'
    have hfgm : AEStronglyMeasurable (f - g) (logMeas c) := (hf.sub hg_mem).aestronglyMeasurable
    have hD0 := logTC_cont c g hg_supp hg_cont
    have hev := ENNReal.tendsto_nhds_zero.1 hD0 e hepos
    filter_upwards [hev] with σ hσ
    have hA : AEStronglyMeasurable (fun x : Coord => f (x.1 + σ, x.2) - g (x.1 + σ, x.2))
        (logMeas c) :=
      hfgm.comp_quasiMeasurePreserving (logTC_measurePreserving c σ).quasiMeasurePreserving
    have hB : AEStronglyMeasurable (fun x : Coord => g (x.1 + σ, x.2) - g x) (logMeas c) :=
      ((hg_cont.comp (logTC_continuous_shift σ)).sub hg_cont).aestronglyMeasurable
    have hC : AEStronglyMeasurable (fun x : Coord => g x - f x) (logMeas c) :=
      hg_cont.aestronglyMeasurable.sub hfm
    have hdec : (fun x : Coord => f (x.1 + σ, x.2) - f x) =
        ((fun x : Coord => f (x.1 + σ, x.2) - g (x.1 + σ, x.2)) +
          (fun x : Coord => g (x.1 + σ, x.2) - g x)) + (fun x : Coord => g x - f x) := by
      funext x
      simp only [Pi.add_apply]
      ring
    have hF : eLpNorm (fun x : Coord => f (x.1 + σ, x.2) - g (x.1 + σ, x.2)) 2 (logMeas c) ≤ e := by
      have h := eLpNorm_comp_measurePreserving (p := 2) hfgm (logTC_measurePreserving c σ)
      exact h.le.trans hfg
    have hH : eLpNorm (fun x : Coord => g x - f x) 2 (logMeas c) ≤ e := by
      show eLpNorm (g - f) 2 (logMeas c) ≤ e
      rw [← eLpNorm_sub_comm]
      exact hfg
    rw [hdec]
    refine (eLpNorm_add_le (hA.add hB) hC one_le_two).trans ?_
    refine (add_le_add (eLpNorm_add_le hA hB one_le_two) le_rfl).trans ?_
    exact (add_le_add (add_le_add hF hσ) hH).trans hesum
  have hpow : Tendsto (fun σ : ℝ => eLpNorm (fun x : Coord => f (x.1 + σ, x.2) - f x) 2
      (logMeas c) ^ 2) (𝓝 0) (𝓝 ((0 : ℝ≥0∞) ^ 2)) :=
    ((ENNReal.continuous_pow 2).tendsto (0 : ℝ≥0∞)).comp hE
  rw [show (0 : ℝ≥0∞) ^ 2 = 0 by norm_num] at hpow
  exact hpow

end UnforcedLeray.Short.IIb
