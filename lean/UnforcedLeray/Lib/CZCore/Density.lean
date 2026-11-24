import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Simultaneous density of compactly supported functions in `L^p ∩ L^q`

Support file for the INF01 Level 1 Calderón–Zygmund core (scoping note

R5 of §6: "the density step needs approximation in `L¹` and `L²` simultaneously").

On a finite-dimensional real normed space with an additive Haar measure:

* `tendsto_eLpNorm_indicator_compl_closedBall`: the `L^p` tail of an `L^p` function outside
  `closedBall 0 n` tends to `0` (dominated convergence).
* `exists_continuous_eLpNorm_sub_le_of_le`: a function in `L^p ∩ L^q` (`1 ≤ p ≤ q < ∞`) is
  approximated in both norms at once by one continuous compactly supported function: cut off
  to a ball, approximate in `L^q` (Mathlib), multiply by a bump which is `1` on the ball, and use
  `‖·‖_p ≤ |U|^{1/p-1/q} ‖·‖_q` on the bounded set `U`.
* `exists_contDiff_eLpNorm_sub_le_of_le`: the same with a smooth compactly supported function
  (uniform smooth approximation with support control, `Continuous.exists_contDiff_approx`).
* `exists_contDiff_eLpNorm_sub_le_two`: the symmetric form (no order between `p` and `q`).
-/

noncomputable section

open MeasureTheory Filter Metric Set
open scoped ENNReal Topology ContDiff

namespace UnforcedLeray.CZ

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
/-- The `L^p` tail of an `L^p` function outside `closedBall 0 n` tends to `0`. -/
theorem tendsto_eLpNorm_indicator_compl_closedBall {p : ℝ≥0∞} (hp : p ≠ ⊤) {f : E → ℝ}
    (hf : MemLp f p μ) :
    Tendsto (fun n : ℕ => eLpNorm ((closedBall (0 : E) n)ᶜ.indicator f) p μ) atTop (𝓝 0) := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp]
  have hlim : Tendsto (fun n : ℕ => ∫⁻ x, ‖(closedBall (0 : E) n)ᶜ.indicator f x‖ₑ ^ p.toReal ∂μ)
      atTop (𝓝 (∫⁻ _x, (0 : ℝ≥0∞) ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence' (fun x => ‖f x‖ₑ ^ p.toReal)
      (fun n => ?_) (fun n => ?_) ?_ ?_
    · exact ((hf.1.indicator measurableSet_closedBall.compl).enorm.pow_const _)
    · refine Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ (closedBall (0 : E) n)ᶜ
      · simp [indicator_of_mem hx]
      · simp [indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hpr]
    · exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp hf.2).ne
    · refine Eventually.of_forall fun x => tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈‖x‖⌉₊] with n hn
      have hx : x ∈ closedBall (0 : E) n := by
        rw [mem_closedBall, dist_zero_right]
        exact (Nat.le_ceil _).trans (by exact_mod_cast hn)
      simp [indicator_of_notMem (notMem_compl_iff.2 hx), ENNReal.zero_rpow_of_pos hpr]
  rw [lintegral_zero] at hlim
  have h1 := (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0
  rw [ENNReal.zero_rpow_of_pos (by positivity)] at h1
  exact h1.comp hlim

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- Hölder on a set of finite measure: if `h` vanishes off `U`, then
`‖h‖_p ≤ ‖h‖_q * μ(U)^{1/p - 1/q}` for `p ≤ q`. -/
theorem eLpNorm_le_of_support_subset {p q : ℝ≥0∞} (hpq : p ≤ q) {h : E → ℝ}
    (hh : AEStronglyMeasurable h μ) {U : Set E}
    (hsupp : Function.support h ⊆ U) :
    eLpNorm h p μ ≤ eLpNorm h q μ * μ U ^ (1 / p.toReal - 1 / q.toReal) := by
  rw [← eLpNorm_restrict_eq_of_support_subset hsupp,
    ← eLpNorm_restrict_eq_of_support_subset (p := q) hsupp]
  have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict U) hpq hh.restrict
  rwa [Measure.restrict_apply_univ] at this

/-- Small `δ` with `δ * M ≤ ε` for a finite `M`. -/
private theorem eventually_ofReal_mul_le {M ε : ℝ≥0∞} (hM : M ≠ ⊤) (hε : ε ≠ 0) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), ENNReal.ofReal δ * M ≤ ε := by
  have h : Tendsto (fun δ : ℝ => ENNReal.ofReal δ * M) (𝓝[>] (0 : ℝ)) (𝓝 (0 * M)) := by
    refine ENNReal.Tendsto.mul_const ?_ (Or.inr hM)
    have := (ENNReal.continuous_ofReal.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  rw [zero_mul] at h
  exact (h.eventually (ge_mem_nhds (pos_iff_ne_zero.2 hε)))

/-- **Simultaneous approximation, continuous version.** A function in `L^p ∩ L^q`,
`1 ≤ p ≤ q < ∞`, is approximated in both norms at once by a continuous compactly supported
function. -/
theorem exists_continuous_eLpNorm_sub_le_of_le {p q : ℝ≥0∞} (hp1 : 1 ≤ p) (hpq : p ≤ q)
    (hq : q ≠ ⊤) {f : E → ℝ} (hfp : MemLp f p μ) (hfq : MemLp f q μ) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) :
    ∃ g : E → ℝ, Continuous g ∧ HasCompactSupport g ∧ eLpNorm (f - g) p μ ≤ ε ∧
      eLpNorm (f - g) q μ ≤ ε := by
  have hp : p ≠ ⊤ := ne_top_of_le_ne_top hq hpq
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε).ne'
  -- tails outside a large ball
  have hev : ∀ᶠ n : ℕ in atTop,
      eLpNorm ((closedBall (0 : E) n)ᶜ.indicator f) p μ ≤ ε / 2 ∧
      eLpNorm ((closedBall (0 : E) n)ᶜ.indicator f) q μ ≤ ε / 2 :=
    ((tendsto_eLpNorm_indicator_compl_closedBall hp hfp).eventually
        (ge_mem_nhds (pos_iff_ne_zero.2 hε2))).and
      ((tendsto_eLpNorm_indicator_compl_closedBall hq hfq).eventually
        (ge_mem_nhds (pos_iff_ne_zero.2 hε2)))
  obtain ⟨n, hnp, hnq⟩ := hev.exists
  set R : ℝ := (n : ℝ) with hR
  have hR0 : 0 ≤ R := Nat.cast_nonneg n
  set fR : E → ℝ := (closedBall (0 : E) R).indicator f with hfR
  have hfRq : MemLp fR q μ := hfq.indicator measurableSet_closedBall
  have hsub : f - fR = (closedBall (0 : E) R)ᶜ.indicator f := by
    rw [hfR, indicator_compl]
  -- the bounded set `U` and the comparison constant
  set U : Set E := ball (0 : E) (R + 2) with hU
  have hUfin : μ U ≠ ⊤ := measure_ball_lt_top.ne
  set M : ℝ≥0∞ := μ U ^ (1 / p.toReal - 1 / q.toReal) with hM
  have hexp : 0 ≤ 1 / p.toReal - 1 / q.toReal := by
    rcases eq_or_ne p 0 with h0 | h0
    · exact absurd h0 (ne_of_gt (lt_of_lt_of_le one_pos hp1))
    have hp' : 0 < p.toReal := ENNReal.toReal_pos h0 hp
    have : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq hpq
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le hp' this
  have hMfin : M ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hexp hUfin
  obtain ⟨δ, hδM, hδ0⟩ := ((eventually_ofReal_mul_le hMfin hε2).and
    ((eventually_ofReal_mul_le ENNReal.one_ne_top hε2).and self_mem_nhdsWithin)).exists
  obtain ⟨hδ1, hδpos⟩ := hδ0
  rw [mul_one] at hδ1
  have hδne : ENNReal.ofReal δ ≠ 0 := by simpa using hδpos
  obtain ⟨g₀, hg₀c, hg₀e, hg₀cont, -⟩ :=
    hfRq.exists_hasCompactSupport_eLpNorm_sub_le hq hδne
  -- the bump
  let χ : ContDiffBump (0 : E) := ⟨R + 1, R + 2, by linarith, by linarith⟩
  refine ⟨fun x => χ x * g₀ x, χ.continuous.mul hg₀cont, hg₀c.mul_left, ?_⟩
  have hχ1 : ∀ x, χ x * fR x = fR x := by
    intro x
    by_cases hx : x ∈ closedBall (0 : E) R
    · rw [χ.one_of_mem_closedBall (mem_closedBall.2 ((mem_closedBall.1 hx).trans
        (by simp [χ]))), one_mul]
    · simp [hfR, indicator_of_notMem hx]
  have heq : fR - (fun x => χ x * g₀ x) = fun x => χ x * (fR x - g₀ x) := by
    funext x; simp only [Pi.sub_apply]; rw [mul_sub, hχ1]
  have hmeasR : AEStronglyMeasurable (fR - fun x => χ x * g₀ x) μ :=
    hfRq.1.sub (χ.continuous.mul hg₀cont).aestronglyMeasurable
  have hq_bd : eLpNorm (fR - fun x => χ x * g₀ x) q μ ≤ ENNReal.ofReal δ := by
    refine le_trans (eLpNorm_mono fun x => ?_) hg₀e
    rw [heq, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, Pi.sub_apply]
    exact mul_le_of_le_one_left (abs_nonneg _) (by rw [abs_of_nonneg (χ.nonneg)]; exact χ.le_one)
  have hsuppU : Function.support (fR - fun x => χ x * g₀ x) ⊆ U := by
    intro x hx
    rw [heq] at hx
    have : χ x ≠ 0 := left_ne_zero_of_mul hx
    have hx' : x ∈ Function.support χ := this
    rwa [χ.support_eq] at hx'
  have hp_bd : eLpNorm (fR - fun x => χ x * g₀ x) p μ ≤ ε / 2 :=
    (eLpNorm_le_of_support_subset hpq hmeasR hsuppU).trans
      ((mul_le_mul_left hq_bd _).trans hδM)
  have hdecomp : f - (fun x => χ x * g₀ x) = (f - fR) + (fR - fun x => χ x * g₀ x) := by
    abel
  have hmeas1 : AEStronglyMeasurable (f - fR) μ :=
    hfp.1.sub (hfp.1.indicator measurableSet_closedBall)
  constructor
  · rw [hdecomp]
    refine (eLpNorm_add_le hmeas1 hmeasR hp1).trans ?_
    rw [hsub, ← ENNReal.add_halves ε]
    exact add_le_add hnp hp_bd
  · rw [hdecomp]
    refine (eLpNorm_add_le hmeas1 hmeasR (hp1.trans hpq)).trans ?_
    rw [hsub, ← ENNReal.add_halves ε]
    exact add_le_add hnq (hq_bd.trans hδ1)

/-- **Simultaneous approximation, smooth version.** A function in `L^p ∩ L^q`,
`1 ≤ p ≤ q < ∞`, is approximated in both norms at once by a smooth compactly supported
function. -/
theorem exists_contDiff_eLpNorm_sub_le_of_le {p q : ℝ≥0∞} (hp1 : 1 ≤ p) (hpq : p ≤ q)
    (hq : q ≠ ⊤) {f : E → ℝ} (hfp : MemLp f p μ) (hfq : MemLp f q μ) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ eLpNorm (f - g) p μ ≤ ε ∧
      eLpNorm (f - g) q μ ≤ ε := by
  have hp : p ≠ ⊤ := ne_top_of_le_ne_top hq hpq
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε).ne'
  obtain ⟨g₁, hg₁c, hg₁s, hg₁p, hg₁q⟩ :=
    exists_continuous_eLpNorm_sub_le_of_le (μ := μ) hp1 hpq hq hfp hfq hε2
  set K := tsupport g₁
  have hKfin : μ K ≠ ⊤ := hg₁s.measure_lt_top.ne
  obtain ⟨η, hη⟩ := ((eventually_ofReal_mul_le
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hKfin : μ K ^ (1 / p.toReal) ≠ ⊤) hε2).and
    ((eventually_ofReal_mul_le
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hKfin : μ K ^ (1 / q.toReal) ≠ ⊤) hε2).and
      self_mem_nhdsWithin)).exists
  obtain ⟨hηp, hηq, hηpos⟩ := hη
  have hηpos' : (0 : ℝ) < η := hηpos
  obtain ⟨g, hgc, hgd, hgs⟩ := hg₁c.exists_contDiff_approx (n := ⊤) (ε := fun _ => η)
    continuous_const (fun _ => hηpos')
  refine ⟨g, hgc, hg₁s.mono hgs, ?_, ?_⟩
  all_goals
    have hdecomp : f - g = (f - g₁) + (g₁ - g) := by abel
    rw [hdecomp, ← ENNReal.add_halves ε]
  · refine (eLpNorm_add_le (hfp.1.sub hg₁c.aestronglyMeasurable)
      (hg₁c.aestronglyMeasurable.sub hgc.continuous.aestronglyMeasurable) hp1).trans
      (add_le_add hg₁p ?_)
    refine (eLpNorm_sub_le_of_dist_bdd μ hp (isClosed_tsupport g₁).measurableSet
      hηpos'.le (fun x => ?_) (subset_tsupport g₁) (hgs.trans (subset_tsupport g₁))).trans hηp
    rw [dist_comm]; exact (hgd x).le
  · refine (eLpNorm_add_le (hfq.1.sub hg₁c.aestronglyMeasurable)
      (hg₁c.aestronglyMeasurable.sub hgc.continuous.aestronglyMeasurable) (hp1.trans hpq)).trans
      (add_le_add hg₁q ?_)
    refine (eLpNorm_sub_le_of_dist_bdd μ hq (isClosed_tsupport g₁).measurableSet
      hηpos'.le (fun x => ?_) (subset_tsupport g₁) (hgs.trans (subset_tsupport g₁))).trans hηq
    rw [dist_comm]; exact (hgd x).le

/-- **Simultaneous smooth approximation, symmetric form.** For `1 ≤ p, q < ∞` and
`f ∈ L^p ∩ L^q`, there is a smooth compactly supported `g` with `‖f - g‖_p ≤ ε` and
`‖f - g‖_q ≤ ε`. -/
theorem exists_contDiff_eLpNorm_sub_le_two {p q : ℝ≥0∞} (hp1 : 1 ≤ p) (hq1 : 1 ≤ q)
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) {f : E → ℝ} (hfp : MemLp f p μ) (hfq : MemLp f q μ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ eLpNorm (f - g) p μ ≤ ε ∧
      eLpNorm (f - g) q μ ≤ ε := by
  rcases le_total p q with hpq | hqp
  · exact exists_contDiff_eLpNorm_sub_le_of_le hp1 hpq hq hfp hfq hε
  · obtain ⟨g, h1, h2, h3, h4⟩ := exists_contDiff_eLpNorm_sub_le_of_le hq1 hqp hp hfq hfp hε
    exact ⟨g, h1, h2, h4, h3⟩

/-- **Simultaneous continuous approximation, symmetric form.** -/
theorem exists_continuous_eLpNorm_sub_le_two {p q : ℝ≥0∞} (hp1 : 1 ≤ p) (hq1 : 1 ≤ q)
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) {f : E → ℝ} (hfp : MemLp f p μ) (hfq : MemLp f q μ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : E → ℝ, Continuous g ∧ HasCompactSupport g ∧ eLpNorm (f - g) p μ ≤ ε ∧
      eLpNorm (f - g) q μ ≤ ε := by
  obtain ⟨g, h1, h2, h3, h4⟩ := exists_contDiff_eLpNorm_sub_le_two hp1 hq1 hp hq hfp hfq hε
  exact ⟨g, h1.continuous, h2, h3, h4⟩

end UnforcedLeray.CZ
