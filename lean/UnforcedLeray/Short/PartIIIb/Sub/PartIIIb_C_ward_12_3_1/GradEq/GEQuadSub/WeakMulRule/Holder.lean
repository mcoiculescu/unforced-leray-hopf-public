import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Hölder limit for products on the phase cell (Lemma D of `WeakMulRule`)

Source `the November 2 reference manuscript`
2562-2564 (limit step of the Friedrichs argument); phase tests have compact `y`-support
(2525-2531).  `a_n → a₀` in `L^p` and `b_n → b₀` in `L^q` on `(0,P] × B(0,R)` with
`1/p + 1/q ≤ 1` give `a_n b_n → a₀ b₀` in `L^1` there, hence the phase integrals against a test
supported in `B(0,R)` converge.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.Cons.C03.Concrete (phaseInt)

/-- Abstract Hölder limit: on a finite measure space, `L^p` and `L^q` convergence with
`1/p + 1/q ≤ 1` gives `L^1` convergence of the products. -/
theorem tendsto_eLpNorm_one_mul {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [IsFiniteMeasure μ] {p q : ℝ≥0∞} (hpq : 1 / p + 1 / q ≤ 1)
    {a b : ℕ → α → ℂ} {a₀ b₀ : α → ℂ}
    (han : ∀ n, MemLp (a n) p μ) (hbn : ∀ n, MemLp (b n) q μ)
    (ha₀ : MemLp a₀ p μ) (hb₀ : MemLp b₀ q μ)
    (hA : Tendsto (fun n => eLpNorm (a n - a₀) p μ) atTop (𝓝 0))
    (hB : Tendsto (fun n => eLpNorm (b n - b₀) q μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => a n x * b n x - a₀ x * b₀ x) 1 μ) atTop (𝓝 0) := by
  set r : ℝ≥0∞ := (p⁻¹ + q⁻¹)⁻¹ with hr
  have : ENNReal.HolderTriple p q r := ENNReal.HolderTriple.of p q
  have hr1 : 1 ≤ r := by
    rw [hr]; apply ENNReal.one_le_inv.mpr
    simpa using hpq
  have hK : μ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / r.toReal) ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg _ (measure_ne_top _ _)
    rcases eq_or_ne r ∞ with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ r.toReal := by
        have := ENNReal.toReal_mono h hr1
        simpa using this
      have h2 : 1 / r.toReal ≤ 1 := by rw [div_le_one (by linarith)]; exact this
      simpa using h2
  have hq1 : 1 ≤ q := by
    have h : q⁻¹ ≤ 1 := le_trans le_add_self (by simpa using hpq)
    exact ENNReal.inv_le_one.mp h
  set K := μ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / r.toReal) with hKdef
  have hmem : ∀ n, MemLp (fun x => a n x * b n x - a₀ x * b₀ x) r μ := by
    intro n
    have h1 : MemLp (fun x => (a n x - a₀ x) * b n x) r μ :=
      (hbn n).mul' ((han n).sub ha₀)
    have h2 : MemLp (fun x => a₀ x * (b n x - b₀ x)) r μ :=
      ((hbn n).sub hb₀).mul' ha₀
    convert h1.add h2 using 1
    funext x; simp only [Pi.add_apply]; ring
  -- bound in `L^r`
  have hbd : ∀ n, eLpNorm (fun x => a n x * b n x - a₀ x * b₀ x) 1 μ ≤
      (eLpNorm (a n - a₀) p μ * (eLpNorm b₀ q μ + eLpNorm (b n - b₀) q μ) +
        eLpNorm a₀ p μ * eLpNorm (b n - b₀) q μ) * K := by
    intro n
    refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hr1 (hmem n).1).trans ?_
    gcongr
    have e : (fun x => a n x * b n x - a₀ x * b₀ x) =
        ((a n - a₀) • b n) + (a₀ • (b n - b₀)) := by
      funext x; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.mul_apply]; ring
    rw [e]
    refine (eLpNorm_add_le (((han n).sub ha₀).1.smul (hbn n).1) (ha₀.1.smul ((hbn n).sub hb₀).1)
      hr1).trans ?_
    gcongr
    · refine (eLpNorm_smul_le_mul_eLpNorm (p := p) (q := q) (hbn n).1 ((han n).sub ha₀).1).trans ?_
      gcongr
      have : b n = b₀ + (b n - b₀) := by funext x; simp
      calc eLpNorm (b n) q μ = eLpNorm (b₀ + (b n - b₀)) q μ := by rw [← this]
        _ ≤ _ := eLpNorm_add_le hb₀.1 ((hbn n).sub hb₀).1 hq1
    · exact eLpNorm_smul_le_mul_eLpNorm (p := p) (q := q) ((hbn n).sub hb₀).1 ha₀.1
  have hBfin : eLpNorm b₀ q μ ≠ ∞ := hb₀.eLpNorm_ne_top
  have hAfin : eLpNorm a₀ p μ ≠ ∞ := ha₀.eLpNorm_ne_top
  have h1 : Tendsto (fun n => eLpNorm (a n - a₀) p μ * (eLpNorm b₀ q μ + eLpNorm (b n - b₀) q μ))
      atTop (𝓝 (0 * (eLpNorm b₀ q μ + 0))) :=
    ENNReal.Tendsto.mul hA (Or.inr (by simpa using hBfin)) (tendsto_const_nhds.add hB)
      (Or.inr ENNReal.zero_ne_top)
  have h2 : Tendsto (fun n => eLpNorm a₀ p μ * eLpNorm (b n - b₀) q μ) atTop
      (𝓝 (eLpNorm a₀ p μ * 0)) :=
    ENNReal.Tendsto.const_mul hB (Or.inr hAfin)
  have h3 := ENNReal.Tendsto.mul_const (h1.add h2) (Or.inr hK)
  simp only [zero_mul, mul_zero, add_zero, zero_add] at h3
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun _ => bot_le) hbd


/-- Products of `L^p` and `L^q` functions with `1/p + 1/q ≤ 1` are integrable on a finite
measure space. -/
theorem integrable_mul_holder {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [IsFiniteMeasure μ] {p q : ℝ≥0∞} (hpq : 1 / p + 1 / q ≤ 1) {f g : α → ℂ}
    (hf : MemLp f p μ) (hg : MemLp g q μ) : Integrable (fun x => f x * g x) μ := by
  set r : ℝ≥0∞ := (p⁻¹ + q⁻¹)⁻¹ with hr
  have : ENNReal.HolderTriple p q r := ENNReal.HolderTriple.of p q
  have hr1 : 1 ≤ r := by
    rw [hr]; apply ENNReal.one_le_inv.mpr
    simpa using hpq
  exact (hg.mul' hf (r := r)).integrable hr1

/-- **Lemma D.**  Hölder limit for the phase integral of a product against a test supported in
`B(0,R)`: `a_n → a₀` in `L^p` and `b_n → b₀` in `L^q` on `(0,P] × B(0,R)` (hypotheses `hA`, `hB`
are the `eLpNorm` convergences there; all functions are `MemLpLoc`), with `1/p + 1/q ≤ 1`. -/
theorem phaseInt_tendsto_of_holder (P : ℝ) [Fact (0 < P)] (R : ℝ) (φ : ℝ × UnforcedLeray.Space → ℂ)
    (hφ : IsPhaseTest P φ) (hsupp : ∀ τ y, R < ‖y‖ → φ (τ, y) = 0)
    (a b : ℕ → ℝ × UnforcedLeray.Space → ℂ) (a₀ b₀ : ℝ × UnforcedLeray.Space → ℂ)
    (p q : ℝ≥0∞) (hpq : 1 / p + 1 / q ≤ 1)
    (han : ∀ n, MemLpLoc P (a n) p) (hbn : ∀ n, MemLpLoc P (b n) q)
    (ha₀ : MemLpLoc P a₀ p) (hb₀ : MemLpLoc P b₀ q)
    (hA : Tendsto (fun n => eLpNorm (a n - a₀) p
      ((volume.restrict (Ioc (0 : ℝ) P)).prod (volume.restrict (Metric.closedBall 0 R)))) atTop (𝓝 0))
    (hB : Tendsto (fun n => eLpNorm (b n - b₀) q
      ((volume.restrict (Ioc (0 : ℝ) P)).prod (volume.restrict (Metric.closedBall 0 R)))) atTop (𝓝 0)) :
    Tendsto (fun n => phaseInt P (fun x => φ x * (a n x * b n x))) atTop
      (𝓝 (phaseInt P (fun x => φ x * (a₀ x * b₀ x)))) := by
  set μ1 : Measure ℝ := volume.restrict (Ioc (0 : ℝ) P) with hμ1
  set μ2 : Measure UnforcedLeray.Space := volume.restrict (Metric.closedBall 0 R) with hμ2
  set μ : Measure (ℝ × UnforcedLeray.Space) := μ1.prod μ2 with hμ
  have : IsFiniteMeasure μ1 := ⟨by simp [hμ1]⟩
  have : IsFiniteMeasure μ2 :=
    ⟨by rw [hμ2, Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
  have hμr : μ = (volume : Measure (ℝ × UnforcedLeray.Space)).restrict
      (Ioc (0 : ℝ) P ×ˢ Metric.closedBall 0 R) := by
    rw [hμ, hμ1, hμ2, Measure.prod_restrict, Measure.volume_eq_prod]
  have hφc : Continuous φ := hφ.smooth.continuous
  -- reduction of `phaseInt` to the product integral
  have reduce : ∀ f : ℝ × UnforcedLeray.Space → ℂ, Integrable (fun x => φ x * f x) μ →
      phaseInt P (fun x => φ x * f x) = P⁻¹ • ∫ x, φ x * f x ∂μ := by
    intro f hf
    unfold phaseInt
    congr 1
    rw [hμ, integral_prod _ hf]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
    rw [hsupp t y (by simpa [not_le] using hy), zero_mul]
  -- bound on `φ`
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := P)).prod
    (isCompact_closedBall (0 : UnforcedLeray.Space) R) |>.exists_bound_of_continuousOn
    hφc.continuousOn
  have hCae : ∀ᵐ x ∂μ, ‖φ x‖ ≤ C := by
    rw [hμr]
    refine (ae_restrict_mem (measurableSet_Ioc.prod measurableSet_closedBall)).mono fun x hx => ?_
    exact hC x ⟨Ioc_subset_Icc_self hx.1, hx.2⟩
  have hint : ∀ f : ℝ × UnforcedLeray.Space → ℂ, Integrable f μ →
      Integrable (fun x => φ x * f x) μ := fun f hf =>
    hf.bdd_mul hφc.aestronglyMeasurable hCae
  have hmem : ∀ f : ℝ × UnforcedLeray.Space → ℂ, ∀ s : ℝ≥0∞, MemLpLoc P f s → MemLp f s μ :=
    fun f s h => h R
  have hL1 := tendsto_eLpNorm_one_mul (μ := μ) hpq (fun n => hmem _ _ (han n))
    (fun n => hmem _ _ (hbn n)) (hmem _ _ ha₀) (hmem _ _ hb₀) hA hB
  have hprod : ∀ n, Integrable (fun x => a n x * b n x) μ := fun n =>
    integrable_mul_holder hpq (hmem _ _ (han n)) (hmem _ _ (hbn n))
  have hprod0 : Integrable (fun x => a₀ x * b₀ x) μ :=
    integrable_mul_holder hpq (hmem _ _ ha₀) (hmem _ _ hb₀)
  -- the bound
  have hbound : ∀ n, ‖phaseInt P (fun x => φ x * (a n x * b n x)) -
      phaseInt P (fun x => φ x * (a₀ x * b₀ x))‖ ≤
      P⁻¹ * (C * (eLpNorm (fun x => a n x * b n x - a₀ x * b₀ x) 1 μ).toReal) := by
    intro n
    rw [reduce _ (hint _ (hprod n)), reduce _ (hint _ hprod0), ← smul_sub,
      ← integral_sub (hint _ (hprod n)) (hint _ hprod0)]
    have hg : Integrable (fun x => a n x * b n x - a₀ x * b₀ x) μ := (hprod n).sub hprod0
    have e1 : (fun x => φ x * (a n x * b n x) - φ x * (a₀ x * b₀ x)) =
        fun x => φ x * (a n x * b n x - a₀ x * b₀ x) := by
      funext x; ring
    rw [e1, norm_smul]
    have hP : ‖P⁻¹‖ = P⁻¹ := by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Fact.out : 0 < P))]
    rw [hP]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Fact.out : 0 < P).le)
    calc ‖∫ x, φ x * (a n x * b n x - a₀ x * b₀ x) ∂μ‖
        ≤ ∫ x, C * ‖a n x * b n x - a₀ x * b₀ x‖ ∂μ := by
          refine norm_integral_le_of_norm_le (hg.norm.const_mul C) ?_
          filter_upwards [hCae] with x hx
          rw [norm_mul]
          gcongr
      _ = C * (eLpNorm (fun x => a n x * b n x - a₀ x * b₀ x) 1 μ).toReal := by
          rw [integral_const_mul, integral_norm_eq_lintegral_enorm hg.1,
            eLpNorm_one_eq_lintegral_enorm]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) hbound ?_
  have h0 : Tendsto (fun n => (eLpNorm (fun x => a n x * b n x - a₀ x * b₀ x) 1 μ).toReal)
      atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL1
    rw [ENNReal.toReal_zero] at this
    exact this
  simpa using (h0.const_mul C).const_mul P⁻¹

end UnforcedLeray.Short.PartIIIb.Concrete
