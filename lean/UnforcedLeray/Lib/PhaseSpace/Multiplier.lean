import UnforcedLeray.Lib.PhaseSpace.Pairing

/-!
# Spatial multipliers of slice-continuous functions (helper for INF25 T25.3)

For a bounded continuous `m : ℝ³ → ℝ` and a periodic slice-continuous `G`, the product
`(mulT m G)(τ, y) = m(y) G(τ, y)` is again periodic and slice-continuous. If a sequence of
multipliers is uniformly bounded and tends to zero pointwise, then `mulT mₙ G → 0` in
`Y_r` for `r < ∞` (`tendsto_testElem_mulT`): pointwise in the phase by dominated convergence,
and uniformly in the phase because the slices of `G` form a compact subset of `L^r`. This is
the convergence step of the cutoff argument of T25.3 (scoping note INF15-INF17-INF25 §5).

Status: infrastructure only.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace UnforcedLeray.PhaseSpace

/-- Multiplication of a phase function by a spatial scalar function. -/
def mulT (m : Space → ℝ) (G : ℝ × Space → CVec3) : ℝ × Space → CVec3 := fun p => m p.2 • G p

variable {r : ℝ≥0∞} [hr1 : Fact (1 ≤ r)]

theorem memLp_mul_of_bound {g : Space → CVec3} (hg : MemLp g r volume) {m : Space → ℝ}
    (hm : Continuous m) {L : ℝ} (hL : ∀ y, |m y| ≤ L) :
    MemLp (fun y => m y • g y) r volume :=
  hg.of_le_mul (c := L) (hm.aestronglyMeasurable.smul hg.1) (Eventually.of_forall fun y => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hL y) (norm_nonneg _))

theorem SliceCont.mulT {G : ℝ × Space → CVec3} (hG : SliceCont r G) {m : Space → ℝ}
    (hm : Continuous m) {L : ℝ} (hL : ∀ y, |m y| ≤ L) : SliceCont r (mulT m G) where
  memLp τ := memLp_mul_of_bound (hG.memLp τ) hm hL
  continuous := by
    have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
    have key : ∀ τ σ : ℝ,
        dist (MemLp.toLp _ (memLp_mul_of_bound (hG.memLp τ) hm hL))
            (MemLp.toLp _ (memLp_mul_of_bound (hG.memLp σ) hm hL)) ≤
          L * dist (MemLp.toLp _ (hG.memLp τ)) (MemLp.toLp _ (hG.memLp σ)) := by
      intro τ σ
      rw [dist_eq_norm, dist_eq_norm, ← MemLp.toLp_sub, ← MemLp.toLp_sub, Lp.norm_toLp,
        Lp.norm_toLp]
      have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := volume)
        (f := (fun y => m y • G (τ, y)) - fun y => m y • G (σ, y))
        (g := (fun y => G (τ, y)) - fun y => G (σ, y)) (c := L)
        (Eventually.of_forall fun y => by
          simp only [Pi.sub_apply]
          rw [← smul_sub, norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hL y) (norm_nonneg _)) r
      have hfin : ENNReal.ofReal L *
          eLpNorm ((fun y => G (τ, y)) - fun y => G (σ, y)) r volume ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          ((hG.memLp τ).sub (hG.memLp σ)).eLpNorm_lt_top.ne
      calc (eLpNorm ((fun y => m y • G (τ, y)) - fun y => m y • G (σ, y)) r volume).toReal
          ≤ (ENNReal.ofReal L *
              eLpNorm ((fun y => G (τ, y)) - fun y => G (σ, y)) r volume).toReal :=
            ENNReal.toReal_mono hfin h
        _ = L * (eLpNorm ((fun y => G (τ, y)) - fun y => G (σ, y)) r volume).toReal := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hL0]
    refine continuous_iff_continuousAt.2 fun τ => ?_
    rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun σ => key σ τ) ?_
    have h := hG.continuous.tendsto τ
    rw [tendsto_iff_dist_tendsto_zero] at h
    simpa using h.const_mul L

theorem IsSliceTest.mulT {P : ℝ} {G : ℝ × Space → CVec3} (hG : IsSliceTest P r G)
    {m : Space → ℝ} (hm : Continuous m) {L : ℝ} (hL : ∀ y, |m y| ≤ L) :
    IsSliceTest P r (mulT m G) :=
  ⟨fun τ y => by simp [PhaseSpace.mulT, hG.1 τ y], hG.2.mulT hm hL⟩

/-- Dominated convergence: a bounded multiplier tending to zero pointwise sends a fixed
`L^r` function to zero in `L^r`, `r < ∞`. -/
theorem tendsto_eLpNorm_mul (hr : r ≠ ⊤) {g : Space → CVec3} (hg : MemLp g r volume)
    {m : ℕ → Space → ℝ} (hm : ∀ n, Continuous (m n)) {L : ℝ} (hL : ∀ n y, |m n y| ≤ L)
    (hlim : ∀ y, Tendsto (fun n => m n y) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun y => m n y • g y) r volume) atTop (𝓝 0) := by
  have hr0 : r ≠ 0 := (zero_lt_one.trans_le hr1.out).ne'
  have hp : 0 < r.toReal := ENNReal.toReal_pos hr0 hr
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hr]
  have hgint : ∫⁻ y, ‖g y‖ₑ ^ r.toReal = eLpNorm g r volume ^ r.toReal := by
    rw [eLpNorm_eq_eLpNorm' hr0 hr, lintegral_rpow_enorm_eq_rpow_eLpNorm' hp]
  have hint : Tendsto (fun n => ∫⁻ y, ‖m n y • g y‖ₑ ^ r.toReal) atTop (𝓝 0) := by
    have h := tendsto_lintegral_of_dominated_convergence' (μ := volume)
      (F := fun n y => ‖m n y • g y‖ₑ ^ r.toReal) (f := fun _ => 0)
      (fun y => (ENNReal.ofReal L * ‖g y‖ₑ) ^ r.toReal)
      (fun n => (((hm n).aestronglyMeasurable.smul hg.1).enorm.pow_const _))
      (fun n => Eventually.of_forall fun y => by
        refine ENNReal.rpow_le_rpow ?_ hp.le
        rw [enorm_smul, ← ofReal_norm, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hL n y)) (by positivity))
      (by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top),
          hgint]
        exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top)
          (ENNReal.rpow_ne_top_of_nonneg hp.le hg.eLpNorm_lt_top.ne))
      (Eventually.of_forall fun y => by
        have h1 : Tendsto (fun n => m n y • g y) atTop (𝓝 0) := by
          simpa using (hlim y).smul_const (g y)
        have h2 := ((ENNReal.continuous_rpow_const (y := r.toReal)).comp
          continuous_enorm).tendsto (0 : CVec3)
        have h3 := h2.comp h1
        simp only [Function.comp_apply, enorm_zero, ENNReal.zero_rpow_of_pos hp] at h3
        exact h3)
    simpa using h
  have h3 := ((ENNReal.continuous_rpow_const (y := 1 / r.toReal)).tendsto 0).comp hint
  rw [ENNReal.zero_rpow_of_pos (by positivity : 0 < 1 / r.toReal)] at h3
  exact h3

variable {P : ℝ} [Fact (0 < P)]

theorem norm_circleSlice_mulT {G : ℝ × Space → CVec3} (hG : IsSliceTest P r G)
    {m : Space → ℝ} (hm : Continuous m) {L : ℝ} (hL : ∀ y, |m y| ≤ L) (τ : AddCircle P) :
    ‖circleSlice (hG.mulT hm hL) τ‖ =
      (eLpNorm (fun y => m y • (circleSlice hG τ : Space → CVec3) y) r volume).toReal := by
  induction τ using QuotientAddGroup.induction_on with
  | H t =>
    rw [circleSlice_coe, circleSlice_coe, sliceMap, Lp.norm_toLp, sliceMap]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (hG.2.memLp t)] with y hy
    simp [PhaseSpace.mulT, hy]

/-- **Convergence of multiplied tests.** If `|mₙ| ≤ L` and `mₙ → 0` pointwise, then
`mulT mₙ G → 0` in `Y_r`, `1 ≤ r < ∞`. -/
theorem tendsto_testElem_mulT (hr : r ≠ ⊤) {G : ℝ × Space → CVec3} (hG : IsSliceTest P r G)
    {m : ℕ → Space → ℝ} (hm : ∀ n, Continuous (m n)) {L : ℝ} (hL : ∀ n y, |m n y| ≤ L)
    (hlim : ∀ y, Tendsto (fun n => m n y) atTop (𝓝 0)) :
    Tendsto (fun n => testElem P r (mulT (m n) G)) atTop (𝓝 0) := by
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ : ℝ := ε / (2 * (L + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  -- a finite δ-net of the compact set of slices
  have hK : IsCompact (range (circleSlice hG)) := isCompact_range (circleSlice hG).continuous
  obtain ⟨t, -, ht, hcover⟩ := finite_approx_of_totallyBounded hK.totallyBounded δ hδ0
  have hev : ∀ᶠ n in atTop, ∀ g ∈ t,
      eLpNorm (fun y => m n y • (g : Space → CVec3) y) r volume < ENNReal.ofReal δ := by
    rw [eventually_all_finite ht]
    intro g _
    exact (tendsto_eLpNorm_mul hr (Lp.memLp g) hm hL hlim).eventually
      (gt_mem_nhds (ENNReal.ofReal_pos.2 hδ0))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn => ?_⟩
  have hbd : ∀ τ : AddCircle P, ‖circleSlice (hG.mulT (hm n) (hL n)) τ‖ ≤ (L + 1) * δ := by
    intro τ
    obtain ⟨g, hgt, hgτ⟩ := mem_iUnion₂.1 (hcover (mem_range_self τ))
    rw [norm_circleSlice_mulT hG (hm n) (hL n)]
    set h := circleSlice hG τ
    have hsplit : (fun y => m n y • (h : Space → CVec3) y) =ᵐ[volume]
        (fun y => m n y • ((h - g : Lp CVec3 r (volume : Measure Space)) : Space → CVec3) y) +
          fun y => m n y • (g : Space → CVec3) y := by
      filter_upwards [Lp.coeFn_sub h g] with y hy
      show _ = m n y • ((h - g : Lp CVec3 r (volume : Measure Space)) : Space → CVec3) y +
        m n y • (g : Space → CVec3) y
      rw [hy, Pi.sub_apply, smul_sub, sub_add_cancel]
    have h1 : eLpNorm (fun y => m n y • ((h - g : Lp CVec3 r (volume : Measure Space)) : Space → CVec3) y)
        r volume ≤ ENNReal.ofReal L * ENNReal.ofReal δ := by
      refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (c := L)
        (g := ((h - g : Lp CVec3 r (volume : Measure Space)) : Space → CVec3))
        (Eventually.of_forall fun y => ?_) r).trans ?_
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hL n y) (norm_nonneg _)
      · gcongr
        rw [← Lp.enorm_def, ← ofReal_norm, ← dist_eq_norm]
        exact ENNReal.ofReal_le_ofReal (le_of_lt hgτ)
    have h2 := hN n hn g hgt
    have hsum : eLpNorm (fun y => m n y • (h : Space → CVec3) y) r volume ≤
        ENNReal.ofReal ((L + 1) * δ) := by
      rw [eLpNorm_congr_ae hsplit]
      refine (eLpNorm_add_le ((hm n).aestronglyMeasurable.smul (Lp.aestronglyMeasurable _))
        ((hm n).aestronglyMeasurable.smul (Lp.aestronglyMeasurable _)) hr1.out).trans ?_
      calc _ ≤ ENNReal.ofReal L * ENNReal.ofReal δ + ENNReal.ofReal δ := add_le_add h1 h2.le
        _ = ENNReal.ofReal ((L + 1) * δ) := by
            rw [← ENNReal.ofReal_mul hL0, ← ENNReal.ofReal_add (by positivity) hδ0.le]
            congr 1
            ring
    calc (eLpNorm (fun y => m n y • (h : Space → CVec3) y) r volume).toReal
        ≤ (ENNReal.ofReal ((L + 1) * δ)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
      _ = (L + 1) * δ := ENNReal.toReal_ofReal (by positivity)
  have hnorm : ‖testElem P r (mulT (m n) G)‖ ≤ (L + 1) * δ := by
    rw [testElem_of (hG.mulT (hm n) (hL n))]
    have h := Lp.norm_le_of_ae_bound (μ := AddCircle.haarAddCircle (T := P))
      (f := ContinuousMap.toLp (E := Lp CVec3 r (volume : Measure Space)) r
        AddCircle.haarAddCircle ℂ (circleSlice (hG.mulT (hm n) (hL n))))
      (C := (L + 1) * δ) (by positivity) (by
        filter_upwards [ContinuousMap.coeFn_toLp (E := Lp CVec3 r (volume : Measure Space))
          (p := r) (𝕜 := ℂ) AddCircle.haarAddCircle
          (circleSlice (hG.mulT (hm n) (hL n)))] with τ hτ
        rw [hτ]
        exact hbd τ)
    have h1 : measureUnivNNReal (AddCircle.haarAddCircle (T := P)) = 1 := by
      simp [measureUnivNNReal]
    rw [h1] at h
    simpa using h
  rw [dist_zero_right]
  calc ‖testElem P r (mulT (m n) G)‖ ≤ (L + 1) * δ := hnorm
    _ = ε / 2 := by
        rw [hδ]
        field_simp
    _ < ε := by linarith

end UnforcedLeray.PhaseSpace
