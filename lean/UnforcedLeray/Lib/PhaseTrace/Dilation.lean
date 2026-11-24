import UnforcedLeray.Lib.PhaseSpace.Charts
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Spatial dilations on `L^q(ℝ³; E)` (block 2F, INF14 T6 support)

The comoving pullback of tex 7612–7616 (`V(t, x) = w(τ₀ + t, e^{-t/2} x)`, unit B0434) is the
composition of the phase slice `w(τ₀ + t)` with the dilation `x ↦ e^{-t/2} x`. This file
builds that dilation as a bounded operator on `L^q(ℝ³; E)`:

* `dil s g = g(e^{-s/2} ·)` (`dil`, `coeFn_dil`), with the exact norm
  `‖dil s g‖ = e^{(3s/2)(1/q)} ‖g‖` (`norm_dil`, constant `dilConst`);
* the group law `dil s (dil t g) = dil (s + t) g` and `dil 0 = id`;
* strong continuity for `q < ∞` (`tendsto_dil_zero`) and joint continuity of
  `(s, g) ↦ dil s g` (`continuous_dil`).

The continuity proof is adapted from

(`tendsto_eLpNorm_comp_sub_of_compact`, `tendsto_eLpNorm_comp_sub`), there for `ℝ³`-valued
fields, here for a general real normed space `E` and specialised to dilations.

Status: infrastructure for the phase trace (`Lib/PhaseTrace.lean`); no manuscript unit is
proved here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.PhaseTrace

open UnforcedLeray.PhaseSpace

/-! ### Scalars -/

/-- The dilation factor `e^{-s/2}` of the comoving chart (tex 7614). -/
def dilScale (s : ℝ) : ℝ := Real.exp (-s / 2)

theorem dilScale_pos (s : ℝ) : 0 < dilScale s := Real.exp_pos _

theorem dilScale_ne_zero (s : ℝ) : dilScale s ≠ 0 := (dilScale_pos s).ne'

theorem dilScale_mul (s t : ℝ) : dilScale s * dilScale t = dilScale (s + t) := by
  unfold dilScale
  rw [← Real.exp_add]
  ring_nf

theorem dilScale_zero : dilScale 0 = 1 := by simp [dilScale]

theorem continuous_dilScale : Continuous dilScale :=
  Real.continuous_exp.comp (continuous_neg.div_const 2)

/-- The norm factor of the dilation: `‖dil s g‖_q = dilConst q s ‖g‖_q`, i.e. `e^{3s/(2q)}`
for finite `q` and `1` for `q = ∞`. -/
def dilConst (q : ℝ≥0∞) (s : ℝ) : ℝ := Real.exp (3 * s / 2 * (1 / q).toReal)

theorem dilConst_pos (q : ℝ≥0∞) (s : ℝ) : 0 < dilConst q s := Real.exp_pos _

theorem dilConst_add (q : ℝ≥0∞) (s t : ℝ) : dilConst q (s + t) = dilConst q s * dilConst q t := by
  unfold dilConst
  rw [← Real.exp_add]
  ring_nf

theorem dilConst_zero (q : ℝ≥0∞) : dilConst q 0 = 1 := by simp [dilConst]

theorem dilConst_mono (q : ℝ≥0∞) {s t : ℝ} (h : s ≤ t) : dilConst q s ≤ dilConst q t := by
  unfold dilConst
  have : 0 ≤ (1 / q).toReal := ENNReal.toReal_nonneg
  gcongr

theorem dilConst_le_one (q : ℝ≥0∞) {s : ℝ} (h : s ≤ 0) : dilConst q s ≤ 1 := by
  simpa [dilConst_zero] using dilConst_mono q h

theorem continuous_dilConst (q : ℝ≥0∞) : Continuous (dilConst q) :=
  Real.continuous_exp.comp (((continuous_const.mul continuous_id).div_const 2).mul continuous_const)

/-! ### Measure transport -/

theorem map_dilScale (s : ℝ) :
    Measure.map (fun x : Space => dilScale s • x) volume =
      ENNReal.ofReal (Real.exp (3 * s / 2)) • volume := by
  rw [map_smul_space (dilScale_ne_zero s)]
  congr 2
  unfold dilScale
  rw [abs_of_pos (by positivity), ← Real.exp_nat_mul, ← Real.exp_neg]
  congr 1
  push_cast
  ring

theorem qmp_dilScale (s : ℝ) :
    Measure.QuasiMeasurePreserving (fun x : Space => dilScale s • x) volume volume :=
  ⟨measurable_const_smul _, by rw [map_dilScale]; exact Measure.smul_absolutelyContinuous⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : ℝ≥0∞}

omit [NormedSpace ℝ E] in
theorem eLpNorm_comp_dilScale (s : ℝ) {g : Space → E} (hg : AEStronglyMeasurable g volume) :
    eLpNorm (fun x => g (dilScale s • x)) q volume =
      ENNReal.ofReal (dilConst q s) * eLpNorm g q volume := by
  have hm : AEMeasurable (fun x : Space => dilScale s • x) volume :=
    (measurable_const_smul _).aemeasurable
  have hg' : AEStronglyMeasurable g (Measure.map (fun x : Space => dilScale s • x) volume) := by
    rw [map_dilScale]; exact hg.smul_measure _
  change eLpNorm (g ∘ fun x : Space => dilScale s • x) q volume = _
  rw [← eLpNorm_map_measure hg' hm, map_dilScale,
    eLpNorm_smul_measure_of_ne_zero (by simp [Real.exp_pos]), smul_eq_mul,
    ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
  rfl

omit [NormedSpace ℝ E] in
theorem memLp_comp_dilScale (s : ℝ) {g : Space → E} (hg : MemLp g q volume) :
    MemLp (fun x => g (dilScale s • x)) q volume :=
  ⟨hg.1.comp_quasiMeasurePreserving (qmp_dilScale s), by
    rw [eLpNorm_comp_dilScale s hg.1]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.2⟩

/-! ### The dilation operator -/

variable [Fact (1 ≤ q)]

variable (E q) in
/-- The dilation `g ↦ g(e^{-s/2} ·)` as a linear map on `L^q(ℝ³; E)`. -/
def dilₗ (s : ℝ) : Lp E q (volume : Measure Space) →ₗ[ℝ] Lp E q (volume : Measure Space) where
  toFun g := (memLp_comp_dilScale s (Lp.memLp g)).toLp _
  map_add' g h := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_comp_dilScale s (Lp.memLp (g + h))),
      Lp.coeFn_add ((memLp_comp_dilScale s (Lp.memLp g)).toLp _)
        ((memLp_comp_dilScale s (Lp.memLp h)).toLp _),
      MemLp.coeFn_toLp (memLp_comp_dilScale s (Lp.memLp g)),
      MemLp.coeFn_toLp (memLp_comp_dilScale s (Lp.memLp h)),
      (qmp_dilScale s).ae_eq_comp (Lp.coeFn_add g h)] with x h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4]
    simpa using h5
  map_smul' c g := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_comp_dilScale s (Lp.memLp (c • g))),
      Lp.coeFn_smul c ((memLp_comp_dilScale s (Lp.memLp g)).toLp _),
      MemLp.coeFn_toLp (memLp_comp_dilScale s (Lp.memLp g)),
      (qmp_dilScale s).ae_eq_comp (Lp.coeFn_smul c g)] with x h1 h2 h3 h5
    rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3]
    simpa using h5

theorem norm_dilₗ (s : ℝ) (g : Lp E q (volume : Measure Space)) :
    ‖dilₗ E q s g‖ = dilConst q s * ‖g‖ := by
  change ‖(memLp_comp_dilScale s (Lp.memLp g)).toLp _‖ = _
  rw [Lp.norm_toLp, eLpNorm_comp_dilScale s (Lp.aestronglyMeasurable g), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (dilConst_pos q s).le, Lp.norm_def]

variable (E q) in
/-- **The dilation operator** `dil s g = g(e^{-s/2} ·)` on `L^q(ℝ³; E)` (tex 7612–7616). -/
def dil (s : ℝ) : Lp E q (volume : Measure Space) →L[ℝ] Lp E q (volume : Measure Space) :=
  (dilₗ E q s).mkContinuous (dilConst q s) fun g => (norm_dilₗ s g).le

theorem dil_apply (s : ℝ) (g : Lp E q (volume : Measure Space)) :
    dil E q s g = (memLp_comp_dilScale s (Lp.memLp g)).toLp (fun x => g (dilScale s • x)) := rfl

theorem coeFn_dil (s : ℝ) (g : Lp E q (volume : Measure Space)) :
    (dil E q s g : Space → E) =ᵐ[volume] fun x => g (dilScale s • x) :=
  MemLp.coeFn_toLp (memLp_comp_dilScale s (Lp.memLp g))

theorem norm_dil (s : ℝ) (g : Lp E q (volume : Measure Space)) :
    ‖dil E q s g‖ = dilConst q s * ‖g‖ :=
  norm_dilₗ s g

theorem dil_dil (s t : ℝ) (g : Lp E q (volume : Measure Space)) :
    dil E q s (dil E q t g) = dil E q (s + t) g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_dil s (dil E q t g), coeFn_dil (s + t) g,
    (qmp_dilScale s).ae_eq_comp (coeFn_dil t g)] with x h1 h2 h3
  rw [h1, h2]
  simp only [Function.comp_apply] at h3
  rw [h3, smul_smul, mul_comm, dilScale_mul, add_comm]

theorem dil_zero (g : Lp E q (volume : Measure Space)) : dil E q 0 g = g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_dil 0 g] with x h1
  rw [h1, dilScale_zero, one_smul]

theorem dil_neg_dil (t : ℝ) (g : Lp E q (volume : Measure Space)) :
    dil E q (-t) (dil E q t g) = g := by
  rw [dil_dil, neg_add_cancel, dil_zero]

/-! ### Strong continuity (adapted from `Units/B0418/Continuity.lean`) -/

omit [Fact (1 ≤ q)] [NormedSpace ℝ E] in
/-- Continuous compactly supported functions: dilations converge to the identity in `L^q`. -/
theorem tendsto_eLpNorm_dil_sub_of_compact {g : Space → E} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hp1 : 1 ≤ q) (hp : q ≠ ∞) :
    Tendsto (fun s => eLpNorm (fun x => g (dilScale s • x) - g x) q volume) (𝓝 0) (𝓝 0) := by
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall (0 : Space)
  set R' : ℝ := |R| * Real.exp (1 / 2) with hR'def
  have hzero : ∀ y, R < ‖y‖ → g y = 0 := by
    intro y hy
    by_contra hne
    have h1 := hR (subset_tsupport g hne)
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    linarith
  have hnear : ∀ᶠ s : ℝ in 𝓝 0, s < 1 := gt_mem_nhds (by norm_num)
  have hsupp : ∀ᶠ s : ℝ in 𝓝 0, ∀ x : Space, ‖dilScale s • x‖ ≤ R → ‖x‖ ≤ R' := by
    filter_upwards [hnear] with s hs x hx
    rw [norm_smul, Real.norm_of_nonneg (dilScale_pos s).le] at hx
    have hb : Real.exp (-1 / 2) ≤ dilScale s := by
      exact Real.exp_le_exp.mpr (by linarith)
    have hb' : Real.exp (-1 / 2) * Real.exp (1 / 2) = 1 := by
      rw [← Real.exp_add]; norm_num
    have hx' : Real.exp (-1 / 2) * ‖x‖ ≤ |R| := by
      calc Real.exp (-1 / 2) * ‖x‖ ≤ dilScale s * ‖x‖ := by gcongr
        _ ≤ R := hx
        _ ≤ |R| := le_abs_self R
    calc ‖x‖ = (Real.exp (-1 / 2) * ‖x‖) * Real.exp (1 / 2) := by
          rw [mul_comm (Real.exp (-1 / 2)), mul_assoc, hb', mul_one]
      _ ≤ |R| * Real.exp (1 / 2) := by gcongr
  have hp0 : q ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hpr : 0 < q.toReal := ENNReal.toReal_pos hp0 hp
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp]
  have hlim : Tendsto (fun s => ∫⁻ x, ‖g (dilScale s • x) - g x‖ₑ ^ q.toReal) (𝓝 0)
      (𝓝 (∫⁻ _x : Space, (0 : ℝ≥0∞))) := by
    refine tendsto_lintegral_filter_of_dominated_convergence
      ((Metric.closedBall (0 : Space) (max R R')).indicator
        (fun _ => (ENNReal.ofReal (2 * M)) ^ q.toReal)) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun s =>
        ((hg.comp (continuous_const_smul _)).sub hg).enorm.measurable.pow_const _
    · filter_upwards [hsupp] with s hi
      refine Eventually.of_forall (fun x => ?_)
      by_cases hx : ‖x‖ ≤ max R R'
      · rw [Set.indicator_of_mem (by simpa using hx)]
        gcongr
        rw [← ofReal_norm]
        apply ENNReal.ofReal_le_ofReal
        calc ‖g (dilScale s • x) - g x‖ ≤ ‖g (dilScale s • x)‖ + ‖g x‖ := norm_sub_le _ _
          _ ≤ M + M := add_le_add (hM _) (hM _)
          _ = 2 * M := by ring
      · rw [Set.indicator_of_notMem (by simpa using hx)]
        have h1 : R' < ‖x‖ := lt_of_le_of_lt (le_max_right _ _) (not_le.mp hx)
        have h2 : R < ‖x‖ := lt_of_le_of_lt (le_max_left _ _) (not_le.mp hx)
        have h3 : R < ‖dilScale s • x‖ := by
          by_contra h
          exact absurd (hi x (not_lt.mp h)) (not_le.mpr h1)
        rw [hzero _ h3, hzero _ h2, sub_zero, enorm_zero, ENNReal.zero_rpow_of_pos hpr]
    · rw [lintegral_indicator measurableSet_closedBall, setLIntegral_const]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hpr.le ENNReal.ofReal_ne_top)
        measure_closedBall_lt_top.ne
    · refine Eventually.of_forall (fun x => ?_)
      have hs : Tendsto (fun s => dilScale s • x) (𝓝 0) (𝓝 x) := by
        have hc : Continuous fun s : ℝ => dilScale s • x := continuous_dilScale.smul continuous_const
        have := hc.tendsto 0
        simpa [dilScale_zero] using this
      have h1 : Tendsto (fun s => g (dilScale s • x) - g x) (𝓝 0) (𝓝 0) := by
        have := ((hg.tendsto x).comp hs).sub_const (g x)
        simpa using this
      have h2 := (continuous_enorm.tendsto (0 : E)).comp h1
      rw [enorm_zero] at h2
      have h3 := ((ENNReal.continuous_rpow_const (y := q.toReal)).tendsto 0).comp h2
      rw [ENNReal.zero_rpow_of_pos hpr] at h3
      exact h3
  rw [lintegral_zero] at hlim
  have h4 := ((ENNReal.continuous_rpow_const (y := 1 / q.toReal)).tendsto 0).comp hlim
  rwa [ENNReal.zero_rpow_of_pos (by positivity)] at h4

omit [Fact (1 ≤ q)] in
/-- Density upgrade: dilations converge to the identity on all of `L^q`, `1 ≤ q < ∞`. -/
theorem tendsto_eLpNorm_dil_sub (hp1 : 1 ≤ q) (hp : q ≠ ∞) {h : Space → E}
    (hh : MemLp h q volume) :
    Tendsto (fun s => eLpNorm (fun x => h (dilScale s • x) - h x) q volume) (𝓝 0) (𝓝 0) := by
  set C : ℝ≥0∞ := ENNReal.ofReal (dilConst q 1) with hCdef
  have hC : C ≠ ∞ := ENNReal.ofReal_ne_top
  have hbound : ∀ᶠ s : ℝ in 𝓝 0, ∀ u : Space → E, MemLp u q volume →
      MemLp (fun x => u (dilScale s • x)) q volume ∧
        eLpNorm (fun x => u (dilScale s • x)) q volume ≤ C * eLpNorm u q volume := by
    filter_upwards [gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with s hs u hu
    refine ⟨memLp_comp_dilScale s hu, ?_⟩
    rw [eLpNorm_comp_dilScale s hu.1]
    gcongr
    exact ENNReal.ofReal_le_ofReal (dilConst_mono q hs.le)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨r, -, hr0, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hr : 0 < r := ENNReal.ofReal_pos.mp hr0
  set δ : ℝ := r / (2 * (C.toReal + 1)) with hδ
  have hC0 : 0 ≤ C.toReal := ENNReal.toReal_nonneg
  have hδ0 : 0 < δ := by positivity
  obtain ⟨g, hgc, hgh, hgcont, hgm⟩ :=
    hh.exists_hasCompactSupport_eLpNorm_sub_le hp (ε := ENNReal.ofReal δ)
      (by simpa using hδ0)
  have hT := tendsto_eLpNorm_dil_sub_of_compact hgcont hgc hp1 hp
  have hev := (ENNReal.tendsto_nhds_zero.mp hT) (ENNReal.ofReal (r / 2))
    (by simpa using hr)
  filter_upwards [hev, hbound] with i hi hb
  have hA := hb (h - g) (hh.sub hgm)
  have hdec : (fun x => h (dilScale i • x) - h x) =
      (fun x => (h - g) (dilScale i • x)) +
        ((fun x => g (dilScale i • x) - g x) + (g - h)) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    abel
  have hgh' : eLpNorm (g - h) q volume ≤ ENNReal.ofReal δ := by
    rw [eLpNorm_sub_comm]
    exact hgh
  have hmB : AEStronglyMeasurable (fun x => g (dilScale i • x) - g x) volume :=
    (hb g hgm).1.aestronglyMeasurable.sub hgm.aestronglyMeasurable
  have hkey : C * ENNReal.ofReal δ + (ENNReal.ofReal (r / 2) + ENNReal.ofReal δ) =
      ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_toReal hC, ← ENNReal.ofReal_mul hC0,
      ← ENNReal.ofReal_add (by positivity) hδ0.le,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    rw [hδ]
    field_simp
    ring
  calc eLpNorm (fun x => h (dilScale i • x) - h x) q volume
      ≤ eLpNorm (fun x => (h - g) (dilScale i • x)) q volume +
          eLpNorm ((fun x => g (dilScale i • x) - g x) + (g - h)) q volume := by
        rw [hdec]
        exact eLpNorm_add_le hA.1.aestronglyMeasurable
          (hmB.add (hgm.aestronglyMeasurable.sub hh.aestronglyMeasurable)) hp1
    _ ≤ eLpNorm (fun x => (h - g) (dilScale i • x)) q volume +
          (eLpNorm (fun x => g (dilScale i • x) - g x) q volume + eLpNorm (g - h) q volume) := by
        gcongr
        exact eLpNorm_add_le hmB (hgm.aestronglyMeasurable.sub hh.aestronglyMeasurable) hp1
    _ ≤ C * ENNReal.ofReal δ + (ENNReal.ofReal (r / 2) + ENNReal.ofReal δ) := by
        gcongr
        exact hA.2.trans (by gcongr)
    _ = ENNReal.ofReal r := hkey
    _ ≤ ε := hrε.le

/-- **Strong continuity of dilations at `s = 0`** on `L^q(ℝ³; E)`, `1 ≤ q < ∞`. -/
theorem tendsto_dil_zero (hq : q ≠ ∞) (g : Lp E q (volume : Measure Space)) :
    Tendsto (fun s => dil E q s g) (𝓝 0) (𝓝 g) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hT := tendsto_eLpNorm_dil_sub (Fact.out : 1 ≤ q) hq (Lp.memLp g)
  have hT' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hT
  rw [ENNReal.toReal_zero] at hT'
  refine hT'.congr fun s => ?_
  simp only [Function.comp_apply]
  rw [Lp.norm_def]
  congr 1
  refine eLpNorm_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (dil E q s g) g, coeFn_dil s g] with x h1 h2
  rw [h1, Pi.sub_apply, h2]

/-- **Joint continuity** of `(s, g) ↦ dil s g` on `ℝ × L^q(ℝ³; E)`, `1 ≤ q < ∞`. -/
theorem continuous_dil (hq : q ≠ ∞) :
    Continuous fun p : ℝ × Lp E q (volume : Measure Space) => dil E q p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨s₀, g₀⟩
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hbd : ∀ p : ℝ × Lp E q (volume : Measure Space),
      ‖dil E q p.1 p.2 - dil E q s₀ g₀‖ ≤
        dilConst q p.1 * ‖p.2 - g₀‖ + dilConst q s₀ * ‖dil E q (p.1 - s₀) g₀ - g₀‖ := by
    rintro ⟨s, g⟩
    have e1 : dil E q s g - dil E q s₀ g₀ =
        dil E q s (g - g₀) + dil E q s₀ (dil E q (s - s₀) g₀ - g₀) := by
      rw [map_sub, map_sub, dil_dil, add_sub_cancel]
      abel
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_dil, norm_dil]
  refine squeeze_zero (fun _ => norm_nonneg _) hbd ?_
  have h1 : Tendsto (fun p : ℝ × Lp E q (volume : Measure Space) =>
      dilConst q p.1 * ‖p.2 - g₀‖) (𝓝 (s₀, g₀)) (𝓝 (dilConst q s₀ * 0)) := by
    refine (((continuous_dilConst q).comp continuous_fst).tendsto _).mul ?_
    have hc : Continuous fun p : ℝ × Lp E q (volume : Measure Space) => ‖p.2 - g₀‖ :=
      (continuous_snd.sub continuous_const).norm
    have := hc.tendsto ((s₀, g₀) : ℝ × Lp E q (volume : Measure Space))
    simpa using this
  have h2 : Tendsto (fun p : ℝ × Lp E q (volume : Measure Space) =>
      dilConst q s₀ * ‖dil E q (p.1 - s₀) g₀ - g₀‖) (𝓝 (s₀, g₀)) (𝓝 (dilConst q s₀ * 0)) := by
    refine tendsto_const_nhds.mul ?_
    have hs : Tendsto (fun p : ℝ × Lp E q (volume : Measure Space) => p.1 - s₀)
        (𝓝 (s₀, g₀)) (𝓝 0) := by
      have hc : Continuous fun p : ℝ × Lp E q (volume : Measure Space) => p.1 - s₀ :=
        continuous_fst.sub continuous_const
      have := hc.tendsto ((s₀, g₀) : ℝ × Lp E q (volume : Measure Space))
      simpa using this
    exact (tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_dil_zero hq g₀)).comp hs
  simpa using h1.add h2

theorem continuous_dil_apply (hq : q ≠ ∞) (g : Lp E q (volume : Measure Space)) :
    Continuous fun s => dil E q s g :=
  (continuous_dil hq).comp (continuous_id.prodMk continuous_const)

end UnforcedLeray.PhaseTrace
