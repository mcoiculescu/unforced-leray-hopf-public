import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_2_2_loc.PlanarDil
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Density of smooth fields vanishing near two vertical lines (helper for `relB4loc_leaf`)

Source: `the November 2 reference manuscript` lines 2960-2970 ("Density extends the
convergence").  Smooth compactly supported fields vanishing near the lines `|Re z| = d₀/2` are dense
in `L²_m`: approximate by smooth compactly supported fields, then cut off near the lines (the lines
are null, dominated convergence).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.RelB4locAux

/-- `Φ` vanishes in a neighbourhood of the lines `|Re z| = d₀/2`. -/
def VanishNearLines (d₀ : ℝ) (Φ : ℂ → ℂ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, d₀ / 2 - δ < |z.re| → |z.re| < d₀ / 2 + δ → Φ z = 0

/-- The dense class: smooth compactly supported fields vanishing near the lines `|Re z| = d₀/2`. -/
def denseClass (m d₀ : ℝ) : Set (Planar.L2w m) :=
  {W | ∃ Φ : ℂ → ℂ, ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧ VanishNearLines d₀ Φ ∧
    ⇑W =ᵐ[Planar.wMeasure m] Φ}

/-- The fixed bump `b = 1` on `[-1/2, 1/2]`, `0` outside `(-1, 1)`. -/
def bump0 : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- `ψ = 1 - b`: zero near `0`, one away from `0`. -/
def psi0 (u : ℝ) : ℝ := 1 - bump0 u

theorem contDiff_psi0 : ContDiff ℝ ∞ psi0 := contDiff_const.sub bump0.contDiff

theorem psi0_eq_zero {u : ℝ} (hu : |u| ≤ 1 / 2) : psi0 u = 0 := by
  have : bump0 u = 1 := bump0.one_of_mem_closedBall (by
    rw [mem_closedBall, Real.dist_eq, sub_zero]; exact hu)
  simp [psi0, this]

theorem psi0_eq_one {u : ℝ} (hu : 1 ≤ |u|) : psi0 u = 1 := by
  have : bump0 u = 0 := bump0.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hu)
  simp [psi0, this]

theorem psi0_nonneg (u : ℝ) : 0 ≤ psi0 u := by
  have := bump0.le_one (x := u); simp only [psi0]; linarith

theorem psi0_le_one (u : ℝ) : psi0 u ≤ 1 := by
  have := bump0.nonneg (x := u); simp only [psi0]; linarith

/-- The cutoff `χ_n` vanishing near `x = ±d₀/2`. -/
def chiN (d₀ : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  psi0 ((n + 1) * (x - d₀ / 2)) * psi0 ((n + 1) * (x + d₀ / 2))

theorem contDiff_chiN (d₀ : ℝ) (n : ℕ) : ContDiff ℝ ∞ (chiN d₀ n) :=
  (contDiff_psi0.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))).mul
    (contDiff_psi0.comp (contDiff_const.mul (contDiff_id.add contDiff_const)))

theorem chiN_nonneg (d₀ : ℝ) (n : ℕ) (x : ℝ) : 0 ≤ chiN d₀ n x :=
  mul_nonneg (psi0_nonneg _) (psi0_nonneg _)

theorem chiN_le_one (d₀ : ℝ) (n : ℕ) (x : ℝ) : chiN d₀ n x ≤ 1 :=
  mul_le_one₀ (psi0_le_one _) (psi0_nonneg _) (psi0_le_one _)

/-- The cut-off field. -/
def cutField (d₀ : ℝ) (n : ℕ) (g : ℂ → ℂ) (z : ℂ) : ℂ := (chiN d₀ n z.re : ℂ) * g z

theorem contDiff_cutField (d₀ : ℝ) (n : ℕ) {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (cutField d₀ n g) := by
  have h1 : ContDiff ℝ ∞ (fun z : ℂ => (chiN d₀ n z.re : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_chiN d₀ n).comp Complex.reCLM.contDiff)
  exact h1.mul hg

theorem hasCompactSupport_cutField (d₀ : ℝ) (n : ℕ) {g : ℂ → ℂ} (hg : HasCompactSupport g) :
    HasCompactSupport (cutField d₀ n g) :=
  hg.mul_left (f := fun z : ℂ => (chiN d₀ n z.re : ℂ))

theorem vanish_cutField {d₀ : ℝ} (hd₀ : 0 < d₀) (n : ℕ) (g : ℂ → ℂ) :
    VanishNearLines d₀ (cutField d₀ n g) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  refine ⟨1 / (2 * (n + 1)), by positivity, fun z h1 h2 => ?_⟩
  have hδ : (n + 1 : ℝ) * (1 / (2 * (n + 1))) = 1 / 2 := by field_simp
  have key : chiN d₀ n z.re = 0 := by
    unfold chiN
    rcases le_or_gt 0 z.re with hz | hz
    · rw [abs_of_nonneg hz] at h1 h2
      have : |(n + 1 : ℝ) * (z.re - d₀ / 2)| ≤ 1 / 2 := by
        rw [abs_mul, abs_of_pos hn, ← hδ]
        have : |z.re - d₀ / 2| ≤ 1 / (2 * (n + 1)) := abs_le.2 ⟨by linarith, by linarith⟩
        exact mul_le_mul_of_nonneg_left this hn.le
      rw [psi0_eq_zero this, zero_mul]
    · rw [abs_of_neg hz] at h1 h2
      have : |(n + 1 : ℝ) * (z.re + d₀ / 2)| ≤ 1 / 2 := by
        rw [abs_mul, abs_of_pos hn, ← hδ]
        have : |z.re + d₀ / 2| ≤ 1 / (2 * (n + 1)) := abs_le.2 ⟨by linarith, by linarith⟩
        exact mul_le_mul_of_nonneg_left this hn.le
      rw [psi0_eq_zero this, mul_zero]
  simp [cutField, key]

theorem volume_re_eq (a : ℝ) : volume {z : ℂ | z.re = a} = 0 := by
  have h := BlockPropagatorSub.measurePreserving_cToPlane_volume
  have hs : {z : ℂ | z.re = a} = cToPlane ⁻¹' ({a} ×ˢ univ) := by
    ext z; simp [cToPlane]
  rw [hs, h.measure_preimage ((measurableSet_singleton a).prod MeasurableSet.univ).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

/-- The cut-off fields converge to `g` in `L²_m`. -/
theorem tendsto_cutField {m d₀ : ℝ} {g : ℂ → ℂ} (hgc : Continuous g)
    (hg : MemLp g 2 (Planar.wMeasure m)) :
    Tendsto (fun n : ℕ => eLpNorm (g - cutField d₀ n g) 2 (Planar.wMeasure m)) atTop (𝓝 0) := by
  set μ := Planar.wMeasure m
  have hnull : μ ({z : ℂ | z.re = d₀ / 2} ∪ {z : ℂ | z.re = -(d₀ / 2)}) = 0 :=
    Planar.wMeasure_ac m (measure_union_null (volume_re_eq _) (volume_re_eq _))
  have hlin : Tendsto (fun n : ℕ => ∫⁻ z, ‖(g - cutField d₀ n g) z‖ₑ ^ (2 : ℝ) ∂μ) atTop
      (𝓝 (∫⁻ _z, (0 : ℝ≥0∞) ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun z => ‖g z‖ₑ ^ (2 : ℝ)) ?_ ?_ ?_ ?_
    · intro n
      have hc : Continuous (g - cutField d₀ n g) :=
        hgc.sub ((Complex.continuous_ofReal.comp ((contDiff_chiN d₀ n).continuous.comp
          Complex.continuous_re)).mul hgc)
      exact (ENNReal.continuous_rpow_const.comp hc.enorm).measurable
    · intro n
      refine Eventually.of_forall fun z => ?_
      simp only [Pi.sub_apply, cutField]
      have hfac : g z - (chiN d₀ n z.re : ℂ) * g z = ((1 - chiN d₀ n z.re : ℝ) : ℂ) * g z := by
        push_cast; ring
      rw [hfac]
      gcongr
      rw [enorm_mul]
      have h1 : ‖((1 - chiN d₀ n z.re : ℝ) : ℂ)‖ₑ ≤ 1 := by
        rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith [chiN_le_one d₀ n z.re])]
        exact ENNReal.ofReal_le_one.2 (by linarith [chiN_nonneg d₀ n z.re])
      calc ‖((1 - chiN d₀ n z.re : ℝ) : ℂ)‖ₑ * ‖g z‖ₑ ≤ 1 * ‖g z‖ₑ := by gcongr
        _ = ‖g z‖ₑ := one_mul _
    · exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num) (by norm_num)
        hg.eLpNorm_lt_top).ne
    · rw [ae_iff]
      refine measure_mono_null (fun z hz => ?_) hnull
      simp only [mem_setOf_eq] at hz
      by_contra hne
      simp only [mem_union, mem_setOf_eq, not_or] at hne
      apply hz
      have hpos1 : 0 < |z.re - d₀ / 2| := abs_pos.2 (sub_ne_zero.2 hne.1)
      have hpos2 : 0 < |z.re + d₀ / 2| := abs_pos.2 (by
        intro h; apply hne.2; linarith)
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / min |z.re - d₀ / 2| |z.re + d₀ / 2|)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      have hmin : 0 < min |z.re - d₀ / 2| |z.re + d₀ / 2| := lt_min hpos1 hpos2
      have hn1 : (1 : ℝ) / min |z.re - d₀ / 2| |z.re + d₀ / 2| < n + 1 := by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      have hbig : 1 ≤ (n + 1 : ℝ) * min |z.re - d₀ / 2| |z.re + d₀ / 2| := by
        rw [div_lt_iff₀ hmin] at hn1; linarith
      have hn0 : (0 : ℝ) < n + 1 := by positivity
      have e1 : psi0 ((n + 1) * (z.re - d₀ / 2)) = 1 := psi0_eq_one (by
        rw [abs_mul, abs_of_pos hn0]
        exact hbig.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hn0.le))
      have e2 : psi0 ((n + 1) * (z.re + d₀ / 2)) = 1 := psi0_eq_one (by
        rw [abs_mul, abs_of_pos hn0]
        exact hbig.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hn0.le))
      have hchi : chiN d₀ n z.re = 1 := by rw [chiN, e1, e2, one_mul]
      simp [cutField, hchi]
  rw [lintegral_zero] at hlin
  have hrpow : Tendsto (fun n : ℕ => (∫⁻ z, ‖(g - cutField d₀ n g) z‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)))
      atTop (𝓝 ((0 : ℝ≥0∞) ^ (1 / (2 : ℝ)))) :=
    ((ENNReal.continuous_rpow_const).tendsto _).comp hlin
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hrpow
  refine hrpow.congr (fun n => ?_)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num

/-- **Density** of `denseClass m d₀` in `L²_m`. -/
theorem dense_denseClass (m : ℝ) {d₀ : ℝ} (hd₀ : 0 < d₀) : Dense (denseClass m d₀) := by
  have : IsLocallyFiniteMeasure (Planar.wMeasure m) :=
    inferInstanceAs (IsLocallyFiniteMeasure (B0008.wMeasure m))
  have hS := MeasureTheory.Lp.dense_hasCompactSupport_contDiff (E := ℂ) (F := ℂ) (p := 2)
    (μ := Planar.wMeasure m) (by norm_num)
  rw [Metric.dense_iff] at hS ⊢
  intro F r hr
  obtain ⟨W₁, hW₁F, g, hW₁g, hgc, hgs⟩ := hS F (r / 2) (by positivity)
  have hgm : MemLp g 2 (Planar.wMeasure m) := hgs.continuous.memLp_of_hasCompactSupport hgc
  have hlim := tendsto_cutField (d₀ := d₀) hgs.continuous hgm
  obtain ⟨n, hn⟩ := ((ENNReal.tendsto_nhds_zero.1 hlim) (ENNReal.ofReal (r / 4))
    (by simp; positivity)).exists
  have hcm : MemLp (cutField d₀ n g) 2 (Planar.wMeasure m) :=
    (contDiff_cutField d₀ n hgs).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_cutField d₀ n hgc)
  refine ⟨hcm.toLp _, ?_, ⟨cutField d₀ n g, contDiff_cutField d₀ n hgs,
    hasCompactSupport_cutField d₀ n hgc, vanish_cutField hd₀ n g, hcm.coeFn_toLp⟩⟩
  rw [mem_ball] at hW₁F ⊢
  have hd : dist W₁ (hcm.toLp _) ≤ r / 4 := by
    rw [dist_eq_norm, Lp.norm_def]
    have hae : ⇑(W₁ - hcm.toLp (cutField d₀ n g)) =ᵐ[Planar.wMeasure m] g - cutField d₀ n g := by
      filter_upwards [Lp.coeFn_sub W₁ (hcm.toLp _), hW₁g, hcm.coeFn_toLp] with z h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3, Pi.sub_apply]
    rw [eLpNorm_congr_ae hae]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hn
  calc dist (hcm.toLp _) F ≤ dist (hcm.toLp _) W₁ + dist W₁ F := dist_triangle _ _ _
    _ < r := by rw [dist_comm]; linarith

end UnforcedLeray.Short.IIIa.RelB4locAux
