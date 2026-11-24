import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_11_1.Cutoff
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Density of smooth chart tensors in `L²(μ)` (`PartIII-b:IIIb-D2/3/2/11/1`, source 4284-4286, 2666-2700)

`lpSmoothDense_proved : LpSmoothDense`: for `c > 0` and a measure `μ` finite on compacts and null
off `chartDom c`, smooth compactly supported approximants are multiplied by the smooth cutoffs
`ψₙ` of `smoothCutoffExhaustion`, and `‖(1 - ψₙ) G‖_{L²(μ)} → 0` by dominated convergence.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `L²` norm as the square root of the lintegral of the squared norm. -/
theorem lpd_eLpNorm_two (μ : Measure Chart) (k : Chart → Ten3) :
    eLpNorm k 2 μ = (∫⁻ p, ENNReal.ofReal (‖k p‖ ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have key : ∀ p, ‖k p‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖k p‖ ^ 2) := by
    intro p
    rw [ENNReal.rpow_two, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  simp only [ENNReal.toReal_ofNat]
  simp only [key]

theorem lpSmoothDense_proved : LpSmoothDense := by
  intro c hc μ hμ hμ0
  obtain ⟨ψ, hψsm, hψc, hψsupp, hψ01, hψlim⟩ := smoothCutoffExhaustion c hc
  have hD : Dense {f : Lp (α := Chart) Ten3 2 μ |
      ∃ g : Chart → Ten3, f =ᵐ[μ] g ∧ HasCompactSupport g ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g} :=
    MeasureTheory.Lp.dense_hasCompactSupport_contDiff (by norm_num)
  have hae : ∀ᵐ p ∂μ, p ∈ chartDom c := by
    filter_upwards [compl_mem_ae_iff.mpr hμ0] with p hp
    simpa using hp
  intro f
  refine Metric.mem_closure_iff.2 (fun ε hε => ?_)
  obtain ⟨b, ⟨G, hbG, hGc, hGs⟩, hfb⟩ :=
    Metric.mem_closure_iff.1 (hD f) (ε / 2) (half_pos hε)
  -- the cutoff approximants
  have hHsm : ∀ n, IsSmoothChart c (fun p => ψ n p • G p) := by
    intro n
    have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p => ψ n p • G p) :=
      ContDiff.smul (f := ψ n) (g := G) (hψsm n) hGs
    have hsub : tsupport (fun p => ψ n p • G p) ⊆ tsupport (ψ n) :=
      tsupport_smul_subset_left (f := ψ n) (g := G)
    have hcs : HasCompactSupport (fun p => ψ n p • G p) :=
      IsCompact.of_isClosed_subset (hψc n) (isClosed_tsupport _) hsub
    have hts : tsupport (fun p => ψ n p • G p) ⊆ chartDom c := hsub.trans (hψsupp n)
    exact ⟨hsm, hcs, hts⟩
  have hHmem : ∀ n, MemLp (fun p => ψ n p • G p) 2 μ := fun n =>
    ((hHsm n).smooth.continuous).memLp_of_hasCompactSupport (hHsm n).compact
  -- pointwise bound
  have hle : ∀ n p, ‖(1 - ψ n p) • G p‖ ≤ ‖G p‖ := by
    intro n p
    rw [norm_smul, Real.norm_eq_abs]
    have h0 := hψ01 n p
    have h1 : |1 - ψ n p| ≤ 1 := abs_le.2 ⟨by linarith [h0.1, h0.2], by linarith [h0.1, h0.2]⟩
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  -- integrability of the dominating function
  have hint : Integrable (fun p => ‖G p‖ ^ 2) μ := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hGs.continuous.norm).pow 2
    · exact hGc.comp_left (g := fun t : Ten3 => ‖t‖ ^ 2) (by simp)
  have hbound_fin : ∫⁻ p, ENNReal.ofReal (‖G p‖ ^ 2) ∂μ ≠ ⊤ :=
    (hint.lintegral_lt_top).ne
  -- pointwise convergence on the chart domain
  have hpt : ∀ p ∈ chartDom c,
      Tendsto (fun n => ENNReal.ofReal (‖(1 - ψ n p) • G p‖ ^ 2)) atTop (𝓝 0) := by
    intro p hp
    have h1 : Tendsto (fun n => (1 - ψ n p) • G p) atTop (𝓝 0) := by
      have := ((tendsto_const_nhds (x := (1 : ℝ))).sub (hψlim p hp)).smul_const (G p)
      simpa using this
    have h2 : Tendsto (fun n => ‖(1 - ψ n p) • G p‖ ^ 2) atTop (𝓝 0) := by
      have := (h1.norm).pow 2
      simpa using this
    have := ENNReal.tendsto_ofReal h2
    simpa using this
  -- dominated convergence of the lintegrals
  have hI : Tendsto (fun n => ∫⁻ p, ENNReal.ofReal (‖(1 - ψ n p) • G p‖ ^ 2) ∂μ) atTop
      (𝓝 0) := by
    have hmeas : ∀ n, Measurable (fun p => ENNReal.ofReal (‖(1 - ψ n p) • G p‖ ^ 2)) := by
      intro n
      have hc' : Continuous fun p => (1 - ψ n p) • G p :=
        (continuous_const.sub (hψsm n).continuous).smul hGs.continuous
      have hc2 : Continuous fun p => ‖(1 - ψ n p) • G p‖ ^ 2 := (hc'.norm).pow 2
      exact ENNReal.measurable_ofReal.comp hc2.measurable
    have hdom : ∀ᵐ p ∂μ, Tendsto
        (fun n => ENNReal.ofReal (‖(1 - ψ n p) • G p‖ ^ 2)) atTop (𝓝 0) := by
      filter_upwards [hae] with p hp
      exact hpt p hp
    have hlim := tendsto_lintegral_filter_of_dominated_convergence
      (μ := μ) (l := atTop) (F := fun n p => ENNReal.ofReal (‖(1 - ψ n p) • G p‖ ^ 2))
      (f := fun _ => 0) (fun p => ENNReal.ofReal (‖G p‖ ^ 2))
      (Eventually.of_forall fun n => hmeas n)
      (Eventually.of_forall fun n => Eventually.of_forall fun p => by
        apply ENNReal.ofReal_le_ofReal
        exact pow_le_pow_left₀ (norm_nonneg _) (hle n p) 2)
      hbound_fin hdom
    simpa using hlim
  -- L² convergence
  have hKlim : Tendsto (fun n => eLpNorm (fun p => (1 - ψ n p) • G p) 2 μ) atTop (𝓝 0) := by
    have h2 := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto (0 : ℝ≥0∞) |>.comp hI
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h2
    exact Tendsto.congr (fun n => (lpd_eLpNorm_two μ _).symm) h2
  -- the approximants in Lp
  set hbn : ℕ → Lp (α := Chart) Ten3 2 μ :=
    fun n => (hHmem n).toLp (fun p => ψ n p • G p) with hbn_def
  have hdist : ∀ n, dist b (hbn n) = (eLpNorm (fun p => (1 - ψ n p) • G p) 2 μ).toReal := by
    intro n
    rw [Lp.dist_def]
    congr 1
    apply eLpNorm_congr_ae
    filter_upwards [hbG, (hHmem n).coeFn_toLp] with p h1 h2
    simp only [Pi.sub_apply]
    rw [h1, h2, sub_smul, one_smul]
  have hlim2 : Tendsto (fun n => dist b (hbn n)) atTop (𝓝 0) := by
    have h3 := (ENNReal.tendsto_toReal (ENNReal.zero_ne_top)).comp hKlim
    simp only [ENNReal.toReal_zero] at h3
    exact Tendsto.congr (fun n => (hdist n).symm) h3
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim2).2 (ε / 2) (half_pos hε)).exists
  refine ⟨hbn n, ⟨fun p => ψ n p • G p, (hHmem n).coeFn_toLp, hHsm n⟩, ?_⟩
  calc dist f (hbn n) ≤ dist f b + dist b (hbn n) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hfb hn
    _ = ε := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
