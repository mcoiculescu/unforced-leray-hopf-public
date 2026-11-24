import UnforcedLeray.Units.B0220.Chart
import UnforcedLeray.Short.PartIIa.StatementsNear
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Density of smooth compactly supported tensors in `L²(U)` for open `U` (source 1678)

Route: (a) a smooth compactly supported `g` approximates `G` in `L²(U)`; (b) a compact `K ⊆ U`
carries all but a small part of the `L²(U)` mass of `G` (inner regularity of the finite measure
`ν = (vol.restrict U).withDensity ‖G‖²`); (c) a smooth cutoff `χ` with `tsupport χ ⊆ U` and
`χ = 1` on `K`; then `φ = χ • g`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff NNReal Manifold

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.SmoothDense

/-- A smooth cutoff equal to `1` on a compact `K` and supported in the open `U`. -/
theorem exists_cutoff_of_compact (U : Set UnforcedLeray.B0220.Profile) (hU : IsOpen U)
    (K : Set UnforcedLeray.B0220.Profile) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ χ : UnforcedLeray.B0220.Profile → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ U ∧
      (∀ x, χ x ∈ Icc (0:ℝ) 1) ∧ ∀ x ∈ K, χ x = 1 := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hKint : K ⊆ interior (Metric.cthickening δ K) :=
    (Metric.self_subset_thickening hδ K).trans
      (interior_maximal (Metric.thickening_subset_cthickening δ K) Metric.isOpen_thickening)
  obtain ⟨f, h1, h0, hf⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (I := 𝓘(ℝ, UnforcedLeray.B0220.Profile)) (n := (⊤ : ℕ∞)) hK.isClosed hKint
  have hsupp : Function.support (fun x => f x) ⊆ Metric.cthickening δ K :=
    fun x hx => by_contra fun h => hx (h0 x h)
  refine ⟨fun x => f x, contMDiff_iff_contDiff.1 f.contMDiff, ?_, fun x => hf x, ?_⟩
  · exact (closure_minimal hsupp Metric.isClosed_cthickening).trans hδU
  · intro x hx
    exact h1.self_of_nhdsSet x hx

/-- A compact part of `U` captures `L²(U)`-mass up to `δ`. -/
theorem exists_compact_tail (U : Set UnforcedLeray.B0220.Profile) (hU : IsOpen U)
    (G : UnforcedLeray.B0220.Profile → UnforcedLeray.Short.PartIIa.TensorVal)
    (hG : MemLp G 2 (volume.restrict U)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : Set UnforcedLeray.B0220.Profile, K ⊆ U ∧ IsCompact K ∧
      eLpNorm (Kᶜ.indicator G) 2 (volume.restrict U) ≤ ENNReal.ofReal δ := by
  set ν : Measure UnforcedLeray.B0220.Profile :=
    volume.withDensity (U.indicator fun x => ‖G x‖ₑ ^ (2:ℝ)) with hν
  have hfin : ∫⁻ x, ‖G x‖ₑ ^ (2:ℝ) ∂(volume.restrict U) < ⊤ := by
    have := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) two_ne_zero
      (by simp : (2:ℝ≥0∞) ≠ ⊤)).1 hG.2
    simpa using this
  have hνuniv : ν univ = ∫⁻ x, ‖G x‖ₑ ^ (2:ℝ) ∂(volume.restrict U) := by
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_indicator hU.measurableSet]
  have : IsFiniteMeasure ν := ⟨by rw [hνuniv]; exact hfin⟩
  have hνU : ν U = ν univ := by
    rw [hν, withDensity_apply _ hU.measurableSet, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ, setLIntegral_indicator hU.measurableSet,
      lintegral_indicator hU.measurableSet, Set.inter_self]
  have hνtop : ν U ≠ ⊤ := by
    rw [hνU]; exact (measure_lt_top ν univ).ne
  obtain ⟨K, hKU, hKc, hlt⟩ := MeasurableSet.exists_isCompact_lt_add (μ := ν)
    hU.measurableSet hνtop (ENNReal.ofReal_pos.2 (by positivity : (0:ℝ) < δ ^ 2)).ne'
  refine ⟨K, hKU, hKc, ?_⟩
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hKfin : ν K ≠ ⊤ := ne_top_of_le_ne_top hνtop (measure_mono hKU)
  have hcompl : ν Kᶜ + ν K = ν univ := by
    rw [add_comm]; exact measure_add_measure_compl (μ := ν) hKm
  have hlt2 : ν Kᶜ < ENNReal.ofReal (δ ^ 2) := by
    have h3 : ν Kᶜ + ν K < ENNReal.ofReal (δ ^ 2) + ν K := by
      calc ν Kᶜ + ν K = ν univ := hcompl
        _ = ν U := hνU.symm
        _ < ν K + ENNReal.ofReal (δ ^ 2) := hlt
        _ = ENNReal.ofReal (δ ^ 2) + ν K := add_comm _ _
    exact (ENNReal.add_lt_add_iff_right hKfin).1 h3
  have hint : ∫⁻ a, ‖Kᶜ.indicator G a‖ₑ ^ (2:ℝ) ∂(volume.restrict U) = ν Kᶜ := by
    have e1 : ∀ a, ‖Kᶜ.indicator G a‖ₑ ^ (2:ℝ) =
        Kᶜ.indicator (fun x => ‖G x‖ₑ ^ (2:ℝ)) a := by
      intro a
      by_cases h : a ∈ Kᶜ
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h]
    simp_rw [e1]
    rw [lintegral_indicator hKm.compl, hν, withDensity_apply _ hKm.compl,
      setLIntegral_indicator hU.measurableSet, Measure.restrict_restrict hKm.compl, inter_comm]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp : (2:ℝ≥0∞) ≠ ⊤)]
  simp only [ENNReal.toReal_ofNat]
  rw [hint]
  calc ν Kᶜ ^ (1 / (2:ℝ)) ≤ (ENNReal.ofReal (δ ^ 2)) ^ (1 / (2:ℝ)) :=
        ENNReal.rpow_le_rpow hlt2.le (by norm_num)
    _ = ENNReal.ofReal δ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          ← Real.sqrt_eq_rpow, Real.sqrt_sq hδ.le]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.SmoothDense

open UnforcedLeray.Short.PartIIIb.NearInst.Masked.SmoothDense in
/-- **Smooth compactly supported tensors are dense in `L²(U)` for open `U`** (source 1678). -/
theorem smoothCompactDenseOpen (U : Set UnforcedLeray.B0220.Profile) (hU : IsOpen U)
    (G : UnforcedLeray.B0220.Profile → UnforcedLeray.Short.PartIIa.TensorVal)
    (hG : MeasureTheory.MemLp G 2 (MeasureTheory.volume.restrict U)) (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : UnforcedLeray.B0220.Profile → UnforcedLeray.Short.PartIIa.TensorVal,
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U ∧
      MeasureTheory.eLpNorm (G - φ) 2 (MeasureTheory.volume.restrict U) < ENNReal.ofReal ε := by
  have hε4 : (0:ℝ) < ε / 4 := by positivity
  obtain ⟨g, hgc, hgs, hgG⟩ :=
    MeasureTheory.MemLp.exist_eLpNorm_sub_le (by simp : (2:ℝ≥0∞) ≠ ⊤) one_le_two hG hε4
  obtain ⟨K, hKU, hKc, hK⟩ := exists_compact_tail U hU G hG hε4
  obtain ⟨χ, hχs, hχU, hχ01, hχ1⟩ := exists_cutoff_of_compact U hU K hKc hKU
  have hφs : ContDiff ℝ ∞ (fun x => χ x • g x) := hχs.smul hgs
  have hφc : HasCompactSupport (fun x => χ x • g x) :=
    IsCompact.of_isClosed_subset hgc.isCompact (isClosed_tsupport _)
      (tsupport_smul_subset_right χ g)
  have hφU : tsupport (fun x => χ x • g x) ⊆ U := (tsupport_smul_subset_left χ g).trans hχU
  refine ⟨fun x => χ x • g x, hφs, hφc, hφU, ?_⟩
  have hsplit : G - (fun x => χ x • g x) = (G - g) + (fun x => (1 - χ x) • g x) := by
    funext x
    simp only [Pi.sub_apply, Pi.add_apply, sub_smul, one_smul]
    abel
  have hpt : ∀ x, ‖(1 - χ x) • g x‖ ≤ ‖Kᶜ.indicator G x‖ + ‖(G - g) x‖ := by
    intro x
    by_cases hx : x ∈ K
    · simp only [hχ1 x hx, sub_self, zero_smul, norm_zero]
      positivity
    · have hGx : Kᶜ.indicator G x = G x := Set.indicator_of_mem (show x ∈ Kᶜ from hx) G
      rw [hGx]
      have h1 : ‖(1 - χ x) • g x‖ ≤ ‖g x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [(hχ01 x).2])]
        exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [(hχ01 x).1])
      have h2 : ‖g x‖ ≤ ‖G x‖ + ‖(G - g) x‖ := by
        have e : ‖g x‖ = ‖G x - (G - g) x‖ := by
          congr 1; simp [Pi.sub_apply]
        rw [e]; exact norm_sub_le _ _
      linarith
  rw [hsplit]
  have hGgm : AEStronglyMeasurable (G - g) (volume.restrict U) :=
    hG.aestronglyMeasurable.sub hgs.continuous.aestronglyMeasurable
  have hHc : Continuous (fun x => (1 - χ x) • g x) :=
    (continuous_const.sub hχs.continuous).smul hgs.continuous
  have hHm : AEStronglyMeasurable (fun x => (1 - χ x) • g x) (volume.restrict U) :=
    hHc.aestronglyMeasurable
  have hF1m : AEStronglyMeasurable (Kᶜ.indicator G) (volume.restrict U) :=
    hG.aestronglyMeasurable.indicator hKc.isClosed.measurableSet.compl
  have hH : eLpNorm (fun x => (1 - χ x) • g x) 2 (volume.restrict U) ≤
      eLpNorm (Kᶜ.indicator G) 2 (volume.restrict U) + eLpNorm (G - g) 2 (volume.restrict U) := by
    refine (eLpNorm_mono_real hpt).trans ?_
    refine (eLpNorm_add_le hF1m.norm hGgm.norm (by simp : (1:ℝ≥0∞) ≤ 2)).trans ?_
    rw [eLpNorm_norm, eLpNorm_norm]
  have htri := eLpNorm_add_le hGgm hHm (by simp : (1:ℝ≥0∞) ≤ 2)
  calc eLpNorm ((G - g) + fun x => (1 - χ x) • g x) 2 (volume.restrict U)
      ≤ eLpNorm (G - g) 2 (volume.restrict U) +
          eLpNorm (fun x => (1 - χ x) • g x) 2 (volume.restrict U) := htri
    _ ≤ ENNReal.ofReal (ε / 4) + (ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)) :=
        add_le_add hgG (hH.trans (add_le_add hK hgG))
    _ < ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith),
          ← ENNReal.ofReal_add (by linarith) (by linarith),
          ENNReal.ofReal_lt_ofReal_iff hε]
        linarith
