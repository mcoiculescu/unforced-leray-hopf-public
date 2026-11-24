import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6_1_1_3.NearFar0
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1_2_5

/-!
# `KerBandInt0`: integrability of `K_d(· - y) ψ` against band-supported tests, every `d > 0`

Source: `the November 2 reference manuscript` lines 2117-2121, 3054-3056.
Same proof as `kerBandInt` with `kerNearFar0` (constant depending on `d`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

def KerBandInt0 : Prop :=
  ∀ d : ℝ, 0 < d → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest d ψ → ∀ (y : ℝ × ℝ) (j : Fin 2),
    IntegrableOn (fun x => kerD d (x - y) j * ψ x) (B0579.cell d)

/-- `KerBandInt` for every `d > 0` (constants depend on `d`). -/
theorem kerBandInt0 : KerBandInt0 := by
  intro d hd0 ψ hψ y j
  obtain ⟨C, hC0, hmeas, hper, hodd, hball, hfar⟩ := kerNearFar0 d hd0
  have hcellEq : UnforcedLeray.B0579.cell d = UnforcedLeray.Cyl.cell d := by
    unfold UnforcedLeray.B0579.cell UnforcedLeray.Cyl.cell
    rw [neg_div]
  have hcellMeas : MeasurableSet (UnforcedLeray.B0579.cell d) := by
    unfold UnforcedLeray.B0579.cell
    exact measurableSet_Ico.prod MeasurableSet.univ
  have hψc : Continuous ψ := hψ.continuous
  obtain ⟨R, hR⟩ := hψ.band
  obtain ⟨M, hM⟩ := ((isCompact_Icc : IsCompact (Icc (-(d / 2)) (d / 2)))).prod
    (isCompact_Icc : IsCompact (Icc (-|R|) |R|)) |>.exists_bound_of_continuousOn
      hψc.continuousOn
  obtain ⟨F, hF⟩ : ∃ F : ℝ × ℝ → ℝ≥0∞, ∀ w, F w = ‖kerD d w j‖ₑ *
      (if |w.2 + y.2| ≤ |R| then 1 else 0) := ⟨_, fun w => rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : Set (ℝ × ℝ),
      K = Icc (-(d / 2)) (d / 2) ×ˢ Icc (y.2 - |R|) (y.2 + |R|) := ⟨_, rfl⟩
  have hKmeas : MeasurableSet K := by
    rw [hK]; exact measurableSet_Icc.prod measurableSet_Icc
  have hKfin : volume K < ⊤ := by
    rw [hK]; exact (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  -- periodicity of `F` in the first variable
  have hFper : ∀ w : ℝ × ℝ, F (w.1 + d, w.2) = F w := by
    intro w
    rw [hF, hF]
    simp only [hper]
  have hGper : UnforcedLeray.Cyl.IsPeriodic d (fun w => F (-w)) := by
    intro z
    show F (-(z.1 + d), -z.2) = F (-z.1, -z.2)
    have h := hFper (-z.1 - d, -z.2)
    have e : -z.1 - d + d = -z.1 := by ring
    have e2 : -(z.1 + d) = -z.1 - d := by ring
    rw [e2]
    simp only [e] at h
    exact h.symm
  -- shift to the periodic reflection
  have hshift : ∫⁻ t in UnforcedLeray.B0579.cell d, F (t - y) =
      ∫⁻ t in UnforcedLeray.B0579.cell d, F (-t) := by
    have h := UnforcedLeray.Cyl.lintegral_cell_comp_sub_left hd0 hGper y
    rw [hcellEq]
    simp only [neg_sub] at h
    exact h
  -- pointwise bound by `F`
  have hbound : ∀ t ∈ UnforcedLeray.B0579.cell d,
      ‖kerD d (t - y) j * ψ t‖ₑ ≤ ENNReal.ofReal (max M 0) * F (t - y) := by
    intro t ht
    have ht' := ht
    simp only [UnforcedLeray.B0579.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true] at ht'
    rw [hF]
    by_cases hb : |t.2| ≤ |R|
    · have hind : |(t - y).2 + y.2| ≤ |R| := by
        have e : (t - y).2 + y.2 = t.2 := by simp
        rw [e]; exact hb
      have hψle : ‖ψ t‖ₑ ≤ ENNReal.ofReal (max M 0) := by
        rw [Real.enorm_eq_ofReal_abs]
        apply ENNReal.ofReal_le_ofReal
        have hmem : t ∈ Icc (-(d / 2)) (d / 2) ×ˢ Icc (-|R|) |R| := by
          simp only [Set.mem_prod, Set.mem_Icc]
          exact ⟨⟨ht'.1, ht'.2.le⟩, abs_le.mp hb⟩
        have h1 := hM t hmem
        rw [Real.norm_eq_abs] at h1
        exact h1.trans (le_max_left _ _)
      rw [if_pos hind, mul_one, enorm_mul]
      calc ‖kerD d (t - y) j‖ₑ * ‖ψ t‖ₑ ≤ ‖kerD d (t - y) j‖ₑ * ENNReal.ofReal (max M 0) :=
            mul_le_mul' le_rfl hψle
        _ = ENNReal.ofReal (max M 0) * ‖kerD d (t - y) j‖ₑ := mul_comm _ _
    · have hψt : ψ t = 0 := hR t (lt_of_le_of_lt (le_abs_self R) (not_le.mp hb))
      simp [hψt]
  have hgmeas : AEStronglyMeasurable (fun t => kerD d (t - y) j * ψ t)
      (volume.restrict (UnforcedLeray.B0579.cell d)) := by
    have h1 : Measurable fun t : ℝ × ℝ => kerD d (t - y) j :=
      (hmeas j).comp (measurable_id.sub_const y)
    exact (h1.mul hψc.measurable).aestronglyMeasurable
  -- the far-and-near splitting of `F(-t)` on the cell
  have hsplit : ∀ t ∈ UnforcedLeray.B0579.cell d,
      F (-t) ≤ (Metric.ball (0 : ℝ × ℝ) 1).indicator (fun t => ‖kerD d t j‖ₑ) t +
        K.indicator (fun _ => ENNReal.ofReal C) t := by
    intro t ht
    have ht' := ht
    simp only [UnforcedLeray.B0579.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true] at ht'
    rw [hF]
    by_cases hb : t ∈ Metric.ball (0 : ℝ × ℝ) 1
    · rw [Set.indicator_of_mem hb]
      have hodd' : ‖kerD d (-t) j‖ₑ = ‖kerD d t j‖ₑ := by rw [hodd t j, enorm_neg]
      calc ‖kerD d (-t) j‖ₑ * (if |(-t).2 + y.2| ≤ |R| then 1 else 0)
            ≤ ‖kerD d (-t) j‖ₑ := mul_le_of_le_one_right' (by split_ifs <;> simp)
        _ = ‖kerD d t j‖ₑ := hodd'
        _ ≤ _ := le_self_add
    · rw [Set.indicator_of_notMem hb, zero_add]
      by_cases hc : |(-t).2 + y.2| ≤ |R|
      · have htK : t ∈ K := by
          rw [hK]
          have h := abs_le.mp hc
          simp only [Prod.snd_neg] at h
          exact Set.mk_mem_prod ⟨ht'.1, ht'.2.le⟩ ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩
        rw [Set.indicator_of_mem htK, if_pos hc, mul_one, hodd t j, enorm_neg,
          Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (hfar t ht hb j)
      · rw [if_neg hc, mul_zero]
        exact zero_le
  -- finiteness of the integral of `F(-t)` over the cell
  have hFint : ∫⁻ t in UnforcedLeray.B0579.cell d, F (-t) < ⊤ := by
    have hBm : Measurable ((Metric.ball (0 : ℝ × ℝ) 1).indicator (fun t => ‖kerD d t j‖ₑ)) :=
      ((hmeas j).enorm).indicator measurableSet_ball
    have h1 : ∫⁻ t in UnforcedLeray.B0579.cell d,
        (Metric.ball (0 : ℝ × ℝ) 1).indicator (fun t => ‖kerD d t j‖ₑ) t ≠ ⊤ := by
      refine ne_of_lt (lt_of_le_of_lt (?_ : _ ≤ ENNReal.ofReal C) ENNReal.ofReal_lt_top)
      rw [setLIntegral_indicator measurableSet_ball]
      calc ∫⁻ a in Metric.ball (0 : ℝ × ℝ) 1 ∩ UnforcedLeray.B0579.cell d, ‖kerD d a j‖ₑ
          ≤ ∫⁻ a in Metric.ball (0 : ℝ × ℝ) 1 ∩ UnforcedLeray.B0579.cell d,
              ∑ j', ‖kerD d a j'‖ₑ :=
            setLIntegral_mono' (measurableSet_ball.inter hcellMeas) (fun a _ =>
              Finset.single_le_sum (f := fun j' => ‖kerD d a j'‖ₑ) (fun _ _ => zero_le)
                (Finset.mem_univ j))
        _ = ∫⁻ a in UnforcedLeray.B0579.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1,
              ∑ j', ‖kerD d a j'‖ₑ := by rw [Set.inter_comm]
        _ ≤ ENNReal.ofReal C := hball
    have h2 : ∫⁻ t in UnforcedLeray.B0579.cell d, K.indicator (fun _ => ENNReal.ofReal C) t ≠ ⊤ := by
      rw [setLIntegral_indicator hKmeas, setLIntegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ne_top_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hKfin))
    calc ∫⁻ t in UnforcedLeray.B0579.cell d, F (-t)
        ≤ ∫⁻ t in UnforcedLeray.B0579.cell d,
            ((Metric.ball (0 : ℝ × ℝ) 1).indicator (fun t => ‖kerD d t j‖ₑ) t +
              K.indicator (fun _ => ENNReal.ofReal C) t) :=
          setLIntegral_mono' hcellMeas hsplit
      _ = (∫⁻ t in UnforcedLeray.B0579.cell d,
            (Metric.ball (0 : ℝ × ℝ) 1).indicator (fun t => ‖kerD d t j‖ₑ) t) +
          (∫⁻ t in UnforcedLeray.B0579.cell d,
            K.indicator (fun _ => ENNReal.ofReal C) t) :=
          lintegral_add_left hBm _
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 h1, lt_top_iff_ne_top.2 h2⟩
  refine ⟨hgmeas, hasFiniteIntegral_iff_enorm.2 ?_⟩
  calc ∫⁻ t in UnforcedLeray.B0579.cell d, ‖kerD d (t - y) j * ψ t‖ₑ
      ≤ ∫⁻ t in UnforcedLeray.B0579.cell d, ENNReal.ofReal (max M 0) * F (t - y) :=
        setLIntegral_mono' hcellMeas hbound
    _ = ENNReal.ofReal (max M 0) * ∫⁻ t in UnforcedLeray.B0579.cell d, F (t - y) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (max M 0) * ∫⁻ t in UnforcedLeray.B0579.cell d, F (-t) := by
        rw [hshift]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFint

end UnforcedLeray.Short.IIIa
