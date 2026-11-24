import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_2_1_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutProps

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace CutRealDU

lemma ladCut_nonneg' (R : ℝ) (x : ℝ × ℝ) : 0 ≤ ladCut R x :=
  Real.smoothTransition.nonneg _

lemma ladCut_le_one' (R : ℝ) (x : ℝ × ℝ) : ladCut R x ≤ 1 :=
  Real.smoothTransition.le_one _

lemma enorm_sq_eq' (z : ℂ) : ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ (2 : ℝ) := by
  rw [ENNReal.ofReal_pow (norm_nonneg z), ofReal_norm_eq_enorm, ENNReal.rpow_two]

lemma jb_nonneg' (x : ℝ × ℝ) : 0 ≤ B0579.jb x := by
  unfold B0579.jb
  positivity

end CutRealDU

open CutRealDU in
/-- **(d) Integrated real bound**: FTC on `[r, s']` for `E_R = cutE0`, the Lower bound (c),
and `E_R(s') ≤ max M 0`, `E_R(r) ≥ 0`. -/
theorem adjCutRateReal (m : ℝ) : AdjCutRateReal m := by
  intro h1 h2 h3 hm ν tr t s G φ hctx M hM
  obtain ⟨hν, hν1, hb, ht, hts, hG, hφ, hj⟩ := id hctx
  obtain ⟨KL, hKL⟩ := h3 ν tr t s G φ hctx M hm hM
  refine ⟨max M 0 + max KL 0 * (s - t), fun R hR r hr s' hs' => ?_⟩
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  obtain ⟨hE, hD, hGk⟩ := h2 ν tr t s G φ hctx R hR0
  have hrs' : r ≤ s' := hs'.1
  have hs'lt : s' < s := hs'.2
  have hrt : t ≤ r := hr.1
  have hsub : Icc r s' ⊆ Ico t s := fun x hx => ⟨le_trans hrt hx.1, lt_of_le_of_lt hx.2 hs'lt⟩
  have hsubO : Ioo r s' ⊆ Ioo t s := fun x hx => ⟨lt_of_le_of_lt hrt hx.1, lt_trans hx.2 hs'lt⟩
  have hs'Icc : s' ∈ Icc t s := ⟨le_trans hrt hrs', hs'lt.le⟩
  -- FTC for the cutoff energy
  have hderiv : ∀ x ∈ Ioo r s', HasDerivAt (cutE0 (ν ^ (-2 : ℝ)) m R φ)
      (cutE0Rate (ν ^ (-2 : ℝ)) m R φ x) x := fun x hx =>
    h1 ν tr t s G φ hctx R hR0 x (hsubO hx)
  have hDint : IntervalIntegrable (cutE0Rate (ν ^ (-2 : ℝ)) m R φ) volume r s' :=
    ContinuousOn.intervalIntegrable_of_Icc hrs' (hD.mono hsub)
  have hFTC : ∫ x in r..s', cutE0Rate (ν ^ (-2 : ℝ)) m R φ x =
      cutE0 (ν ^ (-2 : ℝ)) m R φ s' - cutE0 (ν ^ (-2 : ℝ)) m R φ r :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hrs' (hE.mono hsub) hderiv hDint
  -- nonnegativity at r
  have hEr : 0 ≤ cutE0 (ν ^ (-2 : ℝ)) m R φ r := by
    unfold cutE0
    refine setIntegral_nonneg (B0579.measurableSet_cell _) (fun x _ => ?_)
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (Real.rpow_nonneg (jb_nonneg' x) _) (sq_nonneg _))
  -- uniform upper bound at s'
  have hmem : MemLp (φ s') 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := hφ.memX s' hs'Icc
  have hint : Integrable (fun x => ‖φ s' x‖ ^ 2)
      (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := by
    have h := hmem.integrable_norm_rpow (by norm_num) (by norm_num)
    simpa [Real.rpow_two] using h
  have hbound : ∫ x, ‖φ s' x‖ ^ 2 ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤ max M 0 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg (‖φ s' x‖))
      (hmem.aestronglyMeasurable.norm.pow 2)]
    apply ENNReal.toReal_le_of_le_ofReal (le_max_right M 0)
    have hl := hM s' hs'Icc
    calc ∫⁻ x, ENNReal.ofReal (‖φ s' x‖ ^ 2) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))
        = ∫⁻ x, ‖φ s' x‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
          lintegral_congr fun x => enorm_sq_eq' _
      _ ≤ ENNReal.ofReal M := hl
      _ ≤ ENNReal.ofReal (max M 0) := ENNReal.ofReal_le_ofReal (le_max_left M 0)
  have hEs : cutE0 (ν ^ (-2 : ℝ)) m R φ s' ≤ max M 0 := by
    have hpt : ∀ x, ladCut R x ^ 2 * ‖φ s' x‖ ^ 2 ≤ ‖φ s' x‖ ^ 2 := fun x =>
      mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (ladCut_nonneg' R x) (ladCut_le_one' R x))
    calc cutE0 (ν ^ (-2 : ℝ)) m R φ s'
        = ∫ x, ladCut R x ^ 2 * ‖φ s' x‖ ^ 2 ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := by
          rw [integral_cellMeasure_eq]
          unfold cutE0
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          ring
      _ ≤ ∫ x, ‖φ s' x‖ ^ 2 ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
          integral_mono_of_nonneg
            (ae_of_all _ fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hint (ae_of_all _ hpt)
      _ ≤ max M 0 := hbound
  -- integrating the Lower bound
  have hGI : ∀ k : Fin 2, IntervalIntegrable (cutGReal (ν ^ (-2 : ℝ)) m R φ k) volume r s' :=
    fun k => ContinuousOn.intervalIntegrable_of_Icc hrs' ((hGk k).mono hsub)
  have hSI : IntervalIntegrable (fun x => ∑ k : Fin 2, cutGReal (ν ^ (-2 : ℝ)) m R φ k x)
      volume r s' :=
    ContinuousOn.intervalIntegrable_of_Icc hrs'
      (continuousOn_finset_sum _ fun k _ => (hGk k).mono hsub)
  have hsplit : ∫ x in r..s', (ν * (∑ k : Fin 2, cutGReal (ν ^ (-2 : ℝ)) m R φ k x) - KL) =
      ν * (∑ k : Fin 2, ∫ x in r..s', cutGReal (ν ^ (-2 : ℝ)) m R φ k x) - KL * (s' - r) := by
    rw [intervalIntegral.integral_sub (hSI.const_mul ν) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_finset_sum (fun k _ => hGI k)]
    simp [smul_eq_mul]
    ring
  have hcont_f : ContinuousOn
      (fun x => ν * (∑ k : Fin 2, cutGReal (ν ^ (-2 : ℝ)) m R φ k x) - KL) (Icc r s') :=
    ((continuousOn_const.mul (continuousOn_finset_sum _ fun k _ => (hGk k).mono hsub)).sub
      continuousOn_const)
  have hmono : ∫ x in r..s', (ν * (∑ k : Fin 2, cutGReal (ν ^ (-2 : ℝ)) m R φ k x) - KL) ≤
      ∫ x in r..s', cutE0Rate (ν ^ (-2 : ℝ)) m R φ x := by
    refine intervalIntegral.integral_mono_ae_restrict hrs'
      (ContinuousOn.intervalIntegrable_of_Icc hrs' hcont_f) hDint ?_
    have hae : ∀ᵐ x ∂(volume.restrict (Icc r s')), x ∈ Ioo r s' := by
      rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
      exact ae_restrict_mem measurableSet_Ioo
    refine hae.mono fun x hx => ?_
    exact hKL R hR x ⟨lt_of_le_of_lt hrt hx.1, lt_trans hx.2 hs'lt⟩
  have hfin := hmono.trans_eq hFTC
  rw [hsplit] at hfin
  have hk1 : KL * (s' - r) ≤ max KL 0 * (s' - r) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (sub_nonneg.2 hrs')
  have hk2 : max KL 0 * (s' - r) ≤ max KL 0 * (s - t) :=
    mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _)
  linarith

end UnforcedLeray.Short.IIIa
