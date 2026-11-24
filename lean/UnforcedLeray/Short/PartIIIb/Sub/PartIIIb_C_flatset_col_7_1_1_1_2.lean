import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_1_of
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.SmoothCompactDenseOpen
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# `SFDSmoothApprox` (decomposition of `PartIII-b:C/flatset/col/7/1/1/1/2`)

Source of record `the November 2 reference manuscript` 1678, 1684-1689.
A box-supported `h'` is approximated in the weighted `L²(ageμ c (-3/2))` norm by a `C^∞`
field `F = χ • g`, where `g` is a `C^∞` approximant of `h'` in `L²(ageμ | U)` (Mathlib
`MemLp.exist_eLpNorm_sub_le`) and `χ` is a smooth cutoff, equal to `1` on the box and supported
in an open box `U ⊂ {s > s₀/2} × cell`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (vnorm2 tnorm2)

/-- Weight comparison on `U ⊆ {s ≥ m} × cell`: `ageμ (A ∩ U) ≤ M · vol (A ∩ U)`. -/
theorem sfd_ageμ_inter_le {c a m : ℝ} (hc : 0 < c) (ha : a ≤ 0) (hm : 0 < m)
    (U : Set (ℝ × (ℝ × ℝ))) (hUm : MeasurableSet U)
    (hU : ∀ p ∈ U, m ≤ p.1 ∧ p.2.1 ∈ Ico (-(c / 2)) (c / 2))
    (A : Set (ℝ × (ℝ × ℝ))) (hA : MeasurableSet A) :
    ageμ c a (A ∩ U) ≤ ENNReal.ofReal (c⁻¹ * m ^ a) * volume (A ∩ U) := by
  have hS : MeasurableSet (A ∩ U) := hA.inter hUm
  rw [← lintegral_indicator_one hS, lintegral_ageμ hc a (measurable_one.indicator hS)]
  calc ∫⁻ p in Ioi (0 : ℝ) ×ˢ Cyl.cell c,
        ENNReal.ofReal (c⁻¹ * p.1 ^ a) * (A ∩ U).indicator 1 p
      ≤ ∫⁻ p in Ioi (0 : ℝ) ×ˢ Cyl.cell c,
        ENNReal.ofReal (c⁻¹ * m ^ a) * (A ∩ U).indicator 1 p := by
        refine lintegral_mono fun p => ?_
        by_cases hp : p ∈ A ∩ U
        · have hpU : p ∈ U := hp.2
          have hmp : m ≤ p.1 := (hU p hpU).1
          have h1 : p.1 ^ a ≤ m ^ a := Real.rpow_le_rpow_of_nonpos hm hmp ha
          rw [Set.indicator_of_mem hp, Pi.one_apply, mul_one, mul_one]
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hc.le))
        · simp [hp]
    _ = ENNReal.ofReal (c⁻¹ * m ^ a) * ∫⁻ p in Ioi (0 : ℝ) ×ˢ Cyl.cell c,
        (A ∩ U).indicator 1 p := by
        rw [lintegral_const_mul _ (measurable_one.indicator hS)]
    _ = ENNReal.ofReal (c⁻¹ * m ^ a) * (volume.restrict (Ioi (0 : ℝ) ×ˢ Cyl.cell c)) (A ∩ U) := by
        rw [lintegral_indicator_one hS]
    _ ≤ ENNReal.ofReal (c⁻¹ * m ^ a) * volume (A ∩ U) := by
        gcongr
        exact Measure.restrict_le_self

/-- The restriction of `ageμ` to `U` is finite on compact sets. -/
theorem sfd_restrict_finite {c a m : ℝ} (hc : 0 < c) (ha : a ≤ 0) (hm : 0 < m)
    (U : Set (ℝ × (ℝ × ℝ))) (hUm : MeasurableSet U)
    (hU : ∀ p ∈ U, m ≤ p.1 ∧ p.2.1 ∈ Ico (-(c / 2)) (c / 2)) :
    IsFiniteMeasureOnCompacts ((ageμ c a).restrict U) := by
  refine ⟨fun K hK => ?_⟩
  rw [Measure.restrict_apply hK.isClosed.measurableSet]
  refine lt_of_le_of_lt (sfd_ageμ_inter_le hc ha hm U hUm hU K hK.isClosed.measurableSet) ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    ((measure_mono inter_subset_left).trans_lt hK.measure_lt_top)

/-- **S** Smooth compactly supported approximation of a box-supported field in the weighted `L²`
norm (source 1678, 1684-1689). -/
theorem sfdSmoothApprox : SFDSmoothApprox := by
  intro c s0 s1 a b L hc hs0 ha hb h' hbox ε hε
  obtain ⟨d, hd, hda, hdb⟩ : ∃ d : ℝ, 0 < d ∧ d < a + c / 2 ∧ d < c / 2 - b := by
    have h1 : 0 < a + c / 2 := by linarith
    have h2 : 0 < c / 2 - b := by linarith
    have h3 := lt_min h1 h2
    refine ⟨min (a + c / 2) (c / 2 - b) / 2, half_pos h3, ?_, ?_⟩
    · linarith [min_le_left (a + c / 2) (c / 2 - b)]
    · linarith [min_le_right (a + c / 2) (c / 2 - b)]
  set U : Set (ℝ × (ℝ × ℝ)) :=
    Ioo (s0 / 2) (s1 + 1) ×ˢ (Ioo (a - d) (b + d) ×ˢ Ioo (-L - 1) (L + 1)) with hUdef
  set B : Set (ℝ × (ℝ × ℝ)) := Icc s0 s1 ×ˢ (Icc a b ×ˢ Icc (-L) L) with hBdef
  have hUo : IsOpen U := isOpen_Ioo.prod (isOpen_Ioo.prod isOpen_Ioo)
  have hBc : IsCompact B := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hBU : B ⊆ U := by
    rintro ⟨s, q, η⟩ ⟨hs, hq, hη⟩
    exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩,
      ⟨by linarith [hq.1], by linarith [hq.2]⟩, ⟨by linarith [hη.1], by linarith [hη.2]⟩⟩
  have hUcell : ∀ p ∈ U, s0 / 2 ≤ p.1 ∧ p.2.1 ∈ Ico (-(c / 2)) (c / 2) := by
    rintro ⟨s, q, η⟩ ⟨hs, hq, -⟩
    exact ⟨hs.1.le, ⟨by linarith [hq.1], by linarith [hq.2]⟩⟩
  haveI := sfd_restrict_finite (a := -3 / 2) hc (by norm_num) (half_pos hs0) U hUo.measurableSet
    hUcell
  have hG : MemLp (⇑h' : Chart → EuclideanSpace ℝ (Fin 2)) 2
      ((ageμ c (-3 / 2)).restrict U) := (Lp.memLp h').restrict U
  obtain ⟨g, hgc, hgs, hgG⟩ :=
    MemLp.exist_eLpNorm_sub_le (μ := (ageμ c (-3 / 2)).restrict U) (by simp : (2 : ℝ≥0∞) ≠ ⊤)
      one_le_two hG (half_pos hε)
  obtain ⟨χ, hχs, hχU, hχ01, hχ1⟩ :=
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.SmoothDense.exists_cutoff_of_compact U hUo B hBc
      hBU
  refine ⟨fun p i => χ p * g p i, fun i => hχs.mul ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hgs),
    ⟨s0 / 2, s1 + 1, a - d, b + d, L + 1, half_pos hs0, by linarith, by linarith, ?_⟩, ?_⟩
  · intro p hp
    have hχp : χ p ≠ 0 := by
      intro h0
      apply hp
      funext i
      simp [h0]
    obtain ⟨h1, h2, h3⟩ := hχU (subset_tsupport χ (Function.mem_support.2 hχp))
    exact ⟨⟨h1.1.le, h1.2.le⟩, ⟨h2.1.le, h2.2.le⟩,
      abs_le.2 ⟨by linarith [h3.1], by linarith [h3.2]⟩⟩
  · -- the approximation estimate
    have hpt1 : ∀ p : Chart, vnorm2 (NearInst.velC h' p - fun i => ((χ p * g p i : ℝ) : ℂ)) ^ 2 =
        ‖(⇑h' : Chart → EuclideanSpace ℝ (Fin 2)) p - χ p • g p‖ ^ 2 := by
      intro p
      unfold vnorm2
      rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity), EuclideanSpace.norm_sq_eq]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [NearInst.velC, Pi.sub_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
        ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hvel : ∀ p : Chart, (⇑h' : Chart → EuclideanSpace ℝ (Fin 2)) p ≠ 0 →
        NearInst.velC h' p ≠ 0 := by
      intro p hG0 h0
      apply hG0
      ext i
      have := congrFun h0 i
      simpa [NearInst.velC] using this
    have hB : ∀ᵐ p ∂(ageμ c (-3 / 2)), (⇑h' : Chart → EuclideanSpace ℝ (Fin 2)) p ≠ 0 → p ∈ B := by
      filter_upwards [hbox] with p hp hG0
      obtain ⟨h1, h2, h3⟩ := hp (hvel p hG0)
      exact ⟨h1, h2, abs_le.1 h3⟩
    have hpt : ∀ᵐ p ∂(ageμ c (-3 / 2)),
        ENNReal.ofReal (‖(⇑h' : Chart → EuclideanSpace ℝ (Fin 2)) p - χ p • g p‖ ^ 2) ≤
          U.indicator (fun p => ENNReal.ofReal (‖(⇑h' : Chart → EuclideanSpace ℝ (Fin 2)) p
            - g p‖ ^ 2)) p := by
      filter_upwards [hB] with p hpB'
      by_cases hpB : p ∈ B
      · have hpU : p ∈ U := hBU hpB
        rw [Set.indicator_of_mem hpU, hχ1 p hpB, one_smul]
      · have hG0 : (⇑h' : Chart → EuclideanSpace ℝ (Fin 2)) p = 0 := by
          by_contra hne
          exact hpB (hpB' hne)
        by_cases hpU : p ∈ U
        · rw [Set.indicator_of_mem hpU, hG0]
          apply ENNReal.ofReal_le_ofReal
          have hχ0 := hχ01 p
          rw [zero_sub, zero_sub, norm_neg, norm_neg, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg hχ0.1]
          have hn := norm_nonneg (g p)
          have h1 : χ p * ‖g p‖ ≤ ‖g p‖ := mul_le_of_le_one_left hn hχ0.2
          exact pow_le_pow_left₀ (mul_nonneg hχ0.1 hn) h1 2
        · rw [Set.indicator_of_notMem hpU]
          have hχz : χ p = 0 := by
            by_contra hne
            exact hpU (hχU (subset_tsupport χ (Function.mem_support.2 hne)))
          simp [hχz, hG0]
    have e1 : ∀ p : Chart, ENNReal.ofReal (‖((⇑h' : Chart → EuclideanSpace ℝ (Fin 2)) - g) p‖ ^ 2)
        = ‖((⇑h' : Chart → EuclideanSpace ℝ (Fin 2)) - g) p‖ₑ ^ (2 : ℝ) := by
      intro p
      rw [ENNReal.rpow_two, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
    have e2 := eLpNorm_nnreal_pow_eq_lintegral (μ := (ageμ c (-3 / 2)).restrict U)
      (f := (⇑h' : Chart → EuclideanSpace ℝ (Fin 2)) - g) (p := 2) (by norm_num)
    simp only [ENNReal.coe_ofNat, NNReal.coe_ofNat] at e2
    have hX : ∫⁻ p, ENNReal.ofReal (‖((⇑h' : Chart → EuclideanSpace ℝ (Fin 2)) - g) p‖ ^ 2)
        ∂((ageμ c (-3 / 2)).restrict U) ≤ ENNReal.ofReal ((ε / 2) ^ 2) := by
      rw [lintegral_congr e1, ← e2]
      calc eLpNorm ((⇑h' : Chart → EuclideanSpace ℝ (Fin 2)) - g) 2 ((ageμ c (-3 / 2)).restrict U) ^
            (2 : ℝ)
          ≤ ENNReal.ofReal (ε / 2) ^ (2 : ℝ) := ENNReal.rpow_le_rpow hgG (by norm_num)
        _ = ENNReal.ofReal ((ε / 2) ^ 2) := by
          rw [ENNReal.rpow_two, ENNReal.ofReal_pow (half_pos hε).le]
    calc ∫⁻ p, ENNReal.ofReal (vnorm2 (NearInst.velC h' p - fun i => ((χ p * g p i : ℝ) : ℂ)) ^ 2)
          ∂(ageμ c (-3 / 2))
        = ∫⁻ p, ENNReal.ofReal (‖(⇑h' : Chart → EuclideanSpace ℝ (Fin 2)) p - χ p • g p‖ ^ 2)
          ∂(ageμ c (-3 / 2)) := lintegral_congr fun p => by rw [hpt1 p]
      _ ≤ ∫⁻ p, U.indicator (fun p => ENNReal.ofReal (‖(⇑h' : Chart → EuclideanSpace ℝ (Fin 2)) p
            - g p‖ ^ 2)) p ∂(ageμ c (-3 / 2)) := lintegral_mono_ae hpt
      _ = ∫⁻ p in U, ENNReal.ofReal (‖(⇑h' : Chart → EuclideanSpace ℝ (Fin 2)) p - g p‖ ^ 2)
          ∂(ageμ c (-3 / 2)) := lintegral_indicator hUo.measurableSet _
      _ ≤ ENNReal.ofReal ((ε / 2) ^ 2) := hX
      _ < ENNReal.ofReal (ε ^ 2) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by nlinarith)


end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
