import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_3_3
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Analysis.Normed.Group.Continuity

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- Minkowski for a possibly non-measurable `F` against a measurable-in-the-sense-of
`AEStronglyMeasurable` `h` (the lower Lebesgue integral is handled through simple minorants). -/
theorem fl_minkowski {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F h : α → UnforcedLeray.PhaseSpace.CVec3} (hh : AEStronglyMeasurable h μ)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hpt : p ≠ ⊤) :
    eLpNorm F p μ ≤ eLpNorm (F - h) p μ + eLpNorm h p μ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hp'1 : (1 : ℝ) ≤ p.toReal := by
    have := (ENNReal.toReal_le_toReal ENNReal.one_ne_top hpt).2 hp1
    simpa using this
  have hp'0 : 0 < p.toReal := by linarith
  have hBm : AEStronglyMeasurable (fun x => ‖h x‖ₑ) μ := hh.enorm.aestronglyMeasurable
  have hsimple : ∀ s : MeasureTheory.SimpleFunc α ℝ≥0∞, (∀ x, s x ≤ ‖F x‖ₑ ^ p.toReal) →
      s.lintegral μ ≤ (eLpNorm (F - h) p μ + eLpNorm h p μ) ^ p.toReal := by
    intro s hs
    have hφm : Measurable (fun x => s x ^ (p.toReal)⁻¹) := s.measurable.pow_const _
    have hφ_le : ∀ x, s x ^ (p.toReal)⁻¹ ≤ ‖F x‖ₑ := by
      intro x
      calc s x ^ (p.toReal)⁻¹ ≤ (‖F x‖ₑ ^ p.toReal) ^ (p.toReal)⁻¹ :=
            ENNReal.rpow_le_rpow (hs x) (inv_nonneg.2 hp'0.le)
        _ = ‖F x‖ₑ := by
            rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hp'0.ne', ENNReal.rpow_one]
    have hlint : s.lintegral μ = ∫⁻ x, (s x ^ (p.toReal)⁻¹) ^ p.toReal ∂μ := by
      rw [← SimpleFunc.lintegral_eq_lintegral]
      exact lintegral_congr fun x => (ENNReal.rpow_inv_rpow hp'0.ne' (s x)).symm
    have hnorm : eLpNorm (fun x => s x ^ (p.toReal)⁻¹) p μ =
        (∫⁻ x, (s x ^ (p.toReal)⁻¹) ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
      simp
    have hsub : eLpNorm (fun x => s x ^ (p.toReal)⁻¹) p μ ≤
        eLpNorm (fun x => s x ^ (p.toReal)⁻¹ - ‖h x‖ₑ) p μ + eLpNorm h p μ := by
      have hsubm : AEStronglyMeasurable (fun x => s x ^ (p.toReal)⁻¹ - ‖h x‖ₑ) μ :=
        (hφm.aemeasurable.sub hBm.aemeasurable).aestronglyMeasurable
      calc eLpNorm (fun x => s x ^ (p.toReal)⁻¹) p μ
          ≤ eLpNorm ((fun x => s x ^ (p.toReal)⁻¹ - ‖h x‖ₑ) + (fun x => ‖h x‖ₑ)) p μ :=
            eLpNorm_mono_enorm (fun x => by
              simp only [Pi.add_apply, enorm_eq_self]
              exact le_tsub_add)
        _ ≤ eLpNorm (fun x => s x ^ (p.toReal)⁻¹ - ‖h x‖ₑ) p μ +
              eLpNorm (fun x => ‖h x‖ₑ) p μ := eLpNorm_add_le hsubm hBm hp1
        _ = eLpNorm (fun x => s x ^ (p.toReal)⁻¹ - ‖h x‖ₑ) p μ + eLpNorm h p μ := by
            rw [eLpNorm_enorm]
    have hpoint : ∀ x, s x ^ (p.toReal)⁻¹ - ‖h x‖ₑ ≤ ‖(F - h) x‖ₑ := by
      intro x
      have h1 : ‖F x‖ₑ ≤ ‖(F - h) x‖ₑ + ‖h x‖ₑ := by
        have := enorm_add_le ((F - h) x) (h x)
        simpa using this
      exact tsub_le_iff_right.2 ((hφ_le x).trans h1)
    have hφB : eLpNorm (fun x => s x ^ (p.toReal)⁻¹ - ‖h x‖ₑ) p μ ≤ eLpNorm (F - h) p μ :=
      eLpNorm_mono_enorm (fun x => by
        rw [enorm_eq_self]
        exact hpoint x)
    have hX : (s.lintegral μ) ^ (1 / p.toReal) ≤ eLpNorm (F - h) p μ + eLpNorm h p μ := by
      rw [hlint, ← hnorm]
      exact hsub.trans (add_le_add hφB le_rfl)
    calc s.lintegral μ = ((s.lintegral μ) ^ (1 / p.toReal)) ^ p.toReal := by
          rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp'0.ne', ENNReal.rpow_one]
      _ ≤ (eLpNorm (F - h) p μ + eLpNorm h p μ) ^ p.toReal :=
          ENNReal.rpow_le_rpow hX hp'0.le
  have hI : ∫⁻ x, ‖F x‖ₑ ^ p.toReal ∂μ ≤ (eLpNorm (F - h) p μ + eLpNorm h p μ) ^ p.toReal := by
    rw [MeasureTheory.lintegral]
    exact iSup₂_le fun s hs => hsimple s hs
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
  calc (∫⁻ x, ‖F x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal)
      ≤ ((eLpNorm (F - h) p μ + eLpNorm h p μ) ^ p.toReal) ^ (1 / p.toReal) :=
        ENNReal.rpow_le_rpow hI (one_div_nonneg.2 hp'0.le)
    _ = eLpNorm (F - h) p μ + eLpNorm h p μ := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hp'0.ne', ENNReal.rpow_one]

theorem fatouLimit : FatouLimit := by
  intro μ G H g h C hCtop hG hg hh hGg hHh hev
  have hqr : UnforcedLeray.B0412.q0E.toReal = 11 / 4 := UnforcedLeray.B0412.q0E_toReal
  have hsr : ((2 : ℝ≥0∞) * UnforcedLeray.B0412.q0E).toReal = 11 / 2 := by
    rw [ENNReal.toReal_mul, hqr]
    norm_num
  have hq0 : UnforcedLeray.B0412.q0E ≠ 0 :=
    (zero_lt_one.trans UnforcedLeray.B0412.one_lt_q0E).ne'
  have hqtop : UnforcedLeray.B0412.q0E ≠ ⊤ := UnforcedLeray.B0412.q0E_ne_top
  have hq1 : (1 : ℝ≥0∞) ≤ UnforcedLeray.B0412.q0E := UnforcedLeray.B0412.one_lt_q0E.le
  have h2ne : (2 : ℝ≥0∞) * UnforcedLeray.B0412.q0E ≠ 0 := mul_ne_zero two_ne_zero hq0
  have h2top : (2 : ℝ≥0∞) * UnforcedLeray.B0412.q0E ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top hqtop
  have hLtop : eLpNorm h UnforcedLeray.B0412.q0E μ ≠ ⊤ := hh.eLpNorm_lt_top.ne
  have hup : ∀ n, eLpNorm (H n) UnforcedLeray.B0412.q0E μ ≤
      eLpNorm (H n - h) UnforcedLeray.B0412.q0E μ + eLpNorm h UnforcedLeray.B0412.q0E μ :=
    fun n => fl_minkowski hh.aestronglyMeasurable hq1 hqtop
  have hconv : TendstoInMeasure μ G atTop g :=
    tendstoInMeasure_of_tendsto_eLpNorm hq0 hG hg hGg
  obtain ⟨ns, hns, hae⟩ := hconv.exists_seq_tendsto_ae
  have hev' : ∀ᶠ k in atTop, eLpNorm (G (ns k)) (2 * UnforcedLeray.B0412.q0E) μ ^ 2 ≤
      C * eLpNorm (H (ns k)) UnforcedLeray.B0412.q0E μ :=
    hns.tendsto_atTop.eventually hev
  have hdiff : Tendsto (fun k => eLpNorm (H (ns k) - h) UnforcedLeray.B0412.q0E μ) atTop
      (𝓝 0) := hHh.comp hns.tendsto_atTop
  have hu : Tendsto (fun k => eLpNorm (H (ns k) - h) UnforcedLeray.B0412.q0E μ +
      eLpNorm h UnforcedLeray.B0412.q0E μ) atTop
      (𝓝 (eLpNorm h UnforcedLeray.B0412.q0E μ)) := by
    have := hdiff.add (tendsto_const_nhds (x := eLpNorm h UnforcedLeray.B0412.q0E μ))
    simpa only [zero_add] using this
  have hpt : ∀ᵐ x ∂μ, Tendsto (fun k => ‖G (ns k) x‖ₑ ^ (11 / 2 : ℝ)) atTop
      (𝓝 (‖g x‖ₑ ^ (11 / 2 : ℝ))) :=
    hae.mono fun x hx =>
      (ENNReal.continuous_rpow_const.tendsto _).comp ((continuous_enorm.tendsto _).comp hx)
  have hFm : ∀ k, AEMeasurable (fun x => ‖G (ns k) x‖ₑ ^ (11 / 2 : ℝ)) μ :=
    fun k => ((hG (ns k)).aemeasurable.enorm).pow_const _
  have hfatou : ∫⁻ x, ‖g x‖ₑ ^ (11 / 2 : ℝ) ∂μ ≤
      liminf (fun k => ∫⁻ x, ‖G (ns k) x‖ₑ ^ (11 / 2 : ℝ) ∂μ) atTop := by
    calc ∫⁻ x, ‖g x‖ₑ ^ (11 / 2 : ℝ) ∂μ
        = ∫⁻ x, liminf (fun k => ‖G (ns k) x‖ₑ ^ (11 / 2 : ℝ)) atTop ∂μ :=
          lintegral_congr_ae (hpt.mono fun x hx => hx.liminf_eq.symm)
      _ ≤ _ := lintegral_liminf_le' hFm
  have hbd : ∀ᶠ k in atTop, ∫⁻ x, ‖G (ns k) x‖ₑ ^ (11 / 2 : ℝ) ∂μ ≤
      (C * (eLpNorm (H (ns k) - h) UnforcedLeray.B0412.q0E μ +
        eLpNorm h UnforcedLeray.B0412.q0E μ)) ^ (11 / 4 : ℝ) := by
    filter_upwards [hev'] with k hk
    have hI : ∫⁻ x, ‖G (ns k) x‖ₑ ^ (11 / 2 : ℝ) ∂μ =
        eLpNorm (G (ns k)) (2 * UnforcedLeray.B0412.q0E) μ ^ (11 / 2 : ℝ) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2ne h2top, hsr, one_div,
        ENNReal.rpow_inv_rpow (by norm_num : (11 / 2 : ℝ) ≠ 0)]
    calc ∫⁻ x, ‖G (ns k) x‖ₑ ^ (11 / 2 : ℝ) ∂μ
        = eLpNorm (G (ns k)) (2 * UnforcedLeray.B0412.q0E) μ ^ (11 / 2 : ℝ) := hI
      _ = (eLpNorm (G (ns k)) (2 * UnforcedLeray.B0412.q0E) μ ^ (2 : ℕ)) ^ (11 / 4 : ℝ) := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          norm_num
      _ ≤ (C * eLpNorm (H (ns k)) UnforcedLeray.B0412.q0E μ) ^ (11 / 4 : ℝ) :=
          ENNReal.rpow_le_rpow hk (by norm_num)
      _ ≤ (C * (eLpNorm (H (ns k) - h) UnforcedLeray.B0412.q0E μ +
            eLpNorm h UnforcedLeray.B0412.q0E μ)) ^ (11 / 4 : ℝ) :=
          ENNReal.rpow_le_rpow (mul_le_mul' le_rfl (hup (ns k))) (by norm_num)
  have hlim : Tendsto (fun k => (C * (eLpNorm (H (ns k) - h) UnforcedLeray.B0412.q0E μ +
      eLpNorm h UnforcedLeray.B0412.q0E μ)) ^ (11 / 4 : ℝ)) atTop
      (𝓝 ((C * eLpNorm h UnforcedLeray.B0412.q0E μ) ^ (11 / 4 : ℝ))) :=
    (ENNReal.continuous_rpow_const.tendsto _).comp (ENNReal.Tendsto.const_mul hu (Or.inr hCtop))
  have hliminf : liminf (fun k => ∫⁻ x, ‖G (ns k) x‖ₑ ^ (11 / 2 : ℝ) ∂μ) atTop ≤
      (C * eLpNorm h UnforcedLeray.B0412.q0E μ) ^ (11 / 4 : ℝ) := by
    calc liminf (fun k => ∫⁻ x, ‖G (ns k) x‖ₑ ^ (11 / 2 : ℝ) ∂μ) atTop
        ≤ liminf (fun k => (C * (eLpNorm (H (ns k) - h) UnforcedLeray.B0412.q0E μ +
            eLpNorm h UnforcedLeray.B0412.q0E μ)) ^ (11 / 4 : ℝ)) atTop :=
          Filter.liminf_le_liminf hbd
      _ = _ := hlim.liminf_eq
  have hMne : (C * eLpNorm h UnforcedLeray.B0412.q0E μ) ^ (11 / 4 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top hCtop hLtop)
  have hX : ∫⁻ x, ‖g x‖ₑ ^ (11 / 2 : ℝ) ∂μ ≤
      (C * eLpNorm h UnforcedLeray.B0412.q0E μ) ^ (11 / 4 : ℝ) :=
    hfatou.trans hliminf
  have hgL : MemLp g (2 * UnforcedLeray.B0412.q0E) μ := by
    refine ⟨hg, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top h2ne h2top, hsr]
    exact lt_of_le_of_lt hX hMne.lt_top
  refine ⟨hgL, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2ne h2top, hsr, one_div]
  have e4 : ∀ a : ℝ≥0∞, (a ^ ((11 / 2 : ℝ))⁻¹) ^ (2 : ℕ) = a ^ (4 / 11 : ℝ) := by
    intro a
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [e4]
  calc (∫⁻ x, ‖g x‖ₑ ^ (11 / 2 : ℝ) ∂μ) ^ (4 / 11 : ℝ)
      ≤ ((C * eLpNorm h UnforcedLeray.B0412.q0E μ) ^ (11 / 4 : ℝ)) ^ (4 / 11 : ℝ) :=
        ENNReal.rpow_le_rpow hX (by norm_num)
    _ = C * eLpNorm h UnforcedLeray.B0412.q0E μ := by
        rw [← ENNReal.rpow_mul]
        norm_num

end UnforcedLeray.Short.PartIIIb.Concrete
