import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_5.Defs

/-!
# `L^p` bound for mollification (`mollify_eLpNorm_le`)

Source `the November 2 reference manuscript` lines 1351-1362, 1470-1480.
Mathlib has no Minkowski integral inequality in the form needed, so the bound is proved by
Jensen (through Hölder) for the probability weight `ρ dz`, Tonelli, and translation invariance.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Jensen for a probability weight `w` on `Space`, `1 ≤ p`, via Hölder. -/
theorem mollify_jensen_lintegral {w h : Space → ℝ≥0∞} (hw : ∫⁻ z, w z = 1)
    (hw_m : Measurable w) (hh : AEMeasurable h volume) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ z, w z * h z) ^ p ≤ ∫⁻ z, w z * h z ^ p := by
  rcases eq_or_lt_of_le hp with hp1 | hp1
  · subst hp1
    simp
  · have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp1
    set q : ℝ := Real.conjExponent p with hq_def
    have hinv : p⁻¹ + q⁻¹ = 1 := hpq.inv_add_inv_eq_one
    have hp0 : p ≠ 0 := (zero_lt_one.trans hp1).ne'
    have hqpos : 0 < q := hpq.symm.pos
    have hq0 : q ≠ 0 := hqpos.ne'
    have hp_nn : (0:ℝ) ≤ 1 / p := one_div_nonneg.2 (zero_lt_one.trans hp1).le
    have hq_nn : (0:ℝ) ≤ 1 / q := one_div_nonneg.2 hqpos.le
    have h1 : 1 / p + 1 / q = 1 := by rw [one_div, one_div]; exact hinv
    have hfg : ∀ z, w z ^ (1 / p) * h z * w z ^ (1 / q) = w z * h z := by
      intro z
      rw [show w z ^ (1 / p) * h z * w z ^ (1 / q) = (w z ^ (1 / p) * w z ^ (1 / q)) * h z by ring,
        ← ENNReal.rpow_add_of_nonneg (1 / p) (1 / q) hp_nn hq_nn, h1, ENNReal.rpow_one]
    have hwp : ∀ z, (w z ^ (1 / p)) ^ p = w z := by
      intro z
      rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0, ENNReal.rpow_one]
    have hwq : ∀ z, (w z ^ (1 / q)) ^ q = w z := by
      intro z
      rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0, ENNReal.rpow_one]
    have hpt : ∀ z, (w z ^ (1 / p) * h z) ^ p = w z * h z ^ p := by
      intro z
      rw [ENNReal.mul_rpow_of_nonneg _ _ (zero_lt_one.trans hp1).le, hwp]
    have hf_m : AEMeasurable (fun z => w z ^ (1 / p) * h z) volume :=
      ((hw_m.pow_const (1 / p)).aemeasurable).mul hh
    have hg_m : AEMeasurable (fun z => w z ^ (1 / q)) volume :=
      (hw_m.pow_const (1 / q)).aemeasurable
    have hH : ∫⁻ z, w z * h z ≤ (∫⁻ z, w z * h z ^ p) ^ (1 / p) * (∫⁻ z, w z) ^ (1 / q) := by
      calc ∫⁻ z, w z * h z
          = ∫⁻ z, ((fun z => w z ^ (1 / p) * h z) * (fun z => w z ^ (1 / q))) z :=
            lintegral_congr fun z => (hfg z).symm
        _ ≤ (∫⁻ z, (fun z => w z ^ (1 / p) * h z) z ^ p) ^ (1 / p)
              * (∫⁻ z, (fun z => w z ^ (1 / q)) z ^ q) ^ (1 / q) :=
            ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq hf_m hg_m
        _ = (∫⁻ z, w z * h z ^ p) ^ (1 / p) * (∫⁻ z, w z) ^ (1 / q) := by
            simp only [hpt, hwq]
    calc (∫⁻ z, w z * h z) ^ p
        ≤ ((∫⁻ z, w z * h z ^ p) ^ (1 / p) * (∫⁻ z, w z) ^ (1 / q)) ^ p :=
          ENNReal.rpow_le_rpow hH (zero_lt_one.trans hp1).le
      _ = ∫⁻ z, w z * h z ^ p := by
          rw [hw, ENNReal.one_rpow, mul_one, ← ENNReal.rpow_mul, one_div_mul_cancel hp0,
            ENNReal.rpow_one]

theorem mollify_eLpNorm_le_sm {ρ : Space → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ) (h0 : ∀ z, 0 ≤ ρ z) (h1 : ∫ z : Space, ρ z = 1) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) {g : Space → CVec3} (hgm : Measurable g) (hg : MemLp g p volume) : MemLp (mollify ρ g) p volume ∧ eLpNorm (mollify ρ g) p volume ≤ eLpNorm g p volume := by
  have hρc : Continuous ρ := hρ.continuous
  have hρint : Integrable ρ volume := hρc.integrable_of_hasCompactSupport hc
  have hw1 : ∫⁻ z, ENNReal.ofReal (ρ z) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hρint (ae_of_all _ h0), h1, ENNReal.ofReal_one]
  have hw_m : Measurable (fun z => ENNReal.ofReal (ρ z)) := hρc.measurable.ennreal_ofReal
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hr1 : (1:ℝ) ≤ p.toReal := by
    have := ENNReal.toReal_mono hpt hp
    simpa using this
  have hgl : LocallyIntegrable g volume := hg.locallyIntegrable hp
  have hconv : mollify ρ g = MeasureTheory.convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext x
    simp [mollify, MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply]
  have hcont : Continuous (mollify ρ g) := by
    rw [hconv]
    exact hc.continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρc hgl
  have hpt_bd : ∀ x, ‖mollify ρ g x‖ₑ ≤ ∫⁻ z, ENNReal.ofReal (ρ z) * ‖g (x - z)‖ₑ := by
    intro x
    unfold mollify
    calc ‖∫ z : Space, ρ z • g (x - z)‖ₑ ≤ ∫⁻ z : Space, ‖ρ z • g (x - z)‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ z : Space, ENNReal.ofReal (ρ z) * ‖g (x - z)‖ₑ := by
          refine lintegral_congr fun z => ?_
          rw [enorm_smul, Real.enorm_eq_ofReal (h0 z)]
  have hmeasx : ∀ x : Space, AEMeasurable (fun z : Space => ‖g (x - z)‖ₑ) volume := by
    intro x
    have hsub : Measurable (fun z : Space => x - z) := measurable_const.sub measurable_id
    exact ((hgm.enorm).comp hsub).aemeasurable
  have hprod : Measurable (fun q : Space × Space => ‖g (q.1 - q.2)‖ₑ ^ p.toReal) :=
    (hgm.enorm.pow_const p.toReal).comp (measurable_fst.sub measurable_snd)
  have hswap : AEMeasurable (Function.uncurry fun (x z : Space) =>
      ENNReal.ofReal (ρ z) * ‖g (x - z)‖ₑ ^ p.toReal) (volume.prod volume) :=
    ((hw_m.comp measurable_snd).mul hprod).aemeasurable
  have hC : ∫⁻ x, ‖mollify ρ g x‖ₑ ^ p.toReal ≤ ∫⁻ x, ‖g x‖ₑ ^ p.toReal := by
    calc ∫⁻ x, ‖mollify ρ g x‖ₑ ^ p.toReal
        ≤ ∫⁻ x, ∫⁻ z, ENNReal.ofReal (ρ z) * ‖g (x - z)‖ₑ ^ p.toReal := by
          refine lintegral_mono fun x => ?_
          exact (ENNReal.rpow_le_rpow (hpt_bd x) (by linarith)).trans
            (mollify_jensen_lintegral hw1 hw_m (hmeasx x) hr1)
      _ = ∫⁻ z, ∫⁻ x, ENNReal.ofReal (ρ z) * ‖g (x - z)‖ₑ ^ p.toReal :=
          lintegral_lintegral_swap hswap
      _ = ∫⁻ z, ENNReal.ofReal (ρ z) * ∫⁻ x, ‖g x‖ₑ ^ p.toReal := by
          refine lintegral_congr fun z => ?_
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          exact lintegral_sub_right_eq_self (fun x => ‖g x‖ₑ ^ p.toReal) z
      _ = (∫⁻ z, ENNReal.ofReal (ρ z)) * ∫⁻ x, ‖g x‖ₑ ^ p.toReal := lintegral_mul_const _ hw_m
      _ = ∫⁻ x, ‖g x‖ₑ ^ p.toReal := by rw [hw1, one_mul]
  have hle : eLpNorm (mollify ρ g) p volume ≤ eLpNorm g p volume := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
    exact ENNReal.rpow_le_rpow hC (one_div_nonneg.2 ENNReal.toReal_nonneg)
  have hmem : MemLp (mollify ρ g) p volume :=
    ⟨hcont.aestronglyMeasurable, lt_of_le_of_lt hle hg.eLpNorm_lt_top⟩
  exact ⟨hmem, hle⟩

theorem mollify_eLpNorm_le {ρ : Space → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ) (h0 : ∀ z, 0 ≤ ρ z) (h1 : ∫ z : Space, ρ z = 1) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) {f : Space → CVec3} (hf : MemLp f p volume) : MemLp (mollify ρ f) p volume ∧ eLpNorm (mollify ρ f) p volume ≤ eLpNorm f p volume := by
  obtain ⟨g, hgm, hfg⟩ : ∃ g : Space → CVec3, Measurable g ∧ f =ᵐ[volume] g :=
    ⟨hf.aestronglyMeasurable.mk f, hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable,
      hf.aestronglyMeasurable.ae_eq_mk⟩
  have hg : MemLp g p volume := hf.ae_eq hfg
  have hmoll : mollify ρ f = mollify ρ g := by
    funext x
    unfold mollify
    refine integral_congr_ae ?_
    have hae : ∀ᵐ z ∂volume, f (x - z) = g (x - z) :=
      (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae hfg
    filter_upwards [hae] with z hz
    simp only [hz]
  have hEq : eLpNorm f p volume = eLpNorm g p volume := eLpNorm_congr_ae hfg
  rw [hmoll, hEq]
  exact mollify_eLpNorm_le_sm hρ hc h0 h1 hp hpt hgm hg

end UnforcedLeray.Short.PartIIIb.Concrete
