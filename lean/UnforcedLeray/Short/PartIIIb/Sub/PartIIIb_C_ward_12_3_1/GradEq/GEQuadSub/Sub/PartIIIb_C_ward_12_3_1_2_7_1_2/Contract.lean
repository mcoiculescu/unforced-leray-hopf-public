import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_1_2
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Real.ConjExponents
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Contraction of the `y`-mollification in `L^p(ℝ×ℝ³)` (proof)

Source `the November 2 reference manuscript`
lines 2562-2564 (Minkowski/Jensen in `y'`, translation invariance in `y`).

Route: pointwise `‖spatMol ρ g x‖ₑ ≤ ∫⁻ ρ(y') ‖g(τ,y-y')‖ₑ dy'`; Jensen for the probability
weight `ρ dy'` (ENNReal Hölder); Tonelli and translation invariance; reduction from `g` to a
strongly measurable version by Fubini (a.e. in `τ`, then a.e. in `y'`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal

/-- Hölder step for Jensen with a probability weight, `1 < q`. -/
theorem spatMolC_jensen_aux {α : Type*} [MeasurableSpace α] (μ : Measure α) (q : ℝ) (hq : 1 < q)
    (w a : α → ℝ≥0∞) (hw : Measurable w) (ha : AEMeasurable a μ)
    (hw1 : ∫⁻ x, w x ∂μ = 1) :
    ∫⁻ x, w x * a x ∂μ ≤ (∫⁻ x, w x * a x ^ q ∂μ) ^ (1 / q) := by
  set r : ℝ := q.conjExponent with hr_def
  have hpq : q.HolderConjugate r := Real.HolderConjugate.conjExponent hq
  have hpq' : r.HolderConjugate q := hpq.symm
  have hsum : r⁻¹ + q⁻¹ = 1 := hpq'.inv_add_inv_eq_one
  have hq0 : 0 < q := by linarith
  have hr0 : 0 < r := by
    have h := hpq.conjugate_eq
    rw [h]
    exact div_pos (by linarith) (by linarith)
  have hf_r : ∀ x, (w x ^ r⁻¹) ^ r = w x := fun x => by
    rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hr0.ne', ENNReal.rpow_one]
  have hg_q : ∀ x, (w x ^ q⁻¹ * a x) ^ q = w x * a x ^ q := fun x => by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul, inv_mul_cancel₀ hq0.ne',
      ENNReal.rpow_one]
  have hfg : ∀ x, w x ^ r⁻¹ * (w x ^ q⁻¹ * a x) = w x * a x := fun x => by
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (inv_nonneg.2 hr0.le) (inv_nonneg.2 hq0.le),
      hsum, ENNReal.rpow_one]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq'
    (f := fun x => w x ^ r⁻¹) (g := fun x => w x ^ q⁻¹ * a x)
    (hw.pow_const _).aemeasurable ((hw.pow_const _).aemeasurable.mul ha)
  simp only [Pi.mul_apply, hf_r, hg_q, hfg, hw1, ENNReal.one_rpow, one_mul] at hH
  exact hH

/-- Jensen for a probability weight: `(∫ w a)^q ≤ ∫ w a^q` for `1 ≤ q`. -/
theorem spatMolC_jensen {α : Type*} [MeasurableSpace α] (μ : Measure α) (q : ℝ) (hq : 1 ≤ q)
    (w a : α → ℝ≥0∞) (hw : Measurable w) (ha : AEMeasurable a μ)
    (hw1 : ∫⁻ x, w x ∂μ = 1) :
    (∫⁻ x, w x * a x ∂μ) ^ q ≤ ∫⁻ x, w x * a x ^ q ∂μ := by
  rcases eq_or_lt_of_le hq with h | h
  · rw [← h]
    simp
  · have H := spatMolC_jensen_aux μ q h w a hw ha hw1
    calc (∫⁻ x, w x * a x ∂μ) ^ q ≤ ((∫⁻ x, w x * a x ^ q ∂μ) ^ (1 / q)) ^ q :=
          ENNReal.rpow_le_rpow H (by linarith)
      _ = ∫⁻ x, w x * a x ^ q ∂μ := by
          rw [← ENNReal.rpow_mul, one_div_mul_cancel (by linarith : (0 : ℝ) < q).ne',
            ENNReal.rpow_one]

/-- Translation `(τ, z) ↦ (τ, z - y)` preserves `volume` on `ℝ × ℝ³`. -/
theorem spatMolC_shift_mp (y : UnforcedLeray.Space) :
    MeasurePreserving (fun x : ℝ × UnforcedLeray.Space => (x.1, x.2 - y))
      (volume : Measure (ℝ × UnforcedLeray.Space)) (volume : Measure (ℝ × UnforcedLeray.Space)) := by
  rw [Measure.volume_eq_prod]
  exact (MeasurePreserving.id (volume : Measure ℝ)).prod
    (measurePreserving_sub_right (volume : Measure UnforcedLeray.Space) y)

theorem spatMolC_lintegral_shift (g : ℝ × UnforcedLeray.Space → ℂ) (hg : Measurable g)
    (y : UnforcedLeray.Space) (q : ℝ) :
    ∫⁻ x, ‖g (x.1, x.2 - y)‖ₑ ^ q ∂(volume : Measure (ℝ × UnforcedLeray.Space)) =
      ∫⁻ x, ‖g x‖ₑ ^ q ∂(volume : Measure (ℝ × UnforcedLeray.Space)) :=
  (spatMolC_shift_mp y).lintegral_comp (hg.enorm.pow_const q)

/-- Tonelli in `(x, y')` plus translation invariance: `∫ ∫ w(y') ‖g(τ,y-y')‖^q = ∫ ‖g‖^q`. -/
theorem spatMolC_tonelli (w : UnforcedLeray.Space → ℝ≥0∞) (hw : Measurable w)
    (hw1 : ∫⁻ y, w y ∂(volume : Measure UnforcedLeray.Space) = 1)
    (g : ℝ × UnforcedLeray.Space → ℂ) (hg : Measurable g) (q : ℝ) :
    ∫⁻ x, ∫⁻ y, w y * ‖g (x.1, x.2 - y)‖ₑ ^ q ∂(volume : Measure UnforcedLeray.Space)
        ∂(volume : Measure (ℝ × UnforcedLeray.Space)) =
      ∫⁻ x, ‖g x‖ₑ ^ q ∂(volume : Measure (ℝ × UnforcedLeray.Space)) := by
  have hmeas : Measurable (fun p : (ℝ × UnforcedLeray.Space) × UnforcedLeray.Space =>
      w p.2 * ‖g (p.1.1, p.1.2 - p.2)‖ₑ ^ q) := by
    refine (hw.comp measurable_snd).mul ?_
    refine (hg.comp ?_).enorm.pow_const q
    exact (measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).sub measurable_snd)
  have hsw := lintegral_lintegral_swap
    (μ := (volume : Measure (ℝ × UnforcedLeray.Space)))
    (ν := (volume : Measure UnforcedLeray.Space))
    (f := fun (x : ℝ × UnforcedLeray.Space) (y : UnforcedLeray.Space) =>
      w y * ‖g (x.1, x.2 - y)‖ₑ ^ q)
    hmeas.aemeasurable
  have hm : ∀ y : UnforcedLeray.Space,
      Measurable (fun x : ℝ × UnforcedLeray.Space => ‖g (x.1, x.2 - y)‖ₑ ^ q) := by
    intro y
    refine ((hg.comp ?_).enorm).pow_const q
    exact measurable_fst.prodMk (measurable_snd.sub_const y)
  rw [hsw]
  calc ∫⁻ y, ∫⁻ x, w y * ‖g (x.1, x.2 - y)‖ₑ ^ q ∂(volume : Measure (ℝ × UnforcedLeray.Space))
        ∂(volume : Measure UnforcedLeray.Space)
      = ∫⁻ y, w y * ∫⁻ x, ‖g (x.1, x.2 - y)‖ₑ ^ q ∂(volume : Measure (ℝ × UnforcedLeray.Space))
          ∂(volume : Measure UnforcedLeray.Space) :=
        lintegral_congr fun y => lintegral_const_mul (w y) (hm y)
    _ = ∫⁻ y, w y * ∫⁻ x, ‖g x‖ₑ ^ q ∂(volume : Measure (ℝ × UnforcedLeray.Space))
          ∂(volume : Measure UnforcedLeray.Space) :=
        lintegral_congr fun y => by rw [spatMolC_lintegral_shift g hg y q]
    _ = (∫⁻ y, w y ∂(volume : Measure UnforcedLeray.Space)) *
          ∫⁻ x, ‖g x‖ₑ ^ q ∂(volume : Measure (ℝ × UnforcedLeray.Space)) :=
        lintegral_mul_const _ hw
    _ = ∫⁻ x, ‖g x‖ₑ ^ q ∂(volume : Measure (ℝ × UnforcedLeray.Space)) := by
        rw [hw1, one_mul]

/-- Pointwise bound `‖spatMol ρ g x‖ₑ ≤ ∫⁻ ρ(y) ‖g(τ, z - y)‖ₑ dy` for `ρ ≥ 0`. -/
theorem spatMolC_enorm_le (ρ : UnforcedLeray.Space → ℝ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (g : ℝ × UnforcedLeray.Space → ℂ) (x : ℝ × UnforcedLeray.Space) :
    ‖spatMol ρ g x‖ₑ ≤
      ∫⁻ y, ENNReal.ofReal (ρ y) * ‖g (x.1, x.2 - y)‖ₑ ∂(volume : Measure UnforcedLeray.Space) := by
  show ‖∫ y, (ρ y : ℂ) * g (x.1, x.2 - y)‖ₑ ≤ _
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun y => ?_))
  have hc' : ‖(ρ y : ℂ)‖ₑ = ENNReal.ofReal (ρ y) := by
    rw [← Real.enorm_eq_ofReal (hρ0 y), enorm_eq_nnnorm, enorm_eq_nnnorm, Complex.nnnorm_real]
  rw [enorm_mul, hc']

/-- Core `L^p` contraction for a measurable `g`. -/
theorem spatMolC_core (p : ENNReal) (hp1 : 1 ≤ p) (hpt : p ≠ ⊤)
    (ρ : UnforcedLeray.Space → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ)
    (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∫ y, ρ y = 1)
    (g : ℝ × UnforcedLeray.Space → ℂ) (hg : Measurable g) :
    eLpNorm (spatMol ρ g) p volume ≤ eLpNorm g p volume := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hq1 : (1 : ℝ) ≤ p.toReal := by
    have := ENNReal.toReal_mono hpt hp1
    simpa using this
  have hq0 : (0 : ℝ) < p.toReal := by linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
  refine ENNReal.rpow_le_rpow ?_ (one_div_nonneg.2 hq0.le)
  have hcont : Continuous ρ := hρ.continuous
  have hw : Measurable (fun y => ENNReal.ofReal (ρ y)) :=
    ENNReal.measurable_ofReal.comp hcont.measurable
  have hint : Integrable ρ := hcont.integrable_of_hasCompactSupport hc
  have hw1 : ∫⁻ y, ENNReal.ofReal (ρ y) ∂(volume : Measure UnforcedLeray.Space) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hρ0), hρ1, ENNReal.ofReal_one]
  have hmeas : ∀ x : ℝ × UnforcedLeray.Space,
      Measurable (fun y : UnforcedLeray.Space => ‖g (x.1, x.2 - y)‖ₑ) := by
    intro x
    exact (hg.comp (measurable_const.prodMk (measurable_id.const_sub x.2))).enorm
  calc ∫⁻ x, ‖spatMol ρ g x‖ₑ ^ p.toReal ∂(volume : Measure (ℝ × UnforcedLeray.Space))
      ≤ ∫⁻ x, (∫⁻ y, ENNReal.ofReal (ρ y) * ‖g (x.1, x.2 - y)‖ₑ
          ∂(volume : Measure UnforcedLeray.Space)) ^ p.toReal
          ∂(volume : Measure (ℝ × UnforcedLeray.Space)) :=
        lintegral_mono fun x => ENNReal.rpow_le_rpow (spatMolC_enorm_le ρ hρ0 g x) hq0.le
    _ ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (ρ y) * ‖g (x.1, x.2 - y)‖ₑ ^ p.toReal
          ∂(volume : Measure UnforcedLeray.Space) ∂(volume : Measure (ℝ × UnforcedLeray.Space)) :=
        lintegral_mono fun x => spatMolC_jensen (volume : Measure UnforcedLeray.Space) p.toReal hq1
          (fun y => ENNReal.ofReal (ρ y)) (fun y => ‖g (x.1, x.2 - y)‖ₑ) hw
          (hmeas x).aemeasurable hw1
    _ = ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂(volume : Measure (ℝ × UnforcedLeray.Space)) :=
        spatMolC_tonelli (fun y => ENNReal.ofReal (ρ y)) hw hw1 g hg p.toReal

/-- The `y`-mollification only depends on `g` up to null sets. -/
theorem spatMolC_ae (ρ : UnforcedLeray.Space → ℝ) (g g' : ℝ × UnforcedLeray.Space → ℂ)
    (h : g =ᵐ[volume] g') : spatMol ρ g =ᵐ[volume] spatMol ρ g' := by
  have h2 : ∀ᵐ z ∂((volume : Measure ℝ).prod (volume : Measure UnforcedLeray.Space)),
      g z = g' z := by
    rw [← Measure.volume_eq_prod]
    exact h
  have hτ := Measure.ae_ae_of_ae_prod h2
  have hA : ∀ᵐ τ ∂(volume : Measure ℝ),
      ∀ y : UnforcedLeray.Space, spatMol ρ g (τ, y) = spatMol ρ g' (τ, y) := by
    filter_upwards [hτ] with τ hτ'
    intro y
    have hy : ∀ᵐ y' ∂(volume : Measure UnforcedLeray.Space),
        g (τ, y - y') = g' (τ, y - y') :=
      (Measure.measurePreserving_sub_left (volume : Measure UnforcedLeray.Space) y).quasiMeasurePreserving.ae hτ'
    show ∫ y', (ρ y' : ℂ) * g (τ, y - y') = ∫ y', (ρ y' : ℂ) * g' (τ, y - y')
    refine integral_congr_ae ?_
    filter_upwards [hy] with y' hy'
    rw [hy']
  have hfst : MeasureTheory.Measure.QuasiMeasurePreserving (Prod.fst : ℝ × UnforcedLeray.Space → ℝ)
      ((volume : Measure ℝ).prod (volume : Measure UnforcedLeray.Space)) volume :=
    Measure.quasiMeasurePreserving_fst
  have hF0 : ∀ᵐ x ∂((volume : Measure ℝ).prod (volume : Measure UnforcedLeray.Space)),
      spatMol ρ g x = spatMol ρ g' x := by
    filter_upwards [hfst.ae hA] with x hx
    exact hx x.2
  rw [← Measure.volume_eq_prod] at hF0
  exact hF0

theorem spatMolContract_holds : SpatMolContract := by
  intro p hp1 hpt ρ hρ hc hρ0 hρ1 g hg
  obtain ⟨g', hg'm, hgg'⟩ := hg.aestronglyMeasurable
  have hF : spatMol ρ g =ᵐ[volume] spatMol ρ g' := spatMolC_ae ρ g g' hgg'
  rw [eLpNorm_congr_ae hF, eLpNorm_congr_ae hgg']
  exact spatMolC_core p hp1 hpt ρ hρ hc hρ0 hρ1 g' hg'm.measurable

end UnforcedLeray.Short.PartIIIb.Concrete
