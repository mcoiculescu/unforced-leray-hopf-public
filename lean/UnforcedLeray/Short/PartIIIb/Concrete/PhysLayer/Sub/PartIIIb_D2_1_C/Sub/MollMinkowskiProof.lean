import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_3
import UnforcedLeray.Lib.ConvIneq.MinkowskiMixed
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import UnforcedLeray.Short.PartIIb.Tasks.BodyLift.Norm

/-!
# Proof of `MollMinkowski` (source `the November 2 reference manuscript`
lines 1556-1583)

`ρ ⋆ g - g = ∫ ρ_norm(z) (g(· - z) - g) dz` pointwise (for the points where the integral
converges), and Minkowski's integral inequality in the cell `L²((0,P] × ℝ³)` gives the bound.
The cell norm is written through the iterated lintegral `mollIQ`, and the mixed-norm Minkowski
inequality `UnforcedLeray.Conv.mixedNorm_integral_le`-type lintegral form is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

instance instHaarMollRS : (volume : Measure (ℝ × Space)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure volume volume

/-- The iterated cell lintegral `(∫_{(0,P]} ∫_{ℝ³} K² )^{1/2}`; `phaseLpNorm P 2` is
`(P⁻¹)^{1/2}` times this. -/
def MollIQ (P : ℝ) (K : ℝ × Space → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, K (t, y) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

theorem mollIQ_mono {P : ℝ} {K K' : ℝ × Space → ℝ≥0∞} (h : ∀ p, K p ≤ K' p) :
    MollIQ P K ≤ MollIQ P K' := by
  unfold MollIQ
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  apply lintegral_mono
  intro t
  apply lintegral_mono
  intro y
  exact ENNReal.rpow_le_rpow (h _) (by norm_num)

theorem mollIQ_const_mul {P : ℝ} (c : ℝ≥0∞) (hc : c ≠ ⊤) (K : ℝ × Space → ℝ≥0∞) :
    MollIQ P (fun p => c * K p) = c * MollIQ P K := by
  unfold MollIQ
  have hc2 : c ^ (2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hc
  have h1 : ∀ t : ℝ, ∫⁻ y : Space, (c * K (t, y)) ^ (2 : ℝ)
      = c ^ (2 : ℝ) * ∫⁻ y : Space, K (t, y) ^ (2 : ℝ) := by
    intro t
    rw [← lintegral_const_mul' _ _ hc2]
    apply lintegral_congr
    intro y
    exact ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  simp only [h1]
  rw [lintegral_const_mul' _ _ hc2, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ← ENNReal.rpow_mul]
  norm_num

theorem mixed_eq_mollIQ (P : ℝ) (K : ℝ × Space → ℝ≥0∞) :
    eLpNorm (fun τ : ℝ => eLpNorm (fun y : Space => K (τ, y)) 2 (volume : Measure Space)) 2
      ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)) = MollIQ P K := by
  unfold MollIQ
  simp only [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofNat, enorm_eq_self]
  congr 1
  apply lintegral_congr
  intro t
  simp only [← ENNReal.rpow_mul]
  norm_num

theorem phaseLpNorm_two_eq_mollIQ (P : ℝ) (f : ℝ × Space → CVec3) :
    UnforcedLeray.Short.IIb.phaseLpNorm P 2 f =
      ENNReal.ofReal P⁻¹ ^ (1 / 2 : ℝ) * MollIQ P (fun p => ‖f p‖ₑ) := by
  unfold UnforcedLeray.Short.IIb.phaseLpNorm MollIQ
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]

theorem mollP_congr_pt (ρ : ContDiffBump (0 : ℝ × Space)) {g g' : ℝ × Space → CVec3}
    (h : g =ᵐ[volume] g') (x : ℝ × Space) : mollP ρ g x = mollP ρ g' x := by
  unfold mollP
  apply integral_congr_ae
  filter_upwards [(Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae
    (p := fun y => g y = g' y) h] with z hz
  try simp only at hz
  rw [hz]

theorem mollP_stronglyMeasurable_of (ρ : ContDiffBump (0 : ℝ × Space)) {g : ℝ × Space → CVec3}
    (hg : StronglyMeasurable g) : StronglyMeasurable (mollP ρ g) := by
  have hF : StronglyMeasurable (fun q : (ℝ × Space) × (ℝ × Space) =>
      ρ.normed volume q.2 • g (q.1 - q.2)) :=
    (ρ.continuous_normed.measurable.comp measurable_snd).stronglyMeasurable.smul
      (hg.comp_measurable (measurable_fst.sub measurable_snd))
  unfold mollP
  exact hF.integral_prod_right' (ν := volume)

/-- Core inequality for a strongly measurable representative. -/
theorem mollMinkowski_core (P : ℝ) (ρ : ContDiffBump (0 : ℝ × Space))
    (g : ℝ × Space → CVec3) (hg : StronglyMeasurable g) :
    UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => mollP ρ g x - g x) ≤
      ∫⁻ z, ENNReal.ofReal (ρ.normed volume z) *
        UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => g (x - z) - g x) := by
  have hwnn : ∀ z, 0 ≤ ρ.normed volume z := fun z => ρ.nonneg_normed z
  have hwm : Measurable (ρ.normed volume) := ρ.continuous_normed.measurable
  have hwint : Integrable (ρ.normed volume) := ρ.integrable_normed
  have hwone : ∫ z, ρ.normed volume z = 1 := ρ.integral_normed
  have hgm : Measurable g := hg.measurable
  -- pointwise bound
  have S1 : ∀ p, ‖mollP ρ g p - g p‖ₑ ≤
      ∫⁻ z, ENNReal.ofReal (ρ.normed volume z) * ‖g (p - z) - g p‖ₑ := by
    intro p
    by_cases hG : ∫⁻ z, ENNReal.ofReal (ρ.normed volume z) * ‖g (p - z) - g p‖ₑ = ⊤
    · rw [hG]
      exact le_top
    · have hfin : ∫⁻ z, ‖ρ.normed volume z • (g (p - z) - g p)‖ₑ < ⊤ := by
        have hrw : ∀ z, ‖ρ.normed volume z • (g (p - z) - g p)‖ₑ
            = ENNReal.ofReal (ρ.normed volume z) * ‖g (p - z) - g p‖ₑ := by
          intro z
          rw [enorm_smul, Real.enorm_eq_ofReal (hwnn z)]
        simp only [hrw]
        exact lt_top_iff_ne_top.2 hG
      have hm1 : StronglyMeasurable (fun z => g (p - z) - g p) :=
        (hg.comp_measurable (measurable_const.sub measurable_id)).sub stronglyMeasurable_const
      have hmeas : AEStronglyMeasurable (fun z => ρ.normed volume z • (g (p - z) - g p))
          volume :=
        (hwm.stronglyMeasurable.smul hm1).aestronglyMeasurable
      have hint : Integrable (fun z => ρ.normed volume z • (g (p - z) - g p)) volume :=
        ⟨hmeas, hasFiniteIntegral_iff_enorm.2 hfin⟩
      have hc : Integrable (fun z => ρ.normed volume z • g p) volume :=
        hwint.smul_const (g p)
      have hsplit : (fun z => ρ.normed volume z • g (p - z))
          = fun z => ρ.normed volume z • (g (p - z) - g p) + ρ.normed volume z • g p := by
        funext z
        rw [smul_sub, sub_add_cancel]
      have hmol : mollP ρ g p = (∫ z, ρ.normed volume z • (g (p - z) - g p)) + g p := by
        unfold mollP
        rw [hsplit, integral_add hint hc, integral_smul_const, hwone, one_smul]
      rw [hmol, add_sub_cancel_right]
      calc ‖∫ z, ρ.normed volume z • (g (p - z) - g p)‖ₑ
          ≤ ∫⁻ z, ‖ρ.normed volume z • (g (p - z) - g p)‖ₑ :=
            enorm_integral_le_lintegral_enorm _
        _ = ∫⁻ z, ENNReal.ofReal (ρ.normed volume z) * ‖g (p - z) - g p‖ₑ :=
            lintegral_congr fun z => by rw [enorm_smul, Real.enorm_eq_ofReal (hwnn z)]
  -- Minkowski in the cell
  have hmeasF : Measurable fun z : (ℝ × Space) × (ℝ × Space) =>
      ENNReal.ofReal (ρ.normed volume z.1) *
        ‖g ((z.2.1, z.2.2) - z.1) - g (z.2.1, z.2.2)‖ₑ := by
    fun_prop
  have hM := UnforcedLeray.Conv.mixedNorm_lintegral_le
    (μ := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) P))
    (ν := (volume : Measure Space)) (ρ := (volume : Measure (ℝ × Space)))
    (F := fun z τ y => ENNReal.ofReal (ρ.normed volume z) * ‖g ((τ, y) - z) - g (τ, y)‖ₑ)
    hmeasF (q := 2) (a := 2) (by norm_num) ENNReal.ofNat_ne_top (by norm_num) ENNReal.ofNat_ne_top
  have hL : UnforcedLeray.Conv.mixedNorm 2 2 ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P))
      (volume : Measure Space)
      (fun τ y => ∫⁻ z, ENNReal.ofReal (ρ.normed volume z) * ‖g ((τ, y) - z) - g (τ, y)‖ₑ
        ∂(volume : Measure (ℝ × Space)))
      = MollIQ P (fun p => ∫⁻ z, ENNReal.ofReal (ρ.normed volume z) *
          ‖g (p - z) - g p‖ₑ ∂(volume : Measure (ℝ × Space))) :=
    mixed_eq_mollIQ P (fun p => ∫⁻ z, ENNReal.ofReal (ρ.normed volume z) *
          ‖g (p - z) - g p‖ₑ ∂(volume : Measure (ℝ × Space)))
  have hR : ∫⁻ z, UnforcedLeray.Conv.mixedNorm 2 2
      ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)) (volume : Measure Space)
      (fun τ y => ENNReal.ofReal (ρ.normed volume z) * ‖g ((τ, y) - z) - g (τ, y)‖ₑ)
      ∂(volume : Measure (ℝ × Space))
      = ∫⁻ z, ENNReal.ofReal (ρ.normed volume z) *
          MollIQ P (fun p => ‖g (p - z) - g p‖ₑ) := by
    apply lintegral_congr
    intro z
    unfold UnforcedLeray.Conv.mixedNorm
    refine (mixed_eq_mollIQ P (fun p => ENNReal.ofReal (ρ.normed volume z) *
      ‖g (p - z) - g p‖ₑ)).trans ?_
    exact mollIQ_const_mul _ ENNReal.ofReal_ne_top _
  have hG : MollIQ P (fun p => ∫⁻ z, ENNReal.ofReal (ρ.normed volume z) *
      ‖g (p - z) - g p‖ₑ ∂(volume : Measure (ℝ × Space)))
      ≤ ∫⁻ z, ENNReal.ofReal (ρ.normed volume z) *
          MollIQ P (fun p => ‖g (p - z) - g p‖ₑ) := by
    rw [← hL, ← hR]
    exact hM
  have hc : ENNReal.ofReal P⁻¹ ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  rw [phaseLpNorm_two_eq_mollIQ]
  calc ENNReal.ofReal P⁻¹ ^ (1 / 2 : ℝ) * MollIQ P (fun p => ‖mollP ρ g p - g p‖ₑ)
      ≤ ENNReal.ofReal P⁻¹ ^ (1 / 2 : ℝ) * MollIQ P (fun p => ∫⁻ z,
          ENNReal.ofReal (ρ.normed volume z) * ‖g (p - z) - g p‖ₑ
            ∂(volume : Measure (ℝ × Space))) :=
        by gcongr; exact mollIQ_mono S1
    _ ≤ ENNReal.ofReal P⁻¹ ^ (1 / 2 : ℝ) * ∫⁻ z, ENNReal.ofReal (ρ.normed volume z) *
          MollIQ P (fun p => ‖g (p - z) - g p‖ₑ) := by gcongr
    _ = ∫⁻ z, ENNReal.ofReal P⁻¹ ^ (1 / 2 : ℝ) * (ENNReal.ofReal (ρ.normed volume z) *
          MollIQ P (fun p => ‖g (p - z) - g p‖ₑ)) := (lintegral_const_mul' _ _ hc).symm
    _ = ∫⁻ z, ENNReal.ofReal (ρ.normed volume z) *
          (ENNReal.ofReal P⁻¹ ^ (1 / 2 : ℝ) * MollIQ P (fun p => ‖g (p - z) - g p‖ₑ)) := by
        apply lintegral_congr
        intro z
        ring
    _ = ∫⁻ z, ENNReal.ofReal (ρ.normed volume z) *
          UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => g (x - z) - g x) := by
        apply lintegral_congr
        intro z
        rw [phaseLpNorm_two_eq_mollIQ]

theorem mollMinkowski : MollMinkowski := by
  intro P _hP ρ g hg
  have hgsm : StronglyMeasurable (hg.meas.mk g) := hg.meas.stronglyMeasurable_mk
  have hgg : g =ᵐ[volume] hg.meas.mk g := hg.meas.ae_eq_mk
  refine ⟨?_, ?_⟩
  · have hfun : mollP ρ g = mollP ρ (hg.meas.mk g) := funext (mollP_congr_pt ρ hgg)
    rw [hfun]
    exact (mollP_stronglyMeasurable_of ρ hgsm).aestronglyMeasurable
  · have e1 : UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => mollP ρ g x - g x)
        = UnforcedLeray.Short.IIb.phaseLpNorm P 2
            (fun x => mollP ρ (hg.meas.mk g) x - hg.meas.mk g x) := by
      apply UnforcedLeray.Short.IIb.phaseLpNorm_congr_ae'
      filter_upwards [hgg] with x hx
      rw [mollP_congr_pt ρ hgg x, hx]
    have e2 : ∀ z : ℝ × Space, UnforcedLeray.Short.IIb.phaseLpNorm P 2
          (fun x => g (x - z) - g x)
        = UnforcedLeray.Short.IIb.phaseLpNorm P 2
            (fun x => hg.meas.mk g (x - z) - hg.meas.mk g x) := by
      intro z
      apply UnforcedLeray.Short.IIb.phaseLpNorm_congr_ae'
      have hq := (MeasureTheory.measurePreserving_sub_right volume z).quasiMeasurePreserving
      filter_upwards [hq.ae (p := fun y => g y = hg.meas.mk g y) hgg, hgg] with x hx1 hx2
      try simp only at hx1
      rw [hx1, hx2]
    have e3 : ∫⁻ z, ENNReal.ofReal (ρ.normed volume z) *
          UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => g (x - z) - g x)
        = ∫⁻ z, ENNReal.ofReal (ρ.normed volume z) *
          UnforcedLeray.Short.IIb.phaseLpNorm P 2
            (fun x => hg.meas.mk g (x - z) - hg.meas.mk g x) :=
      lintegral_congr fun z => by rw [e2 z]
    rw [e1, e3]
    exact mollMinkowski_core P ρ _ hgsm

end UnforcedLeray.Short.PartIIIb.Concrete
