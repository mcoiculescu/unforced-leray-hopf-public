import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_4_org_9
import UnforcedLeray.Lib.ConvIneq.MinkowskiMixed
import Mathlib.MeasureTheory.Integral.Prod

/-!
# `phaseMinkowskiSigned`: Minkowski's integral inequality in the phase cell for a signed kernel

Source `the November 2 reference manuscript` lines 1351-1362, 1556-1583.
Same proof as `mollMinkowski` (`MollMinkowskiProof.lean`) with the kernel `ENNReal.ofReal ‖k z‖`
in place of `ρ.normed`, and `F(· - z)` in place of `g(· - z) - g`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Core inequality for a measurable real kernel and a strongly measurable field. -/
theorem phaseMinkowskiCore (P : ℝ) (k : ℝ × Space → ℝ) (hkm : Measurable k)
    (g : ℝ × Space → CVec3) (hg : StronglyMeasurable g) :
    UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => ∫ z, k z • g (x - z)) ≤
      ∫⁻ z, ENNReal.ofReal ‖k z‖ * UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => g (x - z)) := by
  have hgm : Measurable g := hg.measurable
  have S1 : ∀ p, ‖∫ z, k z • g (p - z)‖ₑ ≤
      ∫⁻ z, ENNReal.ofReal ‖k z‖ * ‖g (p - z)‖ₑ := by
    intro p
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun z => ?_
    rw [enorm_smul, ofReal_norm]
  have hmeasF : Measurable fun z : (ℝ × Space) × (ℝ × Space) =>
      ENNReal.ofReal ‖k z.1‖ * ‖g ((z.2.1, z.2.2) - z.1)‖ₑ := by
    fun_prop
  have hM := UnforcedLeray.Conv.mixedNorm_lintegral_le
    (μ := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) P))
    (ν := (volume : Measure Space)) (ρ := (volume : Measure (ℝ × Space)))
    (F := fun z τ y => ENNReal.ofReal ‖k z‖ * ‖g ((τ, y) - z)‖ₑ)
    hmeasF (q := 2) (a := 2) (by norm_num) ENNReal.ofNat_ne_top (by norm_num) ENNReal.ofNat_ne_top
  have hL : UnforcedLeray.Conv.mixedNorm 2 2 ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P))
      (volume : Measure Space)
      (fun τ y => ∫⁻ z, ENNReal.ofReal ‖k z‖ * ‖g ((τ, y) - z)‖ₑ
        ∂(volume : Measure (ℝ × Space)))
      = MollIQ P (fun p => ∫⁻ z, ENNReal.ofReal ‖k z‖ *
          ‖g (p - z)‖ₑ ∂(volume : Measure (ℝ × Space))) :=
    mixed_eq_mollIQ P (fun p => ∫⁻ z, ENNReal.ofReal ‖k z‖ *
          ‖g (p - z)‖ₑ ∂(volume : Measure (ℝ × Space)))
  have hR : ∫⁻ z, UnforcedLeray.Conv.mixedNorm 2 2
      ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)) (volume : Measure Space)
      (fun τ y => ENNReal.ofReal ‖k z‖ * ‖g ((τ, y) - z)‖ₑ)
      ∂(volume : Measure (ℝ × Space))
      = ∫⁻ z, ENNReal.ofReal ‖k z‖ *
          MollIQ P (fun p => ‖g (p - z)‖ₑ) := by
    apply lintegral_congr
    intro z
    unfold UnforcedLeray.Conv.mixedNorm
    refine (mixed_eq_mollIQ P (fun p => ENNReal.ofReal ‖k z‖ *
      ‖g (p - z)‖ₑ)).trans ?_
    exact mollIQ_const_mul _ ENNReal.ofReal_ne_top _
  have hG : MollIQ P (fun p => ∫⁻ z, ENNReal.ofReal ‖k z‖ *
      ‖g (p - z)‖ₑ ∂(volume : Measure (ℝ × Space)))
      ≤ ∫⁻ z, ENNReal.ofReal ‖k z‖ *
          MollIQ P (fun p => ‖g (p - z)‖ₑ) := by
    rw [← hL, ← hR]
    exact hM
  have hc : ENNReal.ofReal P⁻¹ ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  rw [phaseLpNorm_two_eq_mollIQ]
  calc ENNReal.ofReal P⁻¹ ^ (1 / 2 : ℝ) * MollIQ P (fun p => ‖∫ z, k z • g (p - z)‖ₑ)
      ≤ ENNReal.ofReal P⁻¹ ^ (1 / 2 : ℝ) * MollIQ P (fun p => ∫⁻ z,
          ENNReal.ofReal ‖k z‖ * ‖g (p - z)‖ₑ ∂(volume : Measure (ℝ × Space))) :=
        by gcongr; exact mollIQ_mono S1
    _ ≤ ENNReal.ofReal P⁻¹ ^ (1 / 2 : ℝ) * ∫⁻ z, ENNReal.ofReal ‖k z‖ *
          MollIQ P (fun p => ‖g (p - z)‖ₑ) := by gcongr
    _ = ∫⁻ z, ENNReal.ofReal P⁻¹ ^ (1 / 2 : ℝ) * (ENNReal.ofReal ‖k z‖ *
          MollIQ P (fun p => ‖g (p - z)‖ₑ)) := (lintegral_const_mul' _ _ hc).symm
    _ = ∫⁻ z, ENNReal.ofReal ‖k z‖ *
          (ENNReal.ofReal P⁻¹ ^ (1 / 2 : ℝ) * MollIQ P (fun p => ‖g (p - z)‖ₑ)) := by
        apply lintegral_congr
        intro z
        ring
    _ = ∫⁻ z, ENNReal.ofReal ‖k z‖ *
          UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => g (x - z)) := by
        apply lintegral_congr
        intro z
        rw [phaseLpNorm_two_eq_mollIQ]

/-- `PhaseMinkowskiSigned`: the signed Minkowski inequality in the phase cell. -/
theorem phaseMinkowskiSigned : PhaseMinkowskiSigned := by
  intro P _hP k hk F hF
  obtain ⟨g, hgsm, hFg⟩ : ∃ g : ℝ × Space → CVec3, StronglyMeasurable g ∧ F =ᵐ[volume] g :=
    ⟨hF.meas.mk F, hF.meas.stronglyMeasurable_mk, hF.meas.ae_eq_mk⟩
  obtain ⟨k', hksm, hkae⟩ : ∃ k' : ℝ × Space → ℝ, StronglyMeasurable k' ∧ k =ᵐ[volume] k' :=
    ⟨hk.aestronglyMeasurable.mk k, hk.aestronglyMeasurable.stronglyMeasurable_mk,
      hk.aestronglyMeasurable.ae_eq_mk⟩
  have hshift : ∀ x : ℝ × Space, ∀ᵐ z : ℝ × Space, F (x - z) = g (x - z) := fun x =>
    (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae
      (p := fun y => F y = g y) hFg
  have hA : (fun x => ∫ z, k z • F (x - z)) = (fun x => ∫ z, k' z • g (x - z)) := by
    funext x
    apply integral_congr_ae
    filter_upwards [hkae, hshift x] with z hz1 hz2
    rw [hz1, hz2]
  have hB : ∀ z : ℝ × Space, UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => F (x - z))
      = UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => g (x - z)) := fun z =>
    UnforcedLeray.Short.IIb.phaseLpNorm_congr_ae'
      ((measurePreserving_sub_right volume z).quasiMeasurePreserving.ae
        (p := fun y => F y = g y) hFg)
  have hcore := phaseMinkowskiCore P k' hksm.measurable g hgsm
  rw [hA]
  refine hcore.trans (le_of_eq ?_)
  apply lintegral_congr_ae
  filter_upwards [hkae] with z hz
  rw [hz, hB z]

end UnforcedLeray.Short.PartIIIb.Concrete
