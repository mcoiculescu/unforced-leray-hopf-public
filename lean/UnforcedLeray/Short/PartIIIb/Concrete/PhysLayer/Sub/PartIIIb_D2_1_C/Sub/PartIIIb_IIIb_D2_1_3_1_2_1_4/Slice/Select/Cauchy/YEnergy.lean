import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3_2_props
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.PairCont

/-!
# `cYEnergy`: the `Y_2` energy bound from the slice bound (source 1351-1362, 1470-1480)

Proof: the squared `Y_2` norm is `P⁻¹` times the phase integral (`phaseLpNorm_eq`); the phase
integral splits into `τ`-slices (`lint_muP_eq`); the slice bound is integrated over `τ ∈ (0,P]`;
Hölder with `p = q = 2` (`ENNReal.lintegral_mul_le_Lp_mul_Lq`) gives the product of the two norms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem cyE_rpow_half_sq (X : ℝ≥0∞) : (X ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = X := by
  rw [← ENNReal.rpow_mul]
  norm_num

theorem cyE_phaseLpNorm_sq (P : ℝ) (k : ℝ × Space → CVec3) (hk : AEStronglyMeasurable k volume) :
    (UnforcedLeray.Short.IIb.phaseLpNorm P 2 k) ^ (2 : ℝ)
      = ENNReal.ofReal P⁻¹ * ∫⁻ z, ‖k z‖ₑ ^ (2 : ℝ) ∂(muP P) := by
  rw [phaseLpNorm_eq P k hk, cyE_rpow_half_sq]

theorem cyE_slice_aemeas {P : ℝ} (k : ℝ × Space → CVec3) (hk : AEStronglyMeasurable k volume) :
    AEMeasurable (fun τ : ℝ => ∫⁻ y : Space, ‖k (τ, y)‖ₑ ^ (2 : ℝ))
      ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)) := by
  have h2 : AEMeasurable (fun z : ℝ × Space => ‖k z‖ₑ ^ (2 : ℝ)) (muP P) :=
    (aesm_muP hk).enorm.pow_const 2
  exact h2.lintegral_prod_right'

theorem cyE_lint_muP_eq {P : ℝ} (k : ℝ × Space → CVec3) (hk : AEStronglyMeasurable k volume) :
    ∫⁻ z, ‖k z‖ₑ ^ (2 : ℝ) ∂(muP P)
      = ∫⁻ τ in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖k (τ, y)‖ₑ ^ (2 : ℝ) := by
  have h2 : AEMeasurable (fun z : ℝ × Space => ‖k z‖ₑ ^ (2 : ℝ)) (muP P) :=
    (aesm_muP hk).enorm.pow_const 2
  exact lintegral_prod _ h2

theorem cyE_holder_slices {P : ℝ} (F G : ℝ → ℝ≥0∞)
    (hF : AEMeasurable F ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)))
    (hG : AEMeasurable G ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P))) :
    ∫⁻ τ in Ioc (0 : ℝ) P, F τ ^ (1 / 2 : ℝ) * G τ ^ (1 / 2 : ℝ)
      ≤ (∫⁻ τ in Ioc (0 : ℝ) P, F τ) ^ (1 / 2 : ℝ) * (∫⁻ τ in Ioc (0 : ℝ) P, G τ) ^ (1 / 2 : ℝ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P))
    hpq (f := fun τ => F τ ^ (1 / 2 : ℝ)) (g := fun τ => G τ ^ (1 / 2 : ℝ))
    (hF.pow_const _) (hG.pow_const _)
  simpa only [Pi.mul_apply, cyE_rpow_half_sq] using h

theorem cYEnergy : CYEnergy := by
  intro P ν hP hν f h g hf hh hg hslice
  have hPpos : (0 : ℝ) < P := hP
  have hp0 : ENNReal.ofReal P⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hPpos)).ne'
  have hpt : ENNReal.ofReal P⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
  -- (1) the sum of squared norms is a phase integral of `∑ⱼ ‖gⱼ‖²`
  have hFsum : ∑ j : Fin 3, ∫⁻ z, ‖g j z‖ₑ ^ (2 : ℝ) ∂(muP P)
      = ∫⁻ τ in Ioc (0 : ℝ) P, ∑ j : Fin 3, ∫⁻ y : Space, ‖g j (τ, y)‖ₑ ^ (2 : ℝ) := by
    calc ∑ j : Fin 3, ∫⁻ z, ‖g j z‖ₑ ^ (2 : ℝ) ∂(muP P)
        = ∑ j : Fin 3, ∫⁻ τ in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖g j (τ, y)‖ₑ ^ (2 : ℝ) :=
          Finset.sum_congr rfl fun j _ => cyE_lint_muP_eq (g j) (hg j).meas
      _ = ∫⁻ τ in Ioc (0 : ℝ) P, ∑ j : Fin 3, ∫⁻ y : Space, ‖g j (τ, y)‖ₑ ^ (2 : ℝ) :=
          (lintegral_finsetSum' Finset.univ
            (f := fun j τ => ∫⁻ y : Space, ‖g j (τ, y)‖ₑ ^ (2 : ℝ))
            fun j _ => cyE_slice_aemeas (P := P) (g j) (hg j).meas).symm
  -- (2) integrate the slice bound over `τ ∈ (0,P]`
  have hbound : ∫⁻ τ in Ioc (0 : ℝ) P, ∑ j : Fin 3, ∫⁻ y : Space, ‖g j (τ, y)‖ₑ ^ (2 : ℝ)
      ≤ ENNReal.ofReal ν⁻¹ * ∫⁻ τ in Ioc (0 : ℝ) P,
          (∫⁻ y : Space, ‖f (τ, y)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
            * (∫⁻ y : Space, ‖h (τ, y)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    calc _ ≤ ∫⁻ τ in Ioc (0 : ℝ) P, ENNReal.ofReal ν⁻¹
            * ((∫⁻ y : Space, ‖f (τ, y)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
              * (∫⁻ y : Space, ‖h (τ, y)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) :=
          lintegral_mono_ae ((ae_restrict_of_ae hslice).mono fun τ hτ => hτ.trans_eq (mul_assoc _ _ _))
      _ = ENNReal.ofReal ν⁻¹ * ∫⁻ τ in Ioc (0 : ℝ) P,
          (∫⁻ y : Space, ‖f (τ, y)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
            * (∫⁻ y : Space, ‖h (τ, y)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- (3) Hölder in `τ`
  have hholder := cyE_holder_slices (P := P)
    (fun τ => ∫⁻ y : Space, ‖f (τ, y)‖ₑ ^ (2 : ℝ))
    (fun τ => ∫⁻ y : Space, ‖h (τ, y)‖ₑ ^ (2 : ℝ))
    (cyE_slice_aemeas (P := P) f hf.meas) (cyE_slice_aemeas (P := P) h hh.meas)
  have hIf := (cyE_lint_muP_eq (P := P) f hf.meas).symm
  have hIh := (cyE_lint_muP_eq (P := P) h hh.meas).symm
  -- (4) combine: `∑ⱼ ∫⁻‖gⱼ‖² ≤ c (If^{1/2} Ih^{1/2})`
  have hS : ∑ j : Fin 3, ∫⁻ z, ‖g j z‖ₑ ^ (2 : ℝ) ∂(muP P)
      ≤ ENNReal.ofReal ν⁻¹ * (((∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) ∂(muP P))) ^ (1 / 2 : ℝ)
          * ((∫⁻ z, ‖h z‖ₑ ^ (2 : ℝ) ∂(muP P))) ^ (1 / 2 : ℝ)) := by
    calc _ = ∫⁻ τ in Ioc (0 : ℝ) P, ∑ j : Fin 3, ∫⁻ y : Space, ‖g j (τ, y)‖ₑ ^ (2 : ℝ) := hFsum
      _ ≤ _ := hbound
      _ ≤ ENNReal.ofReal ν⁻¹ * ((∫⁻ τ in Ioc (0 : ℝ) P, (∫⁻ y : Space, ‖f (τ, y)‖ₑ ^ (2 : ℝ)))
            ^ (1 / 2 : ℝ) * (∫⁻ τ in Ioc (0 : ℝ) P, (∫⁻ y : Space, ‖h (τ, y)‖ₑ ^ (2 : ℝ)))
            ^ (1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hholder zero_le
      _ = _ := by rw [← hIf, ← hIh]
  -- (5) the norms of `f` and `h` factor through `P⁻¹`
  have hpf : UnforcedLeray.Short.IIb.phaseLpNorm P 2 f
      = ENNReal.ofReal P⁻¹ ^ (1 / 2 : ℝ) * (∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) ∂(muP P)) ^ (1 / 2 : ℝ) := by
    rw [phaseLpNorm_eq P f hf.meas, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have hph : UnforcedLeray.Short.IIb.phaseLpNorm P 2 h
      = ENNReal.ofReal P⁻¹ ^ (1 / 2 : ℝ) * (∫⁻ z, ‖h z‖ₑ ^ (2 : ℝ) ∂(muP P)) ^ (1 / 2 : ℝ) := by
    rw [phaseLpNorm_eq P h hh.meas, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have hpp : ENNReal.ofReal P⁻¹ ^ (1 / 2 : ℝ) * ENNReal.ofReal P⁻¹ ^ (1 / 2 : ℝ)
      = ENNReal.ofReal P⁻¹ := by
    rw [← ENNReal.rpow_add _ _ hp0 hpt]
    norm_num
  -- (6) left side as `P⁻¹ ∑ⱼ ∫⁻‖gⱼ‖²`
  have hL : ∑ j : Fin 3, UnforcedLeray.Short.IIb.phaseLpNorm P 2 (g j) ^ (2 : ℝ)
      = ENNReal.ofReal P⁻¹ * ∑ j : Fin 3, ∫⁻ z, ‖g j z‖ₑ ^ (2 : ℝ) ∂(muP P) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => cyE_phaseLpNorm_sq P (g j) (hg j).meas
  rw [hL, hpf, hph]
  calc ENNReal.ofReal P⁻¹ * ∑ j : Fin 3, ∫⁻ z, ‖g j z‖ₑ ^ (2 : ℝ) ∂(muP P)
      ≤ ENNReal.ofReal P⁻¹ * (ENNReal.ofReal ν⁻¹ * ((∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) ∂(muP P)) ^ (1 / 2 : ℝ)
          * (∫⁻ z, ‖h z‖ₑ ^ (2 : ℝ) ∂(muP P)) ^ (1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hS zero_le
    _ = ENNReal.ofReal ν⁻¹ * (ENNReal.ofReal P⁻¹ * ((∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) ∂(muP P)) ^ (1 / 2 : ℝ)
            * (∫⁻ z, ‖h z‖ₑ ^ (2 : ℝ) ∂(muP P)) ^ (1 / 2 : ℝ))) := by
        ring
    _ = ENNReal.ofReal ν⁻¹ * ((ENNReal.ofReal P⁻¹ ^ (1 / 2 : ℝ) * ENNReal.ofReal P⁻¹ ^ (1 / 2 : ℝ))
          * ((∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) ∂(muP P)) ^ (1 / 2 : ℝ)
            * (∫⁻ z, ‖h z‖ₑ ^ (2 : ℝ) ∂(muP P)) ^ (1 / 2 : ℝ))) := by
        rw [hpp]
    _ = ENNReal.ofReal ν⁻¹ * (ENNReal.ofReal P⁻¹ ^ (1 / 2 : ℝ) * (∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) ∂(muP P)) ^ (1 / 2 : ℝ))
          * (ENNReal.ofReal P⁻¹ ^ (1 / 2 : ℝ) * (∫⁻ z, ‖h z‖ₑ ^ (2 : ℝ) ∂(muP P)) ^ (1 / 2 : ℝ)) := by
        ring

end UnforcedLeray.Short.PartIIIb.Concrete
