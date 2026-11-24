import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_3_3
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

theorem sliceIntegrate : SliceIntegrate := by
  intro hGS P _ W G H M j hM hS hMem hGm hHm
  have hμ : phaseμ P = (volume.restrict (Ioc (0 : ℝ) P)).prod volume := rfl
  have m1 : AEMeasurable (fun x : ℝ × UnforcedLeray.Space =>
      ENNReal.ofReal (‖G x‖ ^ (2 * UnforcedLeray.B0412.q0E.toReal))) (phaseμ P) :=
    ((hGm.norm.aemeasurable).pow_const _).ennreal_ofReal
  have m2 : AEMeasurable (fun x : ℝ × UnforcedLeray.Space =>
      ENNReal.ofReal (‖G x‖ ^ (2 * UnforcedLeray.B0412.q0E.toReal - 2) * ‖H x‖)) (phaseμ P) :=
    (((hGm.norm.aemeasurable).pow_const _).mul hHm.norm.aemeasurable).ennreal_ofReal
  rw [hμ] at m1 m2 ⊢
  have step : ∀ τ : ℝ,
      ∫⁻ y, ENNReal.ofReal (‖G (τ, y)‖ ^ (2 * UnforcedLeray.B0412.q0E.toReal)) ∂volume ≤
        ENNReal.ofReal ((2 * UnforcedLeray.B0412.q0E.toReal - 1) * M) *
          ∫⁻ y, ENNReal.ofReal
            (‖G (τ, y)‖ ^ (2 * UnforcedLeray.B0412.q0E.toReal - 2) * ‖H (τ, y)‖) ∂volume :=
    fun τ => hGS M j (fun y => W (τ, y)) (fun y => G (τ, y)) (fun y => H (τ, y)) hM (hS τ)
      (hMem τ).1 (hMem τ).2
  calc ∫⁻ x, ENNReal.ofReal (‖G x‖ ^ (2 * UnforcedLeray.B0412.q0E.toReal))
        ∂((volume.restrict (Ioc (0 : ℝ) P)).prod volume)
      = ∫⁻ τ, ∫⁻ y, ENNReal.ofReal (‖G (τ, y)‖ ^ (2 * UnforcedLeray.B0412.q0E.toReal)) ∂volume
          ∂(volume.restrict (Ioc (0 : ℝ) P)) := lintegral_prod _ m1
    _ ≤ ∫⁻ τ, ENNReal.ofReal ((2 * UnforcedLeray.B0412.q0E.toReal - 1) * M) *
          ∫⁻ y, ENNReal.ofReal
            (‖G (τ, y)‖ ^ (2 * UnforcedLeray.B0412.q0E.toReal - 2) * ‖H (τ, y)‖) ∂volume
          ∂(volume.restrict (Ioc (0 : ℝ) P)) := lintegral_mono (fun τ => step τ)
    _ = ENNReal.ofReal ((2 * UnforcedLeray.B0412.q0E.toReal - 1) * M) *
          ∫⁻ τ, ∫⁻ y, ENNReal.ofReal
            (‖G (τ, y)‖ ^ (2 * UnforcedLeray.B0412.q0E.toReal - 2) * ‖H (τ, y)‖) ∂volume
          ∂(volume.restrict (Ioc (0 : ℝ) P)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((2 * UnforcedLeray.B0412.q0E.toReal - 1) * M) *
          ∫⁻ x, ENNReal.ofReal
            (‖G x‖ ^ (2 * UnforcedLeray.B0412.q0E.toReal - 2) * ‖H x‖)
            ∂((volume.restrict (Ioc (0 : ℝ) P)).prod volume) := by
        rw [lintegral_prod _ m2]

end UnforcedLeray.Short.PartIIIb.Concrete
