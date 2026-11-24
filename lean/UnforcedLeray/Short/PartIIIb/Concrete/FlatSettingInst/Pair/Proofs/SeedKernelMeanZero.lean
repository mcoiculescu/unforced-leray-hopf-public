import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Defs
import UnforcedLeray.Short.PartI.StatementsSeed
import UnforcedLeray.Short.PartIIIa.Clock.Frame
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Dynamics.Ergodic.MeasurePreserving

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair

/-- The seed profile is odd under multiplication by `I`: `seedPlanar h (I z) = - seedPlanar h z`. -/
theorem seedPlanarIMul_aux (h : ℝ → ℂ) (z : ℂ) :
    UnforcedLeray.Short.PartI.seedPlanar h (Complex.I * z) =
      -UnforcedLeray.Short.PartI.seedPlanar h z := by
  simp only [UnforcedLeray.Short.PartI.seedPlanar, UnforcedLeray.Planar.NUE.Ang.ofProfile,
    UnforcedLeray.Planar.NUE.Ang.angPhase]
  rw [norm_mul, Complex.norm_I, one_mul, mul_div_assoc, zpow_two, zpow_two]
  linear_combination (h ‖z‖ * (z / ((‖z‖ : ℝ) : ℂ)) * (z / ((‖z‖ : ℝ) : ℂ))) * Complex.I_sq

/-- **The planar growing vectors have zero mass** (source 597). -/
theorem seedKernelMeanZero :
    UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.SeedKernelMeanZero := by
  intro κ hκ k
  obtain ⟨lam, h, hh, ℓ, _, he0, he1, _⟩ := hκ
  let R : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    (MeasurableEquiv.prodComm).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.neg ℝ) (MeasurableEquiv.refl ℝ))
  have hRapp : ∀ y : ℝ × ℝ, R y = (-y.2, y.1) := fun y => rfl
  have h1 : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) (volume : Measure (ℝ × ℝ)) volume := by
    rw [Measure.volume_eq_prod]
    exact Measure.measurePreserving_swap
  have h2 : MeasurePreserving (Prod.map (fun x : ℝ => -x) id)
      (volume : Measure (ℝ × ℝ)) volume := by
    rw [Measure.volume_eq_prod]
    exact (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id _)
  have hRm : MeasurePreserving R volume volume := by
    have hfun : ⇑R = Prod.map (fun x : ℝ => -x) id ∘ Prod.swap := by
      funext y
      rfl
    rw [hfun]
    exact h2.comp h1
  have hplane : ∀ y : ℝ × ℝ,
      UnforcedLeray.Short.IIIa.planeToC (R y) = Complex.I * UnforcedLeray.Short.IIIa.planeToC y := by
    intro y
    rw [hRapp]
    apply Complex.ext <;> simp [UnforcedLeray.Short.IIIa.planeToC]
  have hodd : ∀ y : ℝ × ℝ, κ.e 0 (R y) = -κ.e 0 y := by
    intro y
    rw [he0, he0, hplane, seedPlanarIMul_aux]
  have hint0 : ∫ y, κ.e 0 y = 0 := by
    have hc : ∫ y, κ.e 0 (R y) = ∫ y, κ.e 0 y :=
      hRm.integral_comp' (fun y => κ.e 0 y)
    simp only [hodd, integral_neg] at hc
    linear_combination -hc / 2
  fin_cases k
  · show ∫ y, κ.e 0 y = 0
    exact hint0
  · show ∫ y, κ.e 1 y = 0
    have hc : ∀ y, κ.e 1 y = conj (κ.e 0 y) := fun y => by rw [he1, he0]
    simp only [hc, integral_conj, hint0, map_zero]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair
