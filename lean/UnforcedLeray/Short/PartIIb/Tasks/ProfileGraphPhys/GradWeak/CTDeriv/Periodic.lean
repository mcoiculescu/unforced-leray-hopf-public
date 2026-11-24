import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_2

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

/-- The phase period `P = 2εc` shifts the chart phase `ξ = Rτ/2 - (R/2) log s` (`R = ε⁻¹`) by `c`. -/
theorem phase_period_shift {c ε : ℝ} (hε : 0 < ε) (τ : ℝ) (y : Space) :
    Axi.phase ε⁻¹ (τ + 2 * ε * c) y = Axi.phase ε⁻¹ τ y + c :=
  Axi.phase_shift (inv_ne_zero hε.ne') (by field_simp) τ y

/-- `ctLift` is periodic in the phase variable `τ` with period `P = 2εc`. -/
theorem ctLift_periodic (c ε a : ℝ) (hε : 0 < ε) (φ : Coord → ℝ) (x : ℝ × Space) :
    ctLift c ε a φ (x.1 + 2 * ε * c, x.2) = ctLift c ε a φ x := by
  unfold ctLift
  have key : (fun n : ℤ => (Axi.age ε⁻¹ x.2) ^ a *
      φ (Axi.age ε⁻¹ x.2, (Axi.phase ε⁻¹ (x.1 + 2 * ε * c) x.2 + n * c, Axi.trans ε⁻¹ x.2))) =
      (fun n : ℤ => (Axi.age ε⁻¹ x.2) ^ a *
        φ (Axi.age ε⁻¹ x.2, (Axi.phase ε⁻¹ x.1 x.2 + n * c, Axi.trans ε⁻¹ x.2))) ∘
        (Equiv.addRight (1 : ℤ)) := by
    funext n
    simp only [Function.comp_apply, Equiv.coe_addRight, phase_period_shift hε]
    congr 3
    push_cast
    ring_nf
  rw [key]
  exact (Equiv.tsum_eq (Equiv.addRight (1 : ℤ))
    (fun n : ℤ => (Axi.age ε⁻¹ x.2) ^ a *
      φ (Axi.age ε⁻¹ x.2, (Axi.phase ε⁻¹ x.1 x.2 + n * c, Axi.trans ε⁻¹ x.2))))

end UnforcedLeray.Short.IIb
