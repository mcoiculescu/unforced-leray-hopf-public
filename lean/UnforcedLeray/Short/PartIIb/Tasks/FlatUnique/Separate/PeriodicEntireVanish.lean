import UnforcedLeray.Short.PartIIb.Sub.T11_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.Separate.PeriodicEntireBounded
import Mathlib.Analysis.Complex.Liouville
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Leaf `PartII-b:T11/6/2`: an entire periodic `L^r` function of the strip vanishes

Proves `PeriodicEntireVanish` (defined in `Sub/T11_6.lean`). Classical Liouville step, not a
source claim (source of record: `the November 2 reference manuscript`, SP 2618).

1. `PeriodicEntireBounded` (leaf `T11/6/1`) gives a bound `‖f z‖ ≤ C`.
2. Liouville (`Differentiable.apply_eq_apply_of_bounded`) gives `f z = f 0` for all `z`.
3. If `f 0 ≠ 0`, the strip integral of the constant `‖f 0‖ₑ ^ r` is `‖f 0‖ₑ ^ r * volume(strip)`.
   The strip is the preimage of `Ico ×ˢ univ` under the measure preserving
   `Complex.measurableEquivRealProd`, so its volume is `ofReal c * ⊤ = ⊤`. Contradiction.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Leaf `PartII-b:T11/6/2`.** -/
theorem periodicEntireVanish : UnforcedLeray.Short.IIb.PeriodicEntireVanish := by
  unfold PeriodicEntireVanish
  intro c r f hc hr hf hper hI
  have hB : PeriodicEntireBounded := periodicEntireBounded
  unfold PeriodicEntireBounded at hB
  obtain ⟨C, hC⟩ := hB c r f hc hr hf hper hI
  have hbd : Bornology.IsBounded (range f) :=
    isBounded_iff_forall_norm_le.2 ⟨C, by rintro _ ⟨z, rfl⟩; exact hC z⟩
  have hconst : ∀ z, f z = f 0 := fun z => hf.apply_eq_apply_of_bounded hbd z 0
  have hk : f 0 = 0 := by
    by_contra hne
    have hvol : volume {z : ℂ | z.re ∈ Ico (-(c / 2)) (c / 2)} = ⊤ := by
      have hmp : MeasurePreserving Complex.measurableEquivRealProd volume volume :=
        Complex.volume_preserving_equiv_real_prod
      have hset : Complex.measurableEquivRealProd ⁻¹' (Ico (-(c / 2)) (c / 2) ×ˢ univ)
          = {z : ℂ | z.re ∈ Ico (-(c / 2)) (c / 2)} := by
        ext z
        simp
      rw [← hset, hmp.measure_preimage (measurableSet_Ico.prod MeasurableSet.univ).nullMeasurableSet,
        Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_univ,
        ENNReal.mul_top (ENNReal.ofReal_pos.2 (by linarith)).ne']
    have hpos : ‖f 0‖ₑ ^ r ≠ 0 :=
      (ENNReal.rpow_pos (enorm_pos.2 hne) enorm_ne_top).ne'
    have hint : ∫⁻ z in {z : ℂ | z.re ∈ Ico (-(c / 2)) (c / 2)}, ‖f z‖ₑ ^ r
        = ∫⁻ z in {z : ℂ | z.re ∈ Ico (-(c / 2)) (c / 2)}, ‖f 0‖ₑ ^ r :=
      lintegral_congr fun z => by rw [hconst z]
    apply hI
    rw [hint, lintegral_const, Measure.restrict_apply_univ, hvol, ENNReal.mul_top hpos]
  funext z
  simp [hconst z, hk]

end UnforcedLeray.Short.IIb

end
