import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3_1
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Group.Integral

/-!
# `mollExists`: a mollifier exists

Source `the November 2 reference manuscript` lines 1351-1362.
Normalised `ContDiffBump` on `ℝ³`, symmetrised `(b(y) + b(-y))/2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem mollExists : MollExists := by
  let b : ContDiffBump (0 : Space) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let η0 : Space → ℝ := b.normed volume
  have hC : ContDiff ℝ ∞ η0 := b.contDiff_normed
  have hS : HasCompactSupport η0 := b.hasCompactSupport_normed
  have hN : ∀ y, 0 ≤ η0 y := b.nonneg_normed
  have hI : ∫ y : Space, η0 y = 1 := b.integral_normed
  have hInt : Integrable η0 := b.integrable_normed
  refine ⟨fun y => (η0 y + η0 (-y)) / 2, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hC.add (hC.comp contDiff_neg)).div_const 2
  · have hS2 : HasCompactSupport (fun y => η0 y + η0 (-y)) :=
      hS.add (hS.comp_homeomorph (Homeomorph.neg Space))
    exact hS2.comp_left (g := fun t : ℝ => t / 2) (by simp)
  · intro y
    simp only [neg_neg]
    ring
  · intro y
    have h1 := hN y
    have h2 := hN (-y)
    positivity
  · rw [integral_div, integral_add hInt hInt.comp_neg, integral_neg_eq_self, hI]
    norm_num

end UnforcedLeray.Short.PartIIIb.Concrete
