import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_3_1_1_1
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# `sepWZeroOfRoutZero` (`PartIII-b:IIIb-D2/3/1/3/1/1/1/1`)

For `rOut = 0` the source vanishes off the axis `{z 0 = 0}` (hence off `{z 0 = z 1 = 0}`), which
is Lebesgue-null, so every `z`-integral in `sepW` vanishes.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem sepWZeroOfRoutZero : SepWZeroOfRoutZero := by
  intro ν μ P T hT y τ i
  -- the hyperplane `{z 0 = 0}` is Lebesgue-null
  let s : Submodule ℝ Space :=
    { carrier := {z : Space | z 0 = 0}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, PiLp.add_apply] at ha hb ⊢
        rw [ha, hb]; simp
      zero_mem' := by simp
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_setOf_eq, PiLp.smul_apply, smul_eq_mul] at ha ⊢
        rw [ha]; simp }
  have hs : s ≠ ⊤ := by
    intro htop
    have hmem : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : Space) ∈ s := by
      rw [htop]; trivial
    have h1 : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : Space) 0 = 1 := by simp
    have hmem' : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : Space) 0 = 0 := hmem
    rw [h1] at hmem'
    exact one_ne_zero hmem'
  have hnull : (volume : Measure Space) {z : Space | z 0 = 0} = 0 := by
    have := Measure.addHaar_submodule (volume : Measure Space) s hs
    exact this
  have hae : ∀ᵐ z ∂(volume : Measure Space), z 0 ≠ 0 := by
    filter_upwards [compl_mem_ae_iff.mpr hnull] with z hz
    simpa using hz
  have hint : ∀ l : ℝ, ∫ z : Space, ∑ j : Fin 3, ∑ k : Fin 3,
      ((fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x) (y - l • z)
        (coordinateVector k) : ℝ) : ℂ) * ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ) = 0 := by
    intro l
    apply integral_eq_zero_of_ae
    filter_upwards [hae] with z hz
    have h2 : 0 < z 0 ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hz))
    have hpos : 0 < Real.sqrt (z 0 ^ 2 + z 1 ^ 2) :=
      Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg h2 (sq_nonneg _))
    have hzT : T (τ + 2 * Real.log l) z = 0 := hT.support _ _ (by simpa using hpos)
    simp [hzT]
  unfold IIIa.sepW
  simp only [hint, mul_zero, integral_zero]

end UnforcedLeray.Short.PartIIIb.Concrete
