import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.Mollifier.Defs

/-!
# Part III-a, `PartIII-a:T18/3/1/3/1/5`: unfolding the cell integral

Source of record: `the November 2 reference manuscript` lines 3427-3440 (fields on
the cylinder `C_c = (ℝ/cℤ) × ℝ`) and 3541-3552. For `h` vanishing on `|z₁| ≥ c/3` and `g` periodic in
`q`, the cell integral of `h(x - y reduced to the cell) g(y)` is the integral of `h(x - y) g(y)` over
the plane: both are the integral of a periodic function over a period strip (`Cyl.integral_strip_eq_cell`,
which needs no integrability).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff Convolution

namespace UnforcedLeray.Short.IIIa

theorem lm_cell_unfold {c : ℝ} (hc : 0 < c) {h : ℝ × ℝ → ℝ}
    (hh : ∀ z : ℝ × ℝ, c / 3 ≤ |z.1| → h z = 0) {g : ℝ × ℝ → ℂ}
    (hg : ∀ y : ℝ × ℝ, g (y.1 + c, y.2) = g y) (x : ℝ × ℝ) :
    ∫ y in B0579.cell c, (h (lmPer c (x - y)) : ℂ) * g y = ∫ y, (h (x - y) : ℂ) * g y := by
  have hper : Cyl.IsPeriodic c (fun y : ℝ × ℝ => (h (lmPer c (x - y)) : ℂ) * g y) := by
    intro y
    have h1 : lmPer c (x - (y.1 + c, y.2)) = lmPer c (x - y) := by
      have h2 : x - (y.1 + c, y.2) = ((x - y).1 - c, (x - y).2) := by
        ext <;> simp <;> ring
      rw [h2]
      simp only [lmPer, lmPer1_sub hc.ne']
    show (h (lmPer c (x - (y.1 + c, y.2))) : ℂ) * g (y.1 + c, y.2) = _
    rw [h1, hg y]
  have hcell : B0579.cell c = Cyl.cell c := by
    unfold B0579.cell Cyl.cell
    rw [neg_div]
  have hstrip := Cyl.integral_strip_eq_cell hc hper (x.1 - c / 2)
  rw [hcell, ← hstrip]
  have hS : MeasurableSet (Ico (x.1 - c / 2) (x.1 - c / 2 + c) ×ˢ (univ : Set ℝ)) :=
    measurableSet_Ico.prod MeasurableSet.univ
  have hoff : ∀ y : ℝ × ℝ, y ∉ Ico (x.1 - c / 2) (x.1 - c / 2 + c) ×ˢ (univ : Set ℝ) →
      (h (x - y) : ℂ) * g y = 0 := by
    intro y hy
    have hy' : y.1 ∉ Ico (x.1 - c / 2) (x.1 - c / 2 + c) := fun hm => hy ⟨hm, mem_univ _⟩
    have habs : c / 3 ≤ |(x - y).1| := by
      rw [Prod.fst_sub]
      by_cases h1 : x.1 - c / 2 ≤ y.1
      · have h2 : x.1 - c / 2 + c ≤ y.1 := by
          by_contra hcon
          exact hy' ⟨h1, not_le.mp hcon⟩
        rw [abs_of_nonpos (by linarith)]
        linarith
      · rw [abs_of_nonneg (by linarith)]
        linarith
    simp [hh _ habs]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hoff]
  refine setIntegral_congr_fun hS fun y hy => ?_
  have hy1 : y.1 ∈ Ico (x.1 - c / 2) (x.1 - c / 2 + c) := hy.1
  have hle : x.1 - y.1 ≤ c / 2 := by linarith [hy1.1]
  have hgt : -(c / 2) < x.1 - y.1 := by linarith [hy1.2]
  by_cases hend : x.1 - y.1 = c / 2
  · have hz1 : h (x - y) = 0 := hh _ (by
      rw [Prod.fst_sub, hend, abs_of_pos (by positivity)]
      linarith)
    have hz2 : h (lmPer c (x - y)) = 0 := by
      apply hh
      have hval : (lmPer c (x - y)).1 = -(c / 2) := by
        have := lmPer1_eq_sub_int hc (t := (x - y).1) 1 (by
          rw [Prod.fst_sub, hend]
          constructor <;> push_cast <;> linarith)
        show lmPer1 c (x - y).1 = _
        rw [this, Prod.fst_sub, hend]
        push_cast
        ring
      rw [hval, abs_neg, abs_of_pos (by positivity)]
      linarith
    rw [hz1, hz2]
  · have hin : (x - y).1 ∈ Ico (-(c / 2)) (c / 2) := by
      rw [Prod.fst_sub]
      exact ⟨hgt.le, lt_of_le_of_ne hle hend⟩
    have : lmPer c (x - y) = x - y := by
      show (lmPer1 c (x - y).1, (x - y).2) = x - y
      rw [lmPer1_of_mem hc hin]
    rw [this]

end UnforcedLeray.Short.IIIa
