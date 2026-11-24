import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.KT.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.WeakMeas

/-!
# `KTWeakMeas`: weak cell derivatives have measurable representatives

Source: `the November 2 reference manuscript` lines 3052-3057.

The tests are the `η`-bumps `x ↦ bump (x₂ - r)`, `r ∈ ℚ` (`isCylTest_bump`), which are
`1` on `|x₂ - r| ≤ 1`; the rational translates cover the cell.

* For `g_j`: the test `bump(x₂ - r)` is a valid test, so `g_j · bump(· - r)` is integrable on the cell
  (second clause of `HasWeakCellDerivC`), hence `g_j` is a.e.-strongly measurable on the open
  set `{bump(· - r) ≠ 0}`, and the sets cover the cell (`meas_on_nonzero`).
* For `φ`: use the `η`-derivative `j = 1` and the tests `bump(· - r)`; the derivative
  `∂_η bump(· - r)` is nonvanishing at some rational translate near each point (`exists_rat_deriv_ne`),
  so `φ` is a.e.-strongly measurable on each set `{∂_η ψ_r ≠ 0}` (`meas_on_nonzero`) and the union covers the cell.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

open LocWeakMeasAux

theorem ktWeakMeas : UnforcedLeray.Short.IIIa.KTWeakMeas := by
  intro c φ g hc hwd
  have hcov : ∀ x : ℝ × ℝ, ∃ r : ℚ, bump (x.2 - (r : ℝ)) ≠ 0 := by
    intro x
    obtain ⟨r, h1, h2⟩ := exists_rat_btwn (show x.2 - 1 < x.2 + 1 by linarith)
    refine ⟨r, ?_⟩
    rw [bump_one (t := x.2 - (r : ℝ)) (by rw [abs_le]; constructor <;> linarith)]
    norm_num
  have hU : (⋃ r : ℚ, ({x : ℝ × ℝ | bump (x.2 - (r : ℝ)) ≠ 0} ∩ B0579.cell c)) =
      B0579.cell c := by
    ext x
    simp only [mem_iUnion, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨r, _, hx⟩
      exact hx
    · intro hx
      obtain ⟨r, hr⟩ := hcov x
      exact ⟨r, hr, hx⟩
  refine ⟨?_, ?_⟩
  · -- the function `φ`, through its `η`-derivative
    have h1 := hwd 1
    have hcover : ∀ x : ℝ × ℝ, ∃ r : ℚ,
        B0579.pd 1 (fun y : ℝ × ℝ => bump (y.2 - (r : ℝ))) x ≠ 0 := by
      intro x
      obtain ⟨r, hr⟩ := exists_rat_deriv_ne x.2
      refine ⟨r, ?_⟩
      have hD : B0579.pd 1 (fun y : ℝ × ℝ => bump (y.2 - (r : ℝ))) x =
          deriv bump (x.2 - (r : ℝ)) := by
        apply pd1_eq (isCylTest_bump c (r : ℝ)).differentiable x
        exact (((bump_contDiff.differentiable (by simp)) (x.2 - (r : ℝ))).hasDerivAt).comp_sub_const
          x.2 (r : ℝ)
      rw [hD]
      exact hr
    have hU' : (⋃ r : ℚ, ({x : ℝ × ℝ | B0579.pd 1 (fun y : ℝ × ℝ => bump (y.2 - (r : ℝ))) x ≠ 0} ∩
        B0579.cell c)) = B0579.cell c := by
      ext x
      simp only [mem_iUnion, mem_inter_iff, mem_setOf_eq]
      constructor
      · rintro ⟨r, _, hx⟩
        exact hx
      · intro hx
        obtain ⟨r, hr⟩ := hcover x
        exact ⟨r, hr, hx⟩
    rw [← hU']
    refine aestronglyMeasurable_iUnion_iff.2 (fun r => ?_)
    have hψ := isCylTest_bump c (r : ℝ)
    have hA : AEStronglyMeasurable
        (fun x => φ x * ((B0579.pd 1 (fun y : ℝ × ℝ => bump (y.2 - (r : ℝ))) x : ℝ) : ℂ))
        (volume.restrict (B0579.cell c)) :=
      ((h1.1 _ hψ).1).aestronglyMeasurable
    exact meas_on_nonzero φ ((hψ.pd 1).continuous) hA
  · -- the derivatives `g_j`, through the tests `bump(· - r)`
    intro j
    rw [← hU]
    refine aestronglyMeasurable_iUnion_iff.2 (fun r => ?_)
    have hψ := isCylTest_bump c (r : ℝ)
    have hA : AEStronglyMeasurable
        (fun x => g j x * ((bump (x.2 - (r : ℝ)) : ℝ) : ℂ))
        (volume.restrict (B0579.cell c)) :=
      ((hwd j).1 _ hψ).2.aestronglyMeasurable
    exact meas_on_nonzero (g j) hψ.continuous hA

end UnforcedLeray.Short.IIIa
