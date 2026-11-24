import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_9

/-!
# Part III-a, `PartIII-a:T21/3/9/2`: real and imaginary parts of admissible data

Source of record: `the November 2 reference manuscript`, lines 2819-2836.
Statement `ActualRepresentation` is in `Sub/PartIIIa_T21_3_9.lean`. An admissible complex datum
`f` (`GoodC`) is a.e. `Re f + I Im f` with both parts in the physical state space: each part is
`L²(cellMeasure)` with zero circulation, so it is the image of an element of the zero-circulation
submodule.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- A real `L²(cellMeasure)` function with zero cell integral is the representative of an
element of the physical state space. -/
theorem arep_real {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m) (g : ℝ × ℝ → ℝ)
    (hg : MemLp g 2 (B0579.cellMeasure c m)) (hz : ∫ x in B0579.cell c, g x = 0) :
    ∃ w : ActualVorticity (c := c) (m := m) hm, ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      vortFn hm w x = g x := by
  have hw : (hg.toLp g : B0579.X c m) ∈ zeroCirculationSubmodule (c := c) (m := m)
      (by linarith : 1 / 2 < m) := by
    rw [mem_zeroCirculationSubmodule_iff]
    rw [integral_congr_ae ((B0579.ac_cellMeasure c m).ae_eq (MemLp.coeFn_toLp hg))]
    exact hz
  refine ⟨⟨hg.toLp g, hw⟩, ?_⟩
  exact (B0579.ac_cellMeasure c m).ae_eq (MemLp.coeFn_toLp hg)

theorem actualRepresentation : UnforcedLeray.Short.IIIa.Exist.ActualRepresentation := by
  intro c m _ hm f hf
  obtain ⟨hL2, hint, hzero⟩ : MemLp f 2 (B0579.cellMeasure c m) ∧
      IntegrableOn f (B0579.cell c) ∧ ∫ x in B0579.cell c, f x = 0 :=
    ⟨hf.1, hf.2.1, hf.2.2⟩
  have hLr : MemLp (fun x => (f x).re) 2 (B0579.cellMeasure c m) := hL2.re
  have hLi : MemLp (fun x => (f x).im) 2 (B0579.cellMeasure c m) := hL2.im
  have zr : ∫ x in B0579.cell c, (f x).re = 0 := by
    have h := integral_re hint
    rw [hzero] at h
    simpa using h
  have zi : ∫ x in B0579.cell c, (f x).im = 0 := by
    have h := integral_im hint
    rw [hzero] at h
    simpa using h
  obtain ⟨wr, hwr⟩ := arep_real hm (fun x => (f x).re) hLr zr
  obtain ⟨wi, hwi⟩ := arep_real hm (fun x => (f x).im) hLi zi
  refine ⟨wr, wi, ?_⟩
  filter_upwards [hwr, hwi] with x h1 h2
  try dsimp only at h1 h2
  show f x = ((vortFn hm wr x : ℝ) : ℂ) + Complex.I * ((vortFn hm wi x : ℝ) : ℂ)
  rw [h1, h2]
  conv_lhs => rw [← Complex.re_add_im (f x)]
  ring
