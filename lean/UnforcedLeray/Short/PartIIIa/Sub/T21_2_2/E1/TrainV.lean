import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Defs

/-!
# Part III-a, task `PartIII-a:T21/2/2/3/1`: the rescaled train velocity is a regular periodic field

Source of record: `the November 2 reference manuscript`, lines 2861-2873 (the
rescaled train `V = a^{3/2} v(√a y)`). The Prop `MovingTrainVReg` is defined in `E1/Defs.lean`.

For `0 ≤ r` with `0 < a = clockA ν r`, the map `y ↦ movingTrainV tr r y` is `C^1` (indeed `C^∞`)
because it is the constant `a^{3/2}` times the slice `z ↦ tr.v r z` precomposed with the linear map
`y ↦ (√a y.1, √a y.2)`. It is `cellLen c a = c/√a` periodic in `y.1`, because
`√a (y.1 + c/√a) = √a y.1 + c` and `tr.v r` is `c`-periodic.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff
open UnforcedLeray.Cyl (Plane)

namespace UnforcedLeray.Short.IIIa.AdjE1

theorem movingTrainVReg : UnforcedLeray.Short.IIIa.AdjE1.MovingTrainVReg := by
  intro ν c tr r hr ha
  refine ⟨?_, ?_⟩
  · -- smoothness of the slice `z ↦ tr.v r z`
    have hslice : ContDiffOn ℝ ∞ (fun z : Plane => tr.v r z) univ :=
      tr.isTrain.smooth_v.comp ((contDiffOn_const (c := r)).prodMk contDiffOn_id)
        (fun z _ => (⟨hr, mem_univ z⟩ : ((r, z) : ℝ × Plane) ∈ Ici (0 : ℝ) ×ˢ (univ : Set Plane)))
    have hS : ContDiff ℝ ∞ (fun z : Plane => tr.v r z) := contDiffOn_univ.1 hslice
    have hL : ContDiff ℝ ∞ (fun y : ℝ × ℝ =>
        ((Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) : ℝ × ℝ)) := by
      fun_prop
    have hcomp : ContDiff ℝ ∞ (fun y : ℝ × ℝ => tr.v r
        (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)) := hS.comp hL
    have hproj : ∀ j : Fin 2, ContDiff ℝ ∞ (fun f : Fin 2 → ℝ => f j) := fun j => by fun_prop
    have hcoord : ∀ j : Fin 2, ContDiff ℝ ∞ (fun y : ℝ × ℝ =>
        (tr.v r (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)) j) := fun j =>
      ((hproj j).comp (PiLp.contDiff_ofLp (p := 2) (𝕜 := ℝ) (n := ∞))).comp hcomp
    have hfin : ContDiff ℝ ∞ (movingTrainV tr r) := by
      refine contDiff_pi.2 fun j => ?_
      exact contDiff_const.mul (hcoord j)
    exact hfin.of_le (mod_cast le_top)
  · -- `cellLen c a`-periodicity in `y.1`
    intro y
    have hs : 0 < Real.sqrt (clockA ν r) := Real.sqrt_pos.mpr ha
    have hL' : Real.sqrt (clockA ν r) * (y.1 + cellLen c (clockA ν r))
        = Real.sqrt (clockA ν r) * y.1 + c := by
      unfold cellLen
      have hs' : Real.sqrt (clockA ν r) ≠ 0 := hs.ne'
      field_simp
    have key : tr.v r (Real.sqrt (clockA ν r) * y.1 + c, Real.sqrt (clockA ν r) * y.2)
        = tr.v r (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) :=
      tr.isTrain.periodic_v r hr (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)
    funext j
    simp only [movingTrainV]
    rw [hL', key]
end UnforcedLeray.Short.IIIa.AdjE1
