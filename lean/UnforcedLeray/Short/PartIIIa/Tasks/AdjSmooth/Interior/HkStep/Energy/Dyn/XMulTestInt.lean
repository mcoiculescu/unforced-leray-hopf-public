import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Dyn.Defs
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_1_3
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.RhsCont.WeightedCS
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem xMulTestInt : UnforcedLeray.Short.IIIa.XMulTestInt := by
  intro c m f g hc hf hg
  have hgm : MemLp g 2 (B0579.cellMeasure c m) := hg.memLp m
  have hgc : Continuous g := hg.continuous
  exact integrable_pair weightedCS (K := 1) (N := g) (B := fun x => ‖g x‖) hf hgm.norm
    hgc.aestronglyMeasurable
    (fun x _ => by simp [Real.norm_eq_abs])

end UnforcedLeray.Short.IIIa
