import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Dyn.Defs
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Shared
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDualitySub
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.Topology.ContinuousOn

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem velMulMemX (m : ℝ) : UnforcedLeray.Short.IIIa.VelMulMemX m := by
  intro ν tr t s g φ a b χ hctx r hr l
  obtain ⟨hν, hν1, hLad, ht0, hts, hA, hT, hta, hab, hbs, hchi⟩ := hctx
  have hr0 : 0 ≤ r := le_trans ht0 (le_trans hta hr.1.le)
  have hrs : r ∈ Icc t s := ⟨le_trans hta hr.1.le, le_trans hr.2.le hbs.le⟩
  have hrI : r ∈ Ico t s := ⟨le_trans hta hr.1.le, lt_trans hr.2 hbs⟩
  constructor
  · intro x
    have h1 : tr.v r (x.1 + ν ^ (-2 : ℝ), x.2) = tr.v r x := tr.isTrain.periodic_v r hr0 x
    have h2 : φ r (x.1 + ν ^ (-2 : ℝ), x.2) = φ r x := hA.periodic r hrI x
    rw [h1, h2]
  · have hsm : ContinuousOn (fun x : ℝ × (ℝ × ℝ) => tr.v x.1 x.2) (Ici 0 ×ˢ univ) :=
      tr.isTrain.smooth_v.continuousOn
    have hcont : Continuous (fun y : ℝ × ℝ => tr.v r y) :=
      hsm.comp_continuous (f := fun y : ℝ × ℝ => (r, y)) (by fun_prop)
        (fun y => ⟨hr0, mem_univ _⟩)
    have hvl : Continuous (fun y : ℝ × ℝ => ((tr.v r y l : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp ((continuous_apply l).comp
        ((PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ)).comp hcont))
    have hmeas : AEStronglyMeasurable (fun y : ℝ × ℝ => ((tr.v r y l : ℝ) : ℂ) * φ r y)
        (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
      hvl.aestronglyMeasurable.mul (hA.memX r hrs).1
    obtain ⟨C, hCb⟩ := hLad s (le_trans ht0 hts.le)
    have hmem : MemLp (fun y : ℝ × ℝ => ((|C| : ℝ) : ℂ) * φ r y) 2
        (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
      (hA.memX r hrs).const_mul _
    refine MemLp.of_le hmem hmeas ?_
    have hae : ∀ᵐ y ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)), y ∈ B0579.cell (ν ^ (-2 : ℝ)) :=
      (B0579.cellMeasure_ac _ _).ae_le (ae_restrict_mem (B0579.measurableSet_cell _))
    filter_upwards [hae] with y hy
    have hv : |tr.v r y l| ≤ |C| := (hCb r ⟨hr0, hrs.2⟩ y hy).1 l |>.trans (le_abs_self C)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_abs]
    exact mul_le_mul_of_nonneg_right hv (norm_nonneg _)

end UnforcedLeray.Short.IIIa
