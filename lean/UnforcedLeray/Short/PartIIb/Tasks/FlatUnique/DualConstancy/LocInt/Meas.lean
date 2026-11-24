import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_1_aux

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Leaf `T11/2/1/1`: measurability of `dualF` on `(0,s)` by Fubini. -/
theorem DualFMeas_proof : UnforcedLeray.Short.IIb.DualFMeas := by
  intro c r ν μ b H s hc hν hr hs hb hfl hH
  have : SFinite (Cyl.avgμ c) := sfinite_avgμ c
  set M : Measure Coord := (volume.restrict (Ioo (0 : ℝ) s)).prod (Cyl.avgμ c) with hM
  have hbM : AEStronglyMeasurable b M := b_aestronglyMeasurable_prod hc hb s
  have hMr : M = (volume.prod (Cyl.avgμ c)).restrict (Ioo (0 : ℝ) s ×ˢ (univ : Set (ℝ × ℝ))) := by
    rw [hM, ← Measure.prod_restrict, Measure.restrict_univ]
  have hS : MeasurableSet (Ioo (0 : ℝ) s ×ˢ (univ : Set (ℝ × ℝ))) :=
    measurableSet_Ioo.prod MeasurableSet.univ
  have hg : ∀ i : Fin 2, AEStronglyMeasurable
      (fun q : Coord => perpGrad (fun z => H (s - q.1, z)) q.2 i) M := by
    intro i
    rw [hMr]
    have hco : ContinuousOn (fun q : Coord => perpGrad (fun z => H (s - q.1, z)) q.2 i)
        (Ioo (0 : ℝ) s ×ˢ (univ : Set (ℝ × ℝ))) :=
      (perpGradH_continuousOn hH.smooth s i).mono (fun q hq => (mem_ofPred_eq ▸ hq.1.2))
    exact hco.aestronglyMeasurable hS
  have hG : AEStronglyMeasurable (fun q : Coord => ∑ i : Fin 2, b q i *
      ((perpGrad (fun z => H (s - q.1, z)) q.2 i : ℝ) : ℂ)) M := by
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    have h1 : AEStronglyMeasurable (fun q : Coord => b q i) M :=
      (EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable hbM
    exact h1.mul (Complex.continuous_ofReal.comp_aestronglyMeasurable (hg i))
  have hI := hG.integral_prod_right'
  have hcp : Measurable (fun σ : ℝ => ((σ : ℝ) : ℂ) ^ μ) :=
    Complex.measurable_ofReal.pow_const μ
  exact hcp.aestronglyMeasurable.mul hI

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.DualFMeas_proof
