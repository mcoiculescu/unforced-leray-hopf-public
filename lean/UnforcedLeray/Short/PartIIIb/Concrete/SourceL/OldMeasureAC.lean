import UnforcedLeray.Short.PartIIIb.Concrete.SourceL

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The age-weighted density `s^{-1/2}` restricted to `(0,∞)` gives a measure dominating
`vol.restrict (Ioi a)` for `a ≥ 0`. -/
theorem oldMeasureAC : OldMeasureAC := by
  intro c mZ γ ν hν
  -- Step 1: the age factor of the old region is dominated by the age measure `s^{-1/2} ds`.
  have hA : (volume.restrict (Ioi (6 / 5 / ν))) ≪
      (volume.restrict (Ioi (0 : ℝ))).withDensity (fun s : ℝ => ENNReal.ofReal (s ^ (-1 / 2 : ℝ))) := by
    have hsub : Ioi (6 / 5 / ν) ⊆ Ioi (0 : ℝ) :=
      Set.Ioi_subset_Ioi (div_nonneg (by norm_num) hν.le)
    have hle : volume.restrict (Ioi (6 / 5 / ν)) ≤ volume.restrict (Ioi (0 : ℝ)) :=
      Measure.restrict_mono hsub le_rfl
    have hf : AEMeasurable (fun s : ℝ => ENNReal.ofReal (s ^ (-1 / 2 : ℝ)))
        (volume.restrict (Ioi (0 : ℝ))) :=
      (measurable_ofReal_rpow _).aemeasurable
    have hne : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
        ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) ≠ 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (Set.mem_Ioi.mp hs) _)).ne'
    exact (Measure.absolutelyContinuous_of_le hle).trans (withDensity_absolutelyContinuous' hf hne)
  -- Step 2: pass to the product with the cell measure.
  have hProd : oldMeasure c ν ≪ ageμ c (-1 / 2) := by
    haveI : SFinite (Cyl.avgμ c) := by
      unfold Cyl.avgμ
      infer_instance
    unfold oldMeasure ageμ
    exact Measure.AbsolutelyContinuous.prod hA (Measure.AbsolutelyContinuous.refl _)
  -- Step 3: the transverse weight `W²` has positive density.
  have hWm : Measurable (fun p : Chart => ENNReal.ofReal
      (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2)) := by
    unfold UnforcedLeray.Short.IIIa.transWeight
    fun_prop
  have hW : ageμ c (-1 / 2) ≪ (ageμ c (-1 / 2)).withDensity
      (fun p : Chart => ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2)) := by
    refine withDensity_absolutelyContinuous' hWm.aemeasurable (ae_of_all _ fun p => ?_)
    refine (ENNReal.ofReal_pos.mpr ?_).ne'
    unfold UnforcedLeray.Short.IIIa.transWeight
    positivity
  -- Step 4: the inverse gain squared is strictly positive.
  have hGm : Measurable (fun p : Chart => ENNReal.ofReal (ginv γ ν p ^ 2)) := by
    unfold ginv UnforcedLeray.Short.IIIa.gainG
    fun_prop
  have hG : (ageμ c (-1 / 2)).withDensity
      (fun p : Chart => ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2)) ≪
      ((ageμ c (-1 / 2)).withDensity
        (fun p : Chart => ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2))).withDensity
        (fun p : Chart => ENNReal.ofReal (ginv γ ν p ^ 2)) := by
    refine withDensity_absolutelyContinuous' hGm.aemeasurable (ae_of_all _ fun p => ?_)
    refine (ENNReal.ofReal_pos.mpr ?_).ne'
    have hpos : 0 < ginv γ ν p := by
      unfold ginv UnforcedLeray.Short.IIIa.gainG
      exact inv_pos.mpr (Real.exp_pos _)
    positivity
  unfold gainZ1Measure z1Measure
  exact (hProd.trans hW).trans hG

end UnforcedLeray.Short.PartIIIb.Concrete
