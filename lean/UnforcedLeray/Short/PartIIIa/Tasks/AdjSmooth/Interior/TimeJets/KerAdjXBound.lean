import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.NearFar
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.AdjSplit
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.XNormSplit

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem kerAdjXBound (m : ℝ) (hm : 1 < m) : KerAdjXBound m := by
  obtain ⟨C₁, hC₁0, hS⟩ := kerAdjSplit_of kerNearFar
  obtain ⟨C₂, hC₂0, hX⟩ := xNormSplitLe m hm
  refine ⟨C₁ * (1 + C₂), mul_nonneg hC₁0 (by linarith), fun d hd F hF => ?_⟩
  have hd0 : 0 < d := by linarith
  obtain ⟨a, b, hab, hma, hna, hmb, hbd⟩ := hS d hd F hF
  have hxle := hX d hd0 (kerAdj d F) a b
    (ENNReal.ofReal C₁ * ∑ j, eLpNorm (F j) 1 (volume.restrict (B0579.cell d))) hab
    hma.aestronglyMeasurable hmb hbd
  have hsum : ∑ l : Fin 2, (eLpNorm (F l) 1 (volume.restrict (B0579.cell d)) +
      eLpNorm (F l) 2 (volume.restrict (B0579.cell d))) =
      (∑ j, eLpNorm (F j) 1 (volume.restrict (B0579.cell d))) +
      (∑ j, eLpNorm (F j) 2 (volume.restrict (B0579.cell d))) :=
    Finset.sum_add_distrib
  have hkey : ENNReal.ofReal C₁ * (∑ j, eLpNorm (F j) 2 (volume.restrict (B0579.cell d))) +
      ENNReal.ofReal C₂ * (ENNReal.ofReal C₁ * ∑ j, eLpNorm (F j) 1 (volume.restrict (B0579.cell d)))
      ≤ ENNReal.ofReal (C₁ * (1 + C₂)) * ((∑ j, eLpNorm (F j) 1 (volume.restrict (B0579.cell d))) +
        (∑ j, eLpNorm (F j) 2 (volume.restrict (B0579.cell d)))) := by
    have hC : ENNReal.ofReal (C₁ * (1 + C₂)) =
        ENNReal.ofReal C₁ + ENNReal.ofReal C₁ * ENNReal.ofReal C₂ := by
      rw [ENNReal.ofReal_mul hC₁0, ENNReal.ofReal_add zero_le_one hC₂0, ENNReal.ofReal_one,
        mul_add, mul_one]
    rw [hC]
    generalize (∑ j, eLpNorm (F j) 1 (volume.restrict (B0579.cell d))) = S1
    generalize (∑ j, eLpNorm (F j) 2 (volume.restrict (B0579.cell d))) = S2
    calc ENNReal.ofReal C₁ * S2 + ENNReal.ofReal C₂ * (ENNReal.ofReal C₁ * S1)
        = ENNReal.ofReal C₁ * S2 + ENNReal.ofReal C₁ * ENNReal.ofReal C₂ * S1 := by ring
      _ ≤ ENNReal.ofReal C₁ * S2 + ENNReal.ofReal C₁ * ENNReal.ofReal C₂ * S1 +
          (ENNReal.ofReal C₁ * S1 + ENNReal.ofReal C₁ * ENNReal.ofReal C₂ * S2) := le_self_add
      _ = (ENNReal.ofReal C₁ + ENNReal.ofReal C₁ * ENNReal.ofReal C₂) * (S1 + S2) := by ring
  have hbound : xNorm d (-m) (kerAdj d F) ≤
      ENNReal.ofReal (C₁ * (1 + C₂)) * ∑ l : Fin 2, (eLpNorm (F l) 1 (volume.restrict (B0579.cell d)) +
        eLpNorm (F l) 2 (volume.restrict (B0579.cell d))) := by
    rw [hsum]
    exact le_trans hxle (le_trans (add_le_add hna le_rfl) hkey)
  have hfin : ENNReal.ofReal (C₁ * (1 + C₂)) * ∑ l : Fin 2, (eLpNorm (F l) 1
      (volume.restrict (B0579.cell d)) + eLpNorm (F l) 2 (volume.restrict (B0579.cell d))) < ⊤ := by
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    refine ENNReal.sum_lt_top.2 fun l _ => ENNReal.add_lt_top.2 ⟨?_, ?_⟩
    · exact (memLp_one_iff_integrable.2 (hF l).1).eLpNorm_lt_top
    · exact (hF l).2.eLpNorm_lt_top
  have hxfin : xNorm d (-m) (kerAdj d F) < ⊤ := lt_of_le_of_lt hbound hfin
  have hmeas : AEStronglyMeasurable (kerAdj d F) (B0579.cellMeasure d (-m)) :=
    ((hma.aestronglyMeasurable.add hmb).congr hab.symm).mono_ac (B0579.cellMeasure_ac d (-m))
  exact ⟨⟨hmeas, hxfin⟩, hbound⟩

end UnforcedLeray.Short.IIIa
