import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N02_4_4_7
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials.Parseval.HFubini

/-!
# Part II-a, task `PartII-a:N02/4/4/7/3`: product integrability on `measureH c` (`NzFpProdInt`)

For continuous `H` on `ℝ × ℝ` with `x ↦ H x * x.1^{-3/2}` integrable on the strip
`(0,∞) × ℝ`, the function `p ↦ H (p.1, p.2.2)` is integrable on `measureH c`.

Route: `measureH c = (cell c).withDensity weightH` with weight `s^{-3/2}`, so integrability
reduces to `p ↦ H(p.1,p.2.2) * p.1^{-3/2}` on `cell c`. The reassociation `nzfpAssocE` maps
`cell c` onto `((0,∞) × ℝ) × (0,c]`, where the function is the strip function times the constant `1`
on a finite-measure factor (`Integrable.mul_prod`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

theorem nzFpProdInt : NzFpProdInt := by
  intro c hc H hH hK
  have hpre : nzfpAssocE ⁻¹' ((Ioi (0 : ℝ) ×ˢ univ) ×ˢ Ioc (0 : ℝ) c) = cell c := by
    ext p
    simp [cell, nzfpAssocE_apply]
  have hSm : MeasurableSet (((Ioi (0 : ℝ)) ×ˢ (univ : Set ℝ)) ×ˢ Ioc (0 : ℝ) c) :=
    (measurableSet_Ioi.prod MeasurableSet.univ).prod measurableSet_Ioc
  have hmp := nzfpAssocE_mp.restrict_preimage hSm
  rw [hpre] at hmp
  have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc (0 : ℝ) c)) :=
    integrable_const _
  have hI1 : Integrable (fun z : (ℝ × ℝ) × ℝ => (H z.1 * z.1.1 ^ (-(3 / 2 : ℝ))) * (1 : ℝ))
      (((volume : Measure (ℝ × ℝ)).restrict (Ioi (0 : ℝ) ×ˢ univ)).prod
        ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) c))) :=
    Integrable.mul_prod hK hconst
  have hpr : ((volume : Measure (ℝ × ℝ)).restrict (Ioi (0 : ℝ) ×ˢ univ)).prod
      ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) c)) =
      ((((volume : Measure ℝ).prod (volume : Measure ℝ)).prod (volume : Measure ℝ))).restrict
        ((Ioi (0 : ℝ) ×ˢ univ) ×ˢ Ioc (0 : ℝ) c) :=
    Measure.prod_restrict _ _
  rw [hpr] at hI1
  have hcomp : Integrable
      ((fun z : (ℝ × ℝ) × ℝ => (H z.1 * z.1.1 ^ (-(3 / 2 : ℝ))) * (1 : ℝ)) ∘ nzfpAssocE)
      (volume.restrict (cell c)) :=
    (hmp.integrable_comp_emb nzfpAssocE.measurableEmbedding).mpr hI1
  have hcomp2 : Integrable
      (fun p : Profile => H (p.1, p.2.2) * p.1 ^ (-(3 / 2 : ℝ)) * (1 : ℝ))
      (volume.restrict (cell c)) := hcomp
  have hae : (fun p : Profile => H (p.1, p.2.2) * p.1 ^ (-(3 / 2 : ℝ)) * (1 : ℝ)) =ᵐ[volume.restrict (cell c)]
      (fun p : Profile => (weightH p).toReal • H (p.1, p.2.2)) := by
    refine (ae_restrict_iff' (measurableSet_cell c)).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    have hx1 : 0 < x.1 := hx.1
    simp only [weightH, ENNReal.toReal_ofReal (Real.rpow_nonneg hx1.le _), smul_eq_mul]
    ring
  have hW := hcomp2.congr hae
  show Integrable (fun p : Profile => H (p.1, p.2.2)) ((volume.restrict (cell c)).withDensity weightH)
  exact (integrable_withDensity_iff_integrable_smul' measurable_weightH (ae_weightH_lt_top c)).mpr hW

end UnforcedLeray.Short.PartIIa
