import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.LeavesOf
import UnforcedLeray.Units.B0284.Contraction
import NonUniqueEuler.P.Infra.ConvMinkowski.Minkowski
import UnforcedLeray.Lib.Cylinder.Basic
import UnforcedLeray.Units.B0579

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8/1/1`: the periodic Young inequality on the centred cell

Proves `AdjCellYoung` (SP 2819-2836, 3044-3050): Minkowski's integral inequality on
`volume.restrict (B0579.cell c)` for a periodic `g`, translation invariance of the cell `L²`
norm, and the total kernel mass.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

lemma two_ne_top_ennreal : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num

/-- Translation invariance of the cell `L²` norm of a `c`-periodic real field. -/
theorem adjCellYoung_translate {c : ℝ} (hc : 0 < c) {g : ℝ × ℝ → ℝ}
    (hper : ∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x) (z : ℝ × ℝ) :
    eLpNorm (fun x => g (x - z)) 2 (volume.restrict (B0579.cell c)) =
      eLpNorm g 2 (volume.restrict (B0579.cell c)) := by
  have hcell : B0579.cell c = UnforcedLeray.Cyl.cell c := by
    unfold B0579.cell UnforcedLeray.Cyl.cell
    rw [neg_div]
  have hper' : UnforcedLeray.Cyl.IsPeriodic c (fun x => ‖g x‖ₑ ^ (2 : ℝ)) := fun x => by
    show ‖g (x.1 + c, x.2)‖ₑ ^ (2 : ℝ) = ‖g x‖ₑ ^ (2 : ℝ)
    rw [hper x]
  have key := UnforcedLeray.Cyl.lintegral_cell_comp_add hc hper' (-z)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero two_ne_top_ennreal,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero two_ne_top_ennreal]
  congr 1
  simp only [ENNReal.toReal_ofNat]
  rw [hcell]
  simp only [sub_eq_add_neg]
  exact key

/-- **(H1.0) The periodic Young inequality on the centred cell** (SP 2819-2836, 3044-3050):
Minkowski's inequality for a finite kernel `K` against a `c`-periodic real field `g`. -/
theorem adjCellYoung : AdjCellYoung := by
  unfold AdjCellYoung
  intro c hc K hK hKfin g hper hg
  have hsub : AEStronglyMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => g (q.1 - q.2))
      ((volume : Measure (ℝ × ℝ)).prod volume) :=
    hg.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant (volume : Measure (ℝ × ℝ)) volume)
  have hac : (volume.restrict (B0579.cell c)).prod (volume : Measure (ℝ × ℝ)) ≪
      (volume : Measure (ℝ × ℝ)).prod volume :=
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).prod
      Measure.AbsolutelyContinuous.rfl
  have hF : AEMeasurable (Function.uncurry fun x z : ℝ × ℝ => K z * ‖g (x - z)‖ₑ)
      ((volume.restrict (B0579.cell c)).prod (volume : Measure (ℝ × ℝ))) := by
    have h1 : AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => ‖g (q.1 - q.2)‖ₑ)
        ((volume.restrict (B0579.cell c)).prod (volume : Measure (ℝ × ℝ))) :=
      (hsub.enorm).mono_ac hac
    exact (hK.comp measurable_snd).aemeasurable.mul h1
  calc eLpNorm (fun x => ∫⁻ z, K z * ‖g (x - z)‖ₑ) 2 (volume.restrict (B0579.cell c))
      ≤ ∫⁻ z, eLpNorm (fun x => K z * ‖g (x - z)‖ₑ) 2 (volume.restrict (B0579.cell c)) :=
        NonUniqueEuler.Conv.eLpNorm_lintegral_le hF (by norm_num) two_ne_top_ennreal
    _ = ∫⁻ z, K z * eLpNorm g 2 (volume.restrict (B0579.cell c)) := by
        refine lintegral_congr fun z => ?_
        rw [UnforcedLeray.B0284.eLpNorm_const_mul_ennreal (hKfin z) _ two_ne_zero two_ne_top_ennreal, eLpNorm_enorm,
          adjCellYoung_translate hc hper z]
    _ = (∫⁻ z, K z) * eLpNorm g 2 (volume.restrict (B0579.cell c)) :=
        lintegral_mul_const _ hK

end UnforcedLeray.Short.IIIa
