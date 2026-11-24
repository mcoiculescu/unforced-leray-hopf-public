import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1
import UnforcedLeray.Lib.CylinderB.Periodize
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **The circulation of a periodization is the plane integral** (source 4562-4570).
Route: replace `g` by a strongly measurable representative `g'`; the periodizations agree a.e.
(each shift is measure preserving, countably many shifts); then `Cyl.integral_cell_periodize_mul`
with the constant periodic weight `1` gives `∫_cell P_c g' = ∫ g'`. -/
theorem periodizeIntegral : PeriodizeIntegral := by
  intro c g hc hg
  obtain ⟨g', hsm, hgg⟩ := hg.aestronglyMeasurable
  have hint : Integrable g' := hg.congr hgg
  -- the periodizations agree almost everywhere
  have hae : ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)), ∀ n : ℤ,
      g (x.1 - n * c, x.2) = g' (x.1 - n * c, x.2) := by
    rw [ae_all_iff]
    intro n
    have hmp := (UnforcedLeray.Cyl.measurePreserving_shift (-((n : ℝ) * c))).quasiMeasurePreserving.ae
      (p := fun y => g y = g' y) hgg
    filter_upwards [hmp] with x hx
    rw [← sub_eq_add_neg] at hx
    exact hx
  have hP : IIIa.periodizeC c g =ᵐ[volume] IIIa.periodizeC c g' := by
    filter_upwards [hae] with x hx
    unfold IIIa.periodizeC
    exact tsum_congr fun n => hx n
  have hcell : B0579.cell c = UnforcedLeray.Cyl.cell c := by
    unfold B0579.cell UnforcedLeray.Cyl.cell
    rw [neg_div]
  have hI := UnforcedLeray.Cyl.integral_cell_periodize_mul (𝕜 := ℂ) hc (f := g')
    (g := fun _ : ℝ × ℝ => (1 : ℂ)) hsm stronglyMeasurable_const (fun _ => rfl)
    (by simpa using hint)
  simp only [mul_one] at hI
  rw [hcell]
  calc ∫ x in UnforcedLeray.Cyl.cell c, IIIa.periodizeC c g x
      = ∫ x in UnforcedLeray.Cyl.cell c, IIIa.periodizeC c g' x :=
        integral_congr_ae (ae_restrict_of_ae hP)
    _ = ∫ x in UnforcedLeray.Cyl.cell c, UnforcedLeray.Cyl.periodize c g' x := rfl
    _ = ∫ x, g' x := hI
    _ = ∫ x, g x := (integral_congr_ae hgg).symm

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
