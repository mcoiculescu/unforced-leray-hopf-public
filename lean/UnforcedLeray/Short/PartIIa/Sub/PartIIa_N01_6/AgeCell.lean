import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_6
import UnforcedLeray.Short.PartIIa.StatementsNear
import UnforcedLeray.Lib.AxisymmetricB.Lift
import UnforcedLeray.Lib.Axisymmetric.RingMeasure
import UnforcedLeray.Lib.Cylinder.Basic
import UnforcedLeray.Units.B0220.Chart

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01

/-- Splitting a Lebesgue integral over a product set (`ℝ × (ℝ × ℝ)`) into iterated integrals. -/
private theorem lintegral_prod_restrict_split (F : ℝ × (ℝ × ℝ) → ℝ≥0∞) (hF : Measurable F)
    (S : Set ℝ) (T : Set (ℝ × ℝ)) :
    ∫⁻ p in S ×ˢ T, F p = ∫⁻ s in S, ∫⁻ z in T, F (s, z) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact lintegral_prod F hF.aemeasurable

/-- A `q`-`c`-periodic integrand has the same integral over `(0, c]` and over `[-c/2, c/2)`
(one period of the slice, fundamental domain of `(c, 0)` in the plane). -/
private theorem slice_Ioc_eq_cell {c : ℝ} (hc : 0 < c) (g : ℝ × ℝ → ℝ≥0∞)
    (hper : ∀ z : ℝ × ℝ, g (z.1 + c, z.2) = g z) :
    ∫⁻ z in Ioc 0 c ×ˢ (univ : Set ℝ), g z = ∫⁻ z in Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ), g z := by
  have hset : ∫⁻ z in Ioc 0 c ×ˢ (univ : Set ℝ), g z = ∫⁻ z in Ico 0 c ×ˢ (univ : Set ℝ), g z := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, ← Measure.prod_restrict,
      Measure.restrict_univ, Measure.restrict_congr_set Ico_ae_eq_Ioc]
  have hstrip := UnforcedLeray.Cyl.lintegral_strip_eq_cell hc hper 0
  simp only [zero_add] at hstrip
  calc ∫⁻ z in Ioc 0 c ×ˢ (univ : Set ℝ), g z = ∫⁻ z in Ico 0 c ×ˢ (univ : Set ℝ), g z := hset
    _ = ∫⁻ z in Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ), g z := hstrip

/-- `PartII-a:N01/6/3` the age cell measure versus `measureHT` (source 2666-2679, 1642). -/
theorem ageCellTransfer : UnforcedLeray.Short.PartIIa.N01.AgeCellTransfer := by
  intro c hc G hG hper
  have hdens : Measurable (fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (p.1 ^ (-(1 / 2 : ℝ)))) :=
    (UnforcedLeray.Axi.measurable_ofReal_rpow _).comp measurable_fst
  have hF : Measurable (fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (p.1 ^ (-(1 / 2 : ℝ))) * G p) :=
    hdens.mul hG
  set F : ℝ × (ℝ × ℝ) → ℝ≥0∞ := fun p => ENNReal.ofReal (p.1 ^ (-(1 / 2 : ℝ))) * G p with hFdef
  have hFper : ∀ p : ℝ × (ℝ × ℝ), F (p.1, p.2.1 + c, p.2.2) = F p := by
    intro p
    simp only [hFdef, hper p]
  have hL : ∫⁻ p, G p ∂(UnforcedLeray.Axi.ageμ c (-1 / 2)) =
      ENNReal.ofReal c⁻¹ * ∫⁻ p in Ioi (0 : ℝ) ×ˢ UnforcedLeray.Axi.qCell c, F p := by
    have e : (-1 / 2 : ℝ) = -(1 / 2) := by norm_num
    rw [UnforcedLeray.Axi.lintegral_ageμ hc (-1 / 2) hG, e, ← lintegral_const_mul _ hF]
    refine lintegral_congr fun p => ?_
    simp only [hFdef]
    rw [ENNReal.ofReal_mul (inv_nonneg.2 hc.le), mul_assoc]
  have hR : ∫⁻ p, G p ∂(UnforcedLeray.Short.PartIIa.measureHT c) =
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ (Ioc 0 c ×ˢ (univ : Set ℝ)), F p := by
    unfold UnforcedLeray.Short.PartIIa.measureHT UnforcedLeray.B0220.cellMeasure
    rw [lintegral_withDensity_eq_lintegral_mul _ hdens hG]
    rfl
  have hsplit : ∫⁻ p in Ioi (0 : ℝ) ×ˢ UnforcedLeray.Axi.qCell c, F p =
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ (Ioc 0 c ×ˢ (univ : Set ℝ)), F p := by
    rw [lintegral_prod_restrict_split F hF, lintegral_prod_restrict_split F hF]
    refine lintegral_congr fun s => ?_
    exact (slice_Ioc_eq_cell hc (fun z => F (s, z))
      (fun z => hFper (s, z))).symm
  rw [hL, hR, hsplit]

end UnforcedLeray.Short.PartIIa.N01
