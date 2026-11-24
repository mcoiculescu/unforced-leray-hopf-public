import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.TransTable.Props
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.VertYoungL2.Kern
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_1_3

/-!
# `ThinChart/QInt`: one `q`-cell is one phase period (source 2666-2668)

`τ = 2q/R + log s`, so for a `P`-periodic `F` (`P = 2c/R`) the integral over the `q`-cell
`[-c/2, c/2)` of `F(2q/R + L)` is `c` times the normalised period integral of `F`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace TC

theorem qint {R c : ℝ} (hR : 0 < R) (hc : 0 < c) {F : ℝ → ℝ≥0∞} (hFm : Measurable F)
    (hper : ∀ s, F (s + 2 * c / R) = F s) (L : ℝ) :
    ∫⁻ q in Ico (-c / 2) (c / 2), F (2 * q / R + L) =
      ENNReal.ofReal c * ((ENNReal.ofReal (2 * c / R))⁻¹ * ∫⁻ τ in Ioc 0 (2 * c / R), F τ) := by
  set D : ℝ := 2 / R with hD
  have hD0 : 0 < D := by positivity
  set P : ℝ := 2 * c / R with hP
  have hP0 : 0 < P := by positivity
  set K : ℝ → ℝ≥0∞ := (Ico (-c / R) (c / R)).indicator (fun u => F (u + L)) with hK
  have hKm : Measurable K :=
    (hFm.comp (measurable_id.add_const L)).indicator measurableSet_Ico
  have hmem : ∀ q : ℝ, q ∈ Ico (-c / 2) (c / 2) ↔ D * q ∈ Ico (-c / R) (c / R) := by
    intro q
    have e : D * q = 2 * q / R := by rw [hD]; ring
    rw [e, mem_Ico, mem_Ico, div_le_div_iff_of_pos_right hR, div_lt_div_iff_of_pos_right hR]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have h1 : ∫⁻ q in Ico (-c / 2) (c / 2), F (2 * q / R + L) = ∫⁻ q, K (D * q) := by
    rw [← lintegral_indicator measurableSet_Ico]
    refine lintegral_congr fun q => ?_
    have e : 2 * q / R = D * q := by rw [hD]; ring
    by_cases hq : q ∈ Ico (-c / 2) (c / 2)
    · rw [indicator_of_mem hq, hK, indicator_of_mem ((hmem q).1 hq), e]
    · rw [indicator_of_notMem hq, hK, indicator_of_notMem (fun h => hq ((hmem q).2 h))]
  have h2 : ∫⁻ u, K u = ENNReal.ofReal D * ∫⁻ q, K (D * q) := vk7_lintegral_scale hD0 K hKm
  have h3 : ∫⁻ u, K u = ∫⁻ t in Ioc 0 P, F t := by
    have h4 : ∀ u, K u = (Ico (L - c / R) (L + c / R)).indicator F (u + L) := by
      intro u
      have hnd : -c / R = -(c / R) := by ring
      by_cases hu : u ∈ Ico (-c / R) (c / R)
      · have hu1 : -(c / R) ≤ u := by rw [← hnd]; exact hu.1
        have : u + L ∈ Ico (L - c / R) (L + c / R) := by
          constructor <;> linarith [hu.2]
        rw [hK, indicator_of_mem hu, indicator_of_mem this]
      · have : u + L ∉ Ico (L - c / R) (L + c / R) := fun h => hu ⟨by rw [hnd]; linarith [h.1], by linarith [h.2]⟩
        rw [hK, indicator_of_notMem hu, indicator_of_notMem this]
    simp_rw [h4]
    rw [lintegral_add_right_eq_self (fun x => (Ico (L - c / R) (L + c / R)).indicator F x) L,
      lintegral_indicator measurableSet_Ico]
    rw [setLIntegral_congr Ico_ae_eq_Ioc]
    have : L + c / R = (L - c / R) + P := by rw [hP]; ring
    rw [this]
    exact pds_window hP0 hper _
  have hDne : ENNReal.ofReal D ≠ 0 := (ENNReal.ofReal_pos.2 hD0).ne'
  have h5 : ∫⁻ q, K (D * q) = (ENNReal.ofReal D)⁻¹ * ∫⁻ u, K u := by
    rw [h2, ← mul_assoc, ENNReal.inv_mul_cancel hDne ENNReal.ofReal_ne_top, one_mul]
  rw [h1, h5, h3, ← ENNReal.ofReal_inv_of_pos hD0, ← ENNReal.ofReal_inv_of_pos hP0,
    ← mul_assoc, ← ENNReal.ofReal_mul hc.le]
  congr 2
  rw [hD, hP]
  field_simp

end TC

end UnforcedLeray.Short.PartIIIb.Concrete

end
