import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_1.H4

/-!
# Helpers for `wardX0YoungL2_proved` (5): from the transport bound to the `L²` bound of the reading

Source of record: `the November 2 reference manuscript` (73 pages),
2683-2689, 4194-4196.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem w10_final {ν R c : ℝ} (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (g : Chart → Ten3)
    (hg : Measurable g) (r : ℝ) {N : ℝ → Space → ℝ} (hN0 : ∀ τ y, 0 ≤ N τ y)
    {F : ℝ → Space → Space} (hF : ∀ τ y, R * Real.sqrt ν ≤ ϱ y → ‖F τ y‖ ≤ N τ y)
    (K b : ℝ) (hK : 0 ≤ K) (hb : 0 ≤ b)
    (hI : ∫⁻ p in {p : Chart | ν * p.1 ≤ 1}, ‖coefOf R (w10Fn R ν N) p‖ₑ ^ (2 : ℝ)
        ∂(ageμ c (-3 / 2)) ≤
      ENNReal.ofReal (1 / (Real.pi * R ^ 2)) *
        (ENNReal.ofReal K * (ENNReal.ofReal b *
          IIIa.ltauLq (2 * c / R) 2 (IIIa.srcNorm (oldCutSrc R c r g)))) ^ (2 : ℝ)) :
    eLpNorm (wardYoungRead ν R F) 2 (ageμ c (-3 / 2)) ≤
      ENNReal.ofReal (K * b) * eLpNorm g 2 (ageμ c (-1 / 2)) := by
  have h1 := w10_elp_le (c := c) hν hR hN0 hF
  have h2 := w10_src_sq R c r g hR hc hg
  set S := IIIa.ltauLq (2 * c / R) 2 (IIIa.srcNorm (oldCutSrc R c r g)) with hS
  set G' := ∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2)) with hG'
  have hG'2 : ∫⁻ p, ‖g p‖ₑ ^ 2 ∂(ageμ c (-1 / 2)) = G' := by
    simp only [hG', ENNReal.rpow_two]
  rw [hG'2] at h2
  have hpi : 0 < Real.pi * R ^ 2 := by positivity
  have hx : ENNReal.ofReal (1 / (Real.pi * R ^ 2)) * ENNReal.ofReal (Real.pi * R ^ 2) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ hpi.ne']
    simp
  have hSS : S ^ (2 : ℝ) ≤ ENNReal.ofReal (Real.pi * R ^ 2) * G' := h2
  have key : ENNReal.ofReal (1 / (Real.pi * R ^ 2)) *
      (ENNReal.ofReal K * (ENNReal.ofReal b * S)) ^ (2 : ℝ) ≤
      ENNReal.ofReal (K * b) ^ (2 : ℝ) * G' := by
    have e1 : ENNReal.ofReal K * (ENNReal.ofReal b * S) = ENNReal.ofReal (K * b) * S := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hK]
    rw [e1, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    calc ENNReal.ofReal (1 / (Real.pi * R ^ 2)) *
          (ENNReal.ofReal (K * b) ^ (2 : ℝ) * S ^ (2 : ℝ))
        ≤ ENNReal.ofReal (1 / (Real.pi * R ^ 2)) *
          (ENNReal.ofReal (K * b) ^ (2 : ℝ) * (ENNReal.ofReal (Real.pi * R ^ 2) * G')) := by
          gcongr
      _ = (ENNReal.ofReal (1 / (Real.pi * R ^ 2)) * ENNReal.ofReal (Real.pi * R ^ 2)) *
            (ENNReal.ofReal (K * b) ^ (2 : ℝ) * G') := by ring
      _ = ENNReal.ofReal (K * b) ^ (2 : ℝ) * G' := by rw [hx, one_mul]
  have hg2 : eLpNorm g 2 (ageμ c (-1 / 2)) = G' ^ (1 / 2 : ℝ) := by
    have h2r : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), h2r]
  calc eLpNorm (wardYoungRead ν R F) 2 (ageμ c (-3 / 2))
      ≤ _ := h1
    _ ≤ (ENNReal.ofReal (1 / (Real.pi * R ^ 2)) *
          (ENNReal.ofReal K * (ENNReal.ofReal b * S)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hI (by norm_num)
    _ ≤ (ENNReal.ofReal (K * b) ^ (2 : ℝ) * G') ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow key (by norm_num)
    _ = ENNReal.ofReal (K * b) * eLpNorm g 2 (ageμ c (-1 / 2)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), ← ENNReal.rpow_mul,
          hg2]
        norm_num

end UnforcedLeray.Short.PartIIIb.Concrete
end
