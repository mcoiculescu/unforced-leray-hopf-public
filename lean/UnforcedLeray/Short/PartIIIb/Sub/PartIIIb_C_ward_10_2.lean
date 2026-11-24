import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_2.H15

/-!
# `PartIII-b:C/ward/10/2`: `WardStreamCorrYoungL2`

Source of record: `the November 2 reference manuscript` (73 pages), 4180-4186,
3687-3713.

The correction is `w2a(ϱ)Ψ_{X₀}(ϱ, y₃) e_z` with `w2a` supported on `R√ν ≤ ϱ ≤ R√(5ν/4)`, bounded
with its derivative there.  Its value is dominated by `C|Ψ|` (the young `L²` bound of `|Ψ|e_z` is
`w2_psiBd`, the majorant of 3687-3713) and its first partials by `C|Ψ| + C ϱ|X₀|`
(`∂_rΨ = rX₀,z`, `∂_zΨ = -rX₀,r`, `w2_corr_pd_bound`), so the young `L²` bound of `X₀`
(`wardX0YoungL2_proved`) gives the claim.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem wardStreamCorrYoungL2_proved : WardStreamCorrYoungL2 := by
  classical
  intro ν μ R c χy hχ hν hR hc hμ
  obtain ⟨CX, hX⟩ := wardX0YoungL2_proved ν μ R c hν hR hc hμ
  set r2 : ℝ := R * Real.sqrt (5 * ν / 4) with hr2
  have hr2nn : 0 ≤ r2 := by positivity
  obtain ⟨K, hK, hΨ⟩ := w2_psiBd hν hR hc hμ r2
  obtain ⟨Ca, Cb, hCa, hCb, hab⟩ := w2a_bound hχ hν hR
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hX1 : ∀ g : Chart → Ten3, IsOldL2 c ν g → YoungL2Le c ν R CX (wardX0 ν μ R c g) g :=
    fun g hg => (hX g hg).1
  refine ⟨(Ca + Cb) * K + (2 * Ca * r2) * max CX 0, fun g hg => ?_⟩
  have hm0 : 0 ≤ max CX 0 := le_max_right _ _
  have hval : ∀ τ y, R * Real.sqrt ν ≤ ϱ y →
      ‖wardStreamCorr ν R χy (wardX0 ν μ R c g) τ y‖ ≤
        Ca * w2N ν μ R c r2 g τ y + 0 * ‖wardX0 ν μ R c g τ y‖ := by
    intro τ y hy
    rw [wardStreamCorr_eq, norm_smul, wyl_norm_coordinateVector, mul_one, Real.norm_eq_abs,
      abs_mul, zero_mul, add_zero]
    by_cases h2 : ϱ y ≤ r2
    · have hN : w2N ν μ R c r2 g τ y = |outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2)| := by
        unfold w2N; rw [if_pos h2]
      rw [hN]
      exact mul_le_mul_of_nonneg_right (hab (ϱ y) hy h2).1 (abs_nonneg _)
    · rw [w2a_zero_of_gt hχ hν hR (not_le.1 h2), abs_zero, zero_mul]
      exact mul_nonneg hCa (w2N_nonneg _ _ _ _ _ _ _ _)
  have hpd : ∀ (j : Fin 3) τ y, R * Real.sqrt ν ≤ ϱ y →
      ‖physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y‖ ≤
        Cb * w2N ν μ R c r2 g τ y + (2 * Ca * r2) * ‖wardX0 ν μ R c g τ y‖ := by
    intro j τ y hy
    have hyU : y ∈ youngOpen ν R := lt_of_lt_of_le hrr hy
    have hb := w2_corr_pd_bound hχ hν hR hc hμ hg τ j hyU
    refine hb.trans ?_
    by_cases h2 : ϱ y ≤ r2
    · have hN : w2N ν μ R c r2 g τ y = |outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2)| := by
        unfold w2N; rw [if_pos h2]
      rw [hN]
      obtain ⟨h1, h1'⟩ := hab (ϱ y) hy h2
      have hZ := norm_nonneg (wardX0 ν μ R c g τ y)
      have hρ : 0 ≤ ϱ y := ϱ_nonneg y
      have e1 : |deriv (w2a ν R χy) (ϱ y)| * |outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2)| ≤
          Cb * |outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2)| :=
        mul_le_mul_of_nonneg_right h1' (abs_nonneg _)
      have e2 : |w2a ν R χy (ϱ y)| * (2 * ϱ y * ‖wardX0 ν μ R c g τ y‖) ≤
          (2 * Ca * r2) * ‖wardX0 ν μ R c g τ y‖ := by
        calc _ ≤ Ca * (2 * r2 * ‖wardX0 ν μ R c g τ y‖) :=
              mul_le_mul h1 (by nlinarith) (by positivity) hCa
          _ = _ := by ring
      linarith
    · have h2' := not_le.1 h2
      rw [w2a_zero_of_gt hχ hν hR h2', w2a_deriv_zero_of_gt hχ hν hR h2']
      simp only [abs_zero, zero_mul]
      have := w2N_nonneg ν μ R c r2 g τ y
      have hZ := norm_nonneg (wardX0 ν μ R c g τ y)
      have e3 := mul_nonneg hCb this
      have e4 := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hCa) hr2nn) hZ
      linarith
  constructor
  · refine w2_young_mono (w2_young_of_pt hν hR hc hμ r2 hX1 hg
      (w10_read_meas (w2_corr_measurable hg)).aestronglyMeasurable hK (hΨ g hg) hCa le_rfl hval) ?_
    nlinarith [mul_nonneg hCb hK, mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hCa) hr2nn) hm0]
  · intro j
    have hUo : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
    have hPd := w10_meas_pd (w2_corr_measurable (χy := χy) (μ := μ) hg) hUo.measurableSet
      (fun τ y hy => w2_corr_diff hχ hν hR hc hμ hg τ hy) j
    have hread : wardYoungRead ν R
        (fun τ => physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j) =
        wardYoungRead ν R (fun τ y => if y ∈ youngOpen ν R then
          physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y else 0) := by
      refine w10_read_congr hν hR fun τ y hy => ?_
      have : y ∈ youngOpen ν R := lt_of_lt_of_le hrr hy
      simp [this]
    have hFm : AEStronglyMeasurable (wardYoungRead ν R
        (fun τ => physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j)) (ageμ c (-3 / 2)) := by
      rw [hread]
      exact (w10_read_meas hPd).aestronglyMeasurable
    refine w2_young_mono (w2_young_of_pt hν hR hc hμ r2 hX1 hg hFm hK (hΨ g hg) hCb
      (by positivity) (fun τ y hy => hpd j τ y hy)) ?_
    nlinarith [mul_nonneg hCa hK]

end UnforcedLeray.Short.PartIIIb.Concrete
end
