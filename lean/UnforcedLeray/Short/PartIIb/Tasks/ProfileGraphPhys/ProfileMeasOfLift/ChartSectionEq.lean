import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_2_1

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace UnforcedLeray.Short.IIb

theorem chartSectionEq_proof : UnforcedLeray.Short.IIb.ChartSectionEq := by
  intro R z θ hR hs
  rcases z with ⟨s, ξ, η⟩
  have hs' : (0 : ℝ) < s := hs
  have hR0 : R ≠ 0 := hR.ne'
  have hsp : 0 < Real.sqrt s := Real.sqrt_pos.2 hs'
  have hsp0 : Real.sqrt s ≠ 0 := hsp.ne'
  have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs'.le
  have ha : 0 < R / Real.sqrt s := div_pos hR hsp
  have h0 : (psiSpace R (s, (ξ, η)) θ) 0 = R / Real.sqrt s * Real.cos θ := by
    simp [psiSpace]
  have h1 : (psiSpace R (s, (ξ, η)) θ) 1 = R / Real.sqrt s * Real.sin θ := by
    simp [psiSpace]
  have h2 : (psiSpace R (s, (ξ, η)) θ) 2 = η * (R / Real.sqrt s) / R := by
    simp [psiSpace]
  have hϱ : UnforcedLeray.Axi.ϱ (psiSpace R (s, (ξ, η)) θ) = R / Real.sqrt s := by
    unfold UnforcedLeray.Axi.ϱ
    rw [h0, h1]
    have key : (R / Real.sqrt s * Real.cos θ) ^ 2 + (R / Real.sqrt s * Real.sin θ) ^ 2
        = (R / Real.sqrt s) ^ 2 := by
      linear_combination (R / Real.sqrt s) ^ 2 * Real.sin_sq_add_cos_sq θ
    rw [key]
    exact Real.sqrt_sq ha.le
  have hage : UnforcedLeray.Axi.age R (psiSpace R (s, (ξ, η)) θ) = s := by
    unfold UnforcedLeray.Axi.age
    rw [hϱ, div_pow, hsq]
    field_simp
  have htrans : UnforcedLeray.Axi.trans R (psiSpace R (s, (ξ, η)) θ) = η := by
    unfold UnforcedLeray.Axi.trans
    rw [h2, hϱ]
    field_simp
  have hphase : UnforcedLeray.Axi.phase R (psiTau R (s, (ξ, η))) (psiSpace R (s, (ξ, η)) θ)
      = ξ := by
    unfold UnforcedLeray.Axi.phase psiTau
    rw [hage]
    field_simp
    ring
  unfold UnforcedLeray.Axi.chart
  rw [hage, hphase, htrans]

end UnforcedLeray.Short.IIb
