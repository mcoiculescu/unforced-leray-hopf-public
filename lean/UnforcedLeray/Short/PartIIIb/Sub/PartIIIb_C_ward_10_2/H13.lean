import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_2.H12
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T9

/-!
# Helpers for `wardStreamCorrYoungL2_proved` (13): equivariance and axisymmetry of `X₀`

Source of record: `the November 2 reference manuscript` (73 pages), 4171-4178.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

section Ctx

variable {ν μ R c : ℝ} {g : Chart → Ten3}

theorem w2_actM_sub (M : Matrix (Fin 3) (Fin 3) ℝ) (a b : Space) :
    actM M (a - b) = actM M a - actM M b := by
  ext i
  simp [actM, Matrix.mulVec_sub]

theorem w2_X0_equiv (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ)
    (hg : IsOldL2 c ν g) {M : Matrix (Fin 3) (Fin 3) ℝ} (hMo : M * M.transpose = 1)
    (hTM : ∀ τ z, oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g τ (actM M z) =
      M * oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g τ z * M.transpose) (τ : ℝ) (y : Space)
    (hy : R * Real.sqrt (5 * ν / 6) < ϱ y) :
    wardX0 ν μ R c g τ (actM M y) = actM M (wardX0 ν μ R c g τ y) := by
  obtain ⟨hS, hM, -⟩ := w10_ctx hν hR hc hg
  have hr : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  rw [w10_X0_eq hν hR hc hg, sepX0_eq_sub, sepX0_eq_sub, w2_actM_sub,
    w10_equivV hν hμ hr hP hS hM hMo hTM τ y hy,
    w10_equivV hν (by linarith : -(1 / 4) < μ + 1) hr hP hS hM hMo hTM τ y hy]

theorem w2_norm_merid (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ)
    (hg : IsOldL2 c ν g) (τ : ℝ) (y : Space) (hy : R * Real.sqrt (5 * ν / 6) < ϱ y) :
    ‖wardX0 ν μ R c g τ (meridPt y)‖ = ‖wardX0 ν μ R c g τ y‖ := by
  obtain ⟨hS, hM, hAx⟩ := w10_ctx hν hR hc hg
  have hr : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hρ : 0 < ϱ y := lt_of_le_of_lt hr hy
  obtain ⟨M, hMo, hTM, hmer, -⟩ := w10_rotdatum hAx hρ
  have hmU : R * Real.sqrt (5 * ν / 6) < ϱ (meridPt y) := by
    rw [w10_varrho_meridPt]; exact hy
  have e := w2_X0_equiv hν hR hc hμ hg hMo hTM τ (meridPt y) hmU
  rw [hmer] at e
  rw [e, norm_actM hMo]

theorem w2_axi (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ)
    (hg : IsOldL2 c ν g) : AxiNoSwirlOn (youngOpen ν R) (wardX0 ν μ R c g) := by
  obtain ⟨hS, hM, hAx⟩ := w10_ctx hν hR hc hg
  have hr : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  intro τ y hy hax
  have hyr : R * Real.sqrt (5 * ν / 6) < ϱ y := hy
  have hρ : 0 < ϱ y := lt_of_le_of_lt hr hyr
  have hρ2 : ϱ y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Axi.ϱ_sq y
  have hco := w10_cos hρ
  have hmU : R * Real.sqrt (5 * ν / 6) < ϱ (meridPt y) := by
    rw [w10_varrho_meridPt]; exact hyr
  have hmer := w10_mer hρ
  have hfix : actM reflM (meridPt y) = meridPt y := by
    ext i
    fin_cases i <;> simp [actM, reflM, meridPt, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have e1 := w2_X0_equiv hν hR hc hμ hg (rotM_orth hco) (hAx.1 _ _ hco) τ (meridPt y) hmU
  have e2 := w2_X0_equiv hν hR hc hμ hg reflM_orth hAx.2 τ (meridPt y) hmU
  rw [hmer] at e1
  rw [hfix] at e2
  have h1 : wardX0 ν μ R c g τ (meridPt y) 1 = 0 := by
    have := congrArg (fun w : Space => w 1) e2
    simp [actM, reflM, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this
    linarith
  rw [e1]
  ext i
  fin_cases i <;>
    simp [actM, rotM, frameL_apply, eR, hor, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1] <;>
    field_simp

end Ctx

end UnforcedLeray.Short.PartIIIb.Concrete
end
