import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_1.H7

/-!
# Helpers for `wardX0YoungL2_proved` (8): the single-`μ` young bounds

Source of record: `the November 2 reference manuscript` (73 pages),
3631-3646 (`sep:young`), 4171-4174, 4194-4196, 2683-2689.

For `W_m = Re sepW` of the cut old source `T`, the young chart reading of `W_m` and of each partial
`∂_kW_m` is bounded by `C‖g‖_{L²(s^{-1/2}dς)}` (`m > -1/4`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem w10_varrho_refl (y : Space) : ϱ (actM reflM y) = ϱ y := by
  unfold ϱ
  congr 1
  simp [actM, reflM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The cut old source of old `L²` data: separated, finite moment, axisymmetric. -/
theorem w10_ctx {ν R c : ℝ} (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) {g : Chart → Ten3}
    (hg : IsOldL2 c ν g) :
    IIIa.IsSepSource (2 * c / R) (R * Real.sqrt (5 * ν / 6))
        (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) ∧
      SepMoment (2 * c / R) (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) ∧
      IsAxiSource (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) := by
  obtain ⟨hS, hM, -⟩ := xa_oldReg hc hν hR hg
  refine ⟨hS, hM, ?_, ?_⟩
  · intro co si h τ z
    have hϱ : NearInst.hRad (actM (rotM co si) z) = NearInst.hRad z := w10_varrho_act h z
    unfold oldCutSrc
    rw [hϱ]
    split_ifs with hz
    · exact oldPhysRotEquiv co si h R c g τ z
    · simp
  · intro τ z
    have hϱ : NearInst.hRad (actM reflM z) = NearInst.hRad z := w10_varrho_refl z
    unfold oldCutSrc
    rw [hϱ]
    split_ifs with hz
    · exact oldPhysReflEquiv R c g τ z
    · simp

/-- Rotation datum: the rotation taking the meridian point to `y`. -/
theorem w10_rotdatum {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} (hAx : IsAxiSource T) {y : Space}
    (hρ : 0 < ϱ y) :
    ∃ M : Matrix (Fin 3) (Fin 3) ℝ, M * M.transpose = 1 ∧
      (∀ τ z, T τ (actM M z) = M * T τ z * M.transpose) ∧ actM M (meridPt y) = y ∧
      ∀ z, ϱ (actM M z) = ϱ z := by
  have hco := w10_cos hρ
  exact ⟨rotM (y 0 / ϱ y) (y 1 / ϱ y), rotM_orth hco, fun τ z => hAx.1 _ _ hco τ z,
    w10_mer hρ, fun z => w10_varrho_act hco z⟩

end UnforcedLeray.Short.PartIIIb.Concrete
end
