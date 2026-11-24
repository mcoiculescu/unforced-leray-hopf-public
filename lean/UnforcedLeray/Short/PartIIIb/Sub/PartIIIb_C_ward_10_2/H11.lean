import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_2.H10
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T3b
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T3c
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.L1_far
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.XAdd.Prim

/-!
# Helpers for `wardStreamCorrYoungL2_proved` (11): smoothness, decay and partials of the primitive

Source of record: `the November 2 reference manuscript` (73 pages), 4176-4186:
`∂_rΨ_Z = rZ_z`, `∂_zΨ_Z = -rZ_r` for `Z = X₀` of old `L²` data.  The far-field decay is
`SepFarDecay` (`|W|, |∇W| ≤ Cϱ⁻³` for `ϱ ≥ 2r_o`) plus continuity on a compact piece.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

section Ctx

variable {ν μ R c : ℝ} {g : Chart → Ten3}

/-- The cut old source and the equality of `X₀` with the separated field of the cut source. -/
theorem w2_ctx (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hg : IsOldL2 c ν g) :
    IIIa.IsSepSource (2 * c / R) (R * Real.sqrt (5 * ν / 6))
        (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) ∧
      SepMoment (2 * c / R) (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) ∧
      wardX0 ν μ R c g = sepX0 ν μ (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) := by
  obtain ⟨hS, hM, hae⟩ := xa_oldReg hc hν hR hg
  refine ⟨hS, hM, ?_⟩
  exact w10_X0_eq hν hR hc hg

theorem w2_smooth (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ) (hg : IsOldL2 c ν g)
    (τ : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (wardX0 ν μ R c g τ) (youngOpen ν R) := by
  obtain ⟨hS, hM, hZ⟩ := w2_ctx (μ := μ) hν hR hc hg
  set r0 : ℝ := R * Real.sqrt (5 * ν / 6) with hr0
  have hr0nn : 0 ≤ r0 := by positivity
  have hP : 0 < 2 * c / R := by positivity
  set T := oldCutSrc R c r0 g with hT
  have hm1 : -(1 / 4) < ((μ : ℂ)).re := by simpa using hμ
  have hm2 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  have hWa : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => IIIa.sepW ν (μ : ℂ) T z τ)
      {y : Space | r0 < ϱ y} :=
    contDiffOn_pi.2 (fun i => sepW_contDiffOn_top ν (μ : ℂ) r0 (2 * c / R) T hν hm1 hr0nn hP hS hM τ i)
  have hWb : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => IIIa.sepW ν ((μ : ℂ) + 1) T z τ)
      {y : Space | r0 < ϱ y} :=
    contDiffOn_pi.2 (fun i => sepW_contDiffOn_top ν ((μ : ℂ) + 1) r0 (2 * c / R) T hν hm2 hr0nn hP hS hM τ i)
  have : wardX0 ν μ R c g τ = fun z => w10Re (IIIa.sepW ν (μ : ℂ) T z τ - IIIa.sepW ν ((μ : ℂ) + 1) T z τ) := by
    rw [hZ]
    funext z
    rw [sepX0_eq_sub]
    simp only [sepWre, w10Re_apply]
    ext i
    simp
  rw [this]
  exact w10Re.contDiff.comp_contDiffOn (hWa.sub hWb)

end Ctx

end UnforcedLeray.Short.PartIIIb.Concrete
end
