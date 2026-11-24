import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Time
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S1.Defs

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem tcTimeW : TCTimeW := by
  intro σ₁ σ₂ ν μ R P T τ y hctx
  obtain ⟨hσ, hν, hν1, hR1, hP, hμ, hT, hM, hA, hy⟩ := hctx
  have hμ' : -(1 / 4) < μ := lt_of_lt_of_le hσ hμ.1
  have hR : 0 < R := by linarith
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hrr : R * Real.sqrt (5 * ν / 6) < ϱ y := by
    have h1 : Real.sqrt (5 * ν / 6) < Real.sqrt ν :=
      Real.sqrt_lt_sqrt (by positivity) (by linarith)
    have h2 : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν := mul_lt_mul_of_pos_left h1 hR
    exact lt_of_lt_of_le h2 hy.1
  exact (tcr_psi_tau hν hμ' hr0 hP hT hM τ hrr).deriv

end UnforcedLeray.Short.PartIIIb.Concrete

end
