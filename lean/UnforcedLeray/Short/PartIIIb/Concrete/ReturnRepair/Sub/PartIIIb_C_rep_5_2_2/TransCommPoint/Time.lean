import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_2_2_11
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Reg.Tau

/-!
# `PartIII-b:C/rep/5/2/2/11/3` : `TCTime`, `∂_τ` commutes with the outward primitive

Source `the November 2 reference manuscript`
4176-4214, 4181-4192 (`𝒞_y` is phase independent).  The outward primitive
`Ψ_Z(r,z) = -∫_r^∞ ρ Z_z(ρ,0,z) dρ` of `Z = X₀` is differentiated under the integral sign
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, `Reg/Tau.lean`) with the phase-uniform
majorant `C(1+|z|)(ρ - r_o)^{-3/2}` of `ρ ∂_τX₀_z` (`Int/Half2.lean`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem tcr_psi_tau {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ : ℝ) {y : Space}
    (hy : rOut < ϱ y) :
    HasDerivAt (fun t => psiFld (sepX0 ν μ T) t y)
      (psiFld (fun t y' => deriv (fun s => sepX0 ν μ T s y') t) τ y) τ := by
  have h := tcr_outPrim_tau hν hμ hr hP hT hM τ hy
  exact h.smul_const (coordinateVector 2)

/-- **`TCTime`** (source 4176-4214). -/
theorem tcTime : TCTime := by
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
