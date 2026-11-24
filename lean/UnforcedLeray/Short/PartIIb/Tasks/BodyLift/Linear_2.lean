import UnforcedLeray.Short.PartIIb.Sub.PartIIb_P1_1
import UnforcedLeray.Short.PartIIb.Tasks.BodyLift.Norm
import UnforcedLeray.Short.PartIIb.Tasks.BodyLift.Linear_3
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm

/-!
# Part II-b, task `PartII-b:P1/1/2`: a.e. injectivity of the ring lift on `H_p` (`BLUniq`)

Source of record: `the November 2 reference manuscript`, lines 1902-1906.
If `NvC R (toProf g₁) =ᵃᵉ NvC R (toProf g₂)` then `g₁ = g₂`.

Proof: set `h = g₁ + (-1) • g₂`. By additivity and real homogeneity of the lift (`BLNvLin`,
`PartII-b:P1/1/3`) the lift of `h` vanishes a.e. Then the norm identity `phaseLpNorm_NvC`
(`PartII-b:T07`) gives `0 = (πR²)^{1/p} ‖h‖_{H_p}`, so `h = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

/-- The phase-normalised norm of the zero field vanishes. -/
theorem linear2_phaseLpNorm_zero (P r : ℝ) (hr : 0 < r) :
    phaseLpNorm P r (fun _ => (0 : CVec3)) = 0 := by
  unfold phaseLpNorm
  have h1 : (0 : ℝ≥0∞) ^ r = 0 := ENNReal.zero_rpow_of_pos hr
  simp only [enorm_zero, h1, lintegral_zero, mul_zero]
  exact ENNReal.zero_rpow_of_pos (one_div_pos.2 hr)

/-- **`PartII-b:P1/1/2`** `BLUniq`: a.e. equal ring lifts of `H_p` profiles force equal classes. -/
theorem blUniq_proof : UnforcedLeray.Short.IIb.BLUniq := by
  intro R c hR hc g₁ g₂ hae
  have hr : 0 < bgp := by norm_num [bgp]
  have hε : 0 < R⁻¹ := inv_pos.2 hR
  obtain ⟨h, hh⟩ : ∃ h : HpR c, h = g₁ + (-1 : ℝ) • g₂ := ⟨_, rfl⟩
  -- (1) the lift of `h` vanishes a.e.
  have hae0 : ∀ᵐ x : ℝ × Space, NvC R (toProf c h) x = 0 := by
    rw [hh]
    have e1 := (blNvLin_proof R c hc g₁ ((-1 : ℝ) • g₂)).1
    have e2 := (blNvLin_proof R c hc g₂ g₂).2 (-1)
    filter_upwards [e1, e2, hae] with x a b d
    rw [a, b]
    simp [d]
  -- (2) the norm identity for the lift of `h`
  have key := phaseLpNorm_NvC (c := c) (r := bgp) (ε := R⁻¹) hc hr hε (toProf c h)
    (toProf_periodic hc h) (toProf_aestronglyMeasurable hc h)
  rw [inv_inv] at key
  have hz : phaseLpNorm (2 * R⁻¹ * c) bgp (NvC R (toProf c h)) = 0 := by
    rw [phaseLpNorm_congr_ae' (G := fun _ : ℝ × Space => (0 : CVec3)) hae0]
    exact linear2_phaseLpNorm_zero _ _ hr
  rw [hz, hNorm_toProf hc h] at key
  -- (3) `0 = (πR²)^{1/p} ‖h‖`, hence `h = 0`
  have hK : 0 < (Real.pi * R ^ 2) ^ (1 / bgp) := by positivity
  have hprod : ENNReal.ofReal ((Real.pi * R ^ 2) ^ (1 / bgp)) * ‖h‖ₑ = 0 := key.symm
  have h1 : h = 0 := by
    rcases mul_eq_zero.1 hprod with h0 | h0
    · exact absurd (ENNReal.ofReal_eq_zero.1 h0) (not_le.2 hK)
    · exact enorm_eq_zero.1 h0
  have h2 : g₁ + (-1 : ℝ) • g₂ = 0 := by rw [← hh]; exact h1
  calc g₁ = (g₁ + (-1 : ℝ) • g₂) + g₂ := by simp
    _ = g₂ := by rw [h2, zero_add]

end UnforcedLeray.Short.IIb
