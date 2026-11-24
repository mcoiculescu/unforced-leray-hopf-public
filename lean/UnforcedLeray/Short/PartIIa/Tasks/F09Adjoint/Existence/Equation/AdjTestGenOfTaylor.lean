import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_1_3

/-!
# Part II-a, task `PartII-a:F09/1/3/2`: the generator identity from the Taylor expansion

Source `the November 2 reference manuscript`, lines 1403-1413.
Proves `AdjTestGenOfTaylor`: from `AdjPhaseTaylor` (`ψs` represents `x ↦ ⟪Φ, S(s)^* x⟫` with
`‖ψs - Φ + s L₀Φ‖ ≤ C s²`) the right derivative at `0` of `t ↦ ⟪Φ, S(t)^* x⟫` is `-⟪L₀Φ, x⟫`.
The quotient `t⁻¹(⟪Φ, S(t)^*x⟫ - ⟪Φ, x⟫)` equals `⟪t⁻¹(ψt - Φ), x⟫`, which differs from
`-⟪L₀Φ, x⟫` by `⟪t⁻¹(ψt - Φ + t L₀Φ), x⟫`, of size at most `‖⟪·, x⟫‖ C t`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- **Passage from the Taylor expansion to the generator identity** (task `PartII-a:F09/1/3/2`). -/
theorem adjTestGenOfTaylor : AdjTestGenOfTaylor := by
  unfold AdjTestGenOfTaylor AdjTestGen
  intro h P _ ν hν Φ hΦ x
  obtain ⟨C, hC0, hT⟩ := h P ν hν Φ hΦ
  -- the pairing with a fixed `x` is bounded uniformly in the first slot
  have hbound : ∀ ψ : Yq P (conjExp 2),
      ‖phasePairing P 2 ψ x‖ ≤ (‖phasePairing P 2‖ * ‖x‖) * ‖ψ‖ := by
    intro ψ
    calc ‖phasePairing P 2 ψ x‖ ≤ ‖phasePairing P 2 ψ‖ * ‖x‖ := (phasePairing P 2 ψ).le_opNorm x
      _ ≤ (‖phasePairing P 2‖ * ‖ψ‖) * ‖x‖ :=
          mul_le_mul_of_nonneg_right ((phasePairing P 2).le_opNorm ψ) (norm_nonneg x)
      _ = (‖phasePairing P 2‖ * ‖x‖) * ‖ψ‖ := by ring
  have hK0 : 0 ≤ ‖phasePairing P 2‖ * ‖x‖ := by positivity
  -- the bound tends to zero
  have hlim : Tendsto (fun t : ℝ => (‖phasePairing P 2‖ * ‖x‖) * (C * t)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => (‖phasePairing P 2‖ * ‖x‖) * (C * t)) :=
      continuous_const.mul (continuous_const.mul continuous_id)
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  -- the quotient is close to the limit, with error at most a multiple of `t`
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ‖(t⁻¹ : ℝ) • (phasePair P 2 Φ (adjT P ν t x) - phasePair P 2 Φ x)
        - (-(phasePair P 2 (L0 ν Φ) x))‖ ≤ (‖phasePairing P 2‖ * ‖x‖) * (C * t) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have ht0 : 0 < t := ht.1
    obtain ⟨ψ, hψ1, hψ2⟩ := hT t ht0 ht.2.le
    set D : Yq P (conjExp 2) :=
      ψ - testElem P (conjExp 2) Φ + (t : ℂ) • testElem P (conjExp 2) (L0 ν Φ) with hDdef
    have hct : ((t⁻¹ : ℝ) : ℂ) * (t : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ ht0.ne', Complex.ofReal_one]
    have hE : ∀ y, phasePair P 2 Φ y = phasePairing P 2 (testElem P (conjExp 2) Φ) y :=
      fun y => rfl
    have hF : ∀ y, phasePair P 2 (L0 ν Φ) y =
        phasePairing P 2 (testElem P (conjExp 2) (L0 ν Φ)) y := fun y => rfl
    have hD : phasePairing P 2 (((t⁻¹ : ℝ) : ℂ) • D) x
        = (t⁻¹ : ℝ) • (phasePairing P 2 ψ x - phasePairing P 2 (testElem P (conjExp 2) Φ) x)
          - (-(phasePairing P 2 (testElem P (conjExp 2) (L0 ν Φ)) x)) := by
      simp only [hDdef, map_smul, map_add, map_sub, smul_apply,
        add_apply, sub_apply, smul_eq_mul,
        Complex.real_smul]
      linear_combination (phasePairing P 2 (testElem P (conjExp 2) (L0 ν Φ)) x) * hct
    have hnorm := hbound (((t⁻¹ : ℝ) : ℂ) • D)
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 ht0.le)] at hnorm
    rw [hψ1 x, hE x, hF x, ← hD]
    calc ‖phasePairing P 2 (((t⁻¹ : ℝ) : ℂ) • D) x‖
        ≤ (‖phasePairing P 2‖ * ‖x‖) * (t⁻¹ * ‖D‖) := hnorm
      _ ≤ (‖phasePairing P 2‖ * ‖x‖) * (t⁻¹ * (C * t ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ hK0
          exact mul_le_mul_of_nonneg_left hψ2 (inv_nonneg.2 ht0.le)
      _ = (‖phasePairing P 2‖ * ‖x‖) * (C * t) := by
          congr 1
          calc t⁻¹ * (C * t ^ 2) = C * t * (t⁻¹ * t) := by ring
            _ = C * t := by rw [inv_mul_cancel₀ ht0.ne', mul_one]
  have hfin := squeeze_zero_norm' hev hlim
  exact (tendsto_sub_nhds_zero_iff).1 hfin

end UnforcedLeray.Short.PartIIa
