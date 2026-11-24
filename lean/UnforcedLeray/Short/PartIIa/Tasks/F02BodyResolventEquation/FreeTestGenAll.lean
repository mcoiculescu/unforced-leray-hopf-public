import UnforcedLeray.Short.PartIIa.Sub.F02
import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation.PhaseAdjointTaylor

/-!
# Part II-a, task `PartII-a:F02/11`: the generator identity on phase tests, by duality

Source of record: `the November 2 reference manuscript`, lines 1363-1370
("using the generator of `S_ν` on the tests"). Proves the Prop `FreeTestGenAll` of `Sub/F02.lean`
from the adjoint Taylor bound `PhaseAdjointTaylor` (task `PartII-a:F02/10`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp

/-- **The generator identity on phase tests, by duality** (task `PartII-a:F02/11`). -/
theorem freeTestGenAll : UnforcedLeray.Short.PartIIa.FreeTestGenAll := by
  intro r _ h1 h3 P _ nu hnu Φ hΦ x
  obtain ⟨C, hC0, hT⟩ := phaseAdjointTaylor r h1 h3 P nu hnu Φ hΦ
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = ‖(phasePairing P r : Yq P (conjExp r) →L[ℂ] Yq P r →L[ℂ] ℂ)‖ :=
    ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact norm_nonneg (phasePairing P r : Yq P (conjExp r) →L[ℂ] Yq P r →L[ℂ] ℂ)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun s : ℝ => C * K * ‖x‖ * s) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun s : ℝ => C * K * ‖x‖ * s) (𝓝 0) (𝓝 (C * K * ‖x‖ * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    simpa using h0.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with s hs
  obtain ⟨ψs, hψs1, hψs2⟩ := hT s hs.1 hs.2.le
  have hs0 : s ≠ 0 := hs.1.ne'
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
  have hsinv : (s : ℂ)⁻¹ * (s : ℂ) = 1 := inv_mul_cancel₀ hsC
  have hE : phasePairing P r ψs x - phasePairing P r (testElem P (conjExp r) Φ) x
      - (s : ℂ) * phasePairing P r (testElem P (conjExp r) (F02.genT nu Φ)) x
      = phasePairing P r (ψs - testElem P (conjExp r) Φ
          - (s : ℂ) • testElem P (conjExp r) (F02.genT nu Φ)) x := by
    simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]
  have hbound : ‖phasePairing P r (ψs - testElem P (conjExp r) Φ
          - (s : ℂ) • testElem P (conjExp r) (F02.genT nu Φ)) x‖ ≤ K * (C * s ^ 2) * ‖x‖ := by
    have hop : ‖phasePairing P r (ψs - testElem P (conjExp r) Φ
          - (s : ℂ) • testElem P (conjExp r) (F02.genT nu Φ)) x‖
        ≤ K * ‖ψs - testElem P (conjExp r) Φ - (s : ℂ) • testElem P (conjExp r) (F02.genT nu Φ)‖
          * ‖x‖ := by
      rw [hKdef]
      exact ContinuousLinearMap.le_opNorm₂ (phasePairing P r) _ x
    exact hop.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hψs2 hK0) (norm_nonneg _))
  rw [hψs1 x]
  show ‖(s⁻¹ : ℝ) • (phasePairing P r ψs x - phasePairing P r (testElem P (conjExp r) Φ) x)
      - phasePairing P r (testElem P (conjExp r) (F02.genT nu Φ)) x‖ ≤ _
  have hgoal : (s⁻¹ : ℝ) • (phasePairing P r ψs x - phasePairing P r (testElem P (conjExp r) Φ) x)
      - phasePairing P r (testElem P (conjExp r) (F02.genT nu Φ)) x
      = (s⁻¹ : ℝ) • phasePairing P r (ψs - testElem P (conjExp r) Φ
          - (s : ℂ) • testElem P (conjExp r) (F02.genT nu Φ)) x := by
    rw [← hE, Complex.real_smul, Complex.real_smul, Complex.ofReal_inv]
    linear_combination (phasePairing P r (testElem P (conjExp r) (F02.genT nu Φ)) x) * hsinv
  rw [hgoal, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.1.le)]
  have hsi : s⁻¹ * s = 1 := inv_mul_cancel₀ hs0
  calc s⁻¹ * ‖phasePairing P r (ψs - testElem P (conjExp r) Φ
          - (s : ℂ) • testElem P (conjExp r) (F02.genT nu Φ)) x‖
      ≤ s⁻¹ * (K * (C * s ^ 2) * ‖x‖) := mul_le_mul_of_nonneg_left hbound (inv_nonneg.2 hs.1.le)
    _ = C * K * ‖x‖ * s := by linear_combination (C * K * ‖x‖ * s) * hsi

end UnforcedLeray.Short.PartIIa
