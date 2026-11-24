import UnforcedLeray.Short.PartIIb.Tasks.GreenSelector.CylCoupledPairing.Assemble

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray CCP

theorem cylCoupledPairingCLM_proof : UnforcedLeray.Short.IIb.CylCoupledPairingCLM := by
  intro m hm ν c H tr φ hν hc hH hφ
  have hm' : 1 / 2 < m := by linarith
  obtain ⟨M, hM, hMb⟩ := main_bound hc hm' tr H hH hφ
  have key : ∀ r : ℝ, ∃ T : Xmc c m →L[ℝ] ℝ, r ∈ Icc 0 H → ‖T‖ ≤ M ∧ ∀ w : Xmc c m,
      IntegrableOn (cylCoupledIntegrand tr w r φ) (B0579.cell c) volume ∧
      T w = ∫ x in B0579.cell c, cylCoupledIntegrand tr w r φ x := by
    intro r
    by_cases hr : r ∈ Icc 0 H
    · obtain ⟨T, hT, hT2⟩ := clm_of_bound (c := c) (m := m)
        (fun w => cylCoupledIntegrand tr ⇑w r φ) M hM (fun w => (hMb r hr w).1)
        (fun w => (hMb r hr w).2)
        (fun w1 w2 => by
          filter_upwards [coe_add_ae w1 w2, K_add_ae hc hm' w1 w2] with x h hK
          rw [integrand_eq, integrand_eq, integrand_eq, h, hK]
          simp only [PiLp.add_apply]
          ring)
        (fun a w => by
          filter_upwards [coe_smul_ae a w] with x h
          rw [integrand_eq, integrand_eq, h, K_smul hm' a w x]
          simp only [PiLp.smul_apply, smul_eq_mul]
          ring)
      exact ⟨T, fun _ => ⟨hT, hT2⟩⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose L hL using key
  exact ⟨M, L, hM, fun r hr => hL r hr⟩

end UnforcedLeray.Short.IIb
