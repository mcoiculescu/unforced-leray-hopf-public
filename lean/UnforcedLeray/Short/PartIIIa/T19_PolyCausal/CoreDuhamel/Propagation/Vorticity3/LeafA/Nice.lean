import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation.Vorticity3.LeafA.Nice.Source
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation.Vorticity3.LeafA.Nice.FlowKernel
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation.Vorticity3.LeafA.Nice.FlatTestIdent

/-!
# `PartIII-a:T19/2/3/2/3/1/1`: `CoreDuhamelNice` (SP 3504-3545)

Source of record: `the November 2 reference manuscript` (SP), lines 3504-3545.

Assembles `coreDuhamelNice_proof : UnforcedLeray.Short.IIIa.CoreDuhamelNice` from the three
submodules under `LeafA/Nice/`:
1. `Source.lean` (`CoreDuhamelNiceAux.niceSourceConstruct`): constructs the smooth Stokes-Oseen
   solution `(b_cl, G_cl)` for nice forces `F`, identifies `(b₀, G₀)` with `(b_cl, G_cl)` on
   `(0, coreEnd ν b)` via homogeneous causal uniqueness, and builds the `X_{9,c}^0` vorticity
   source `f` with norm continuity and `H¹_{9,c}` pairing.
2. `FlowKernel.lean` (`CoreDuhamelNiceAux.niceFlowKernelConstruct`): constructs the jointly
   measurable Duhamel kernel `k_ker`, Bochner Duhamel vorticity `ω_duh`, and Biot-Savart
   velocity/gradient `(u_duh, G_duh)`, and establishes the stream-test weak vorticity identity.
3. `FlatTestIdent.lean` (`CoreDuhamelNiceAux.nicePerturbVortEq`): extends the stream-test identity
   to core flat velocity tests via `y`-primitive cutoffs and applies `coreCausalHomogeneousZero` to
   identify `corePerturbVort` with `ω_duh` on a.e. slice `s ∈ (0, coreEnd ν b)`.
-/

open MeasureTheory Set

namespace UnforcedLeray.Short.IIIa

theorem coreDuhamelNice_proof : CoreDuhamelNice := by
  intro P hP K hK b hb
  obtain ⟨ν_src, hν_src, hSrc⟩ := CoreDuhamelNiceAux.niceSourceConstruct P hP K hK b hb
  have hb_pos : 0 < 2 * b := by linarith
  refine ⟨min (1 / 2) (min ((2 * b)⁻¹) ν_src),
    lt_min (by norm_num) (lt_min (inv_pos.2 hb_pos) hν_src), ?_⟩
  intro ν hν tr hflow μ A_m C_clock hclock F b₀ G₀ b_sol G_sol hF hd _hvw
  have hν0 : 0 < ν := hν.1
  have hν1 : ν ≤ 1 / 2 := hν.2.trans (min_le_left _ _)
  have hνb : ν ≤ (2 * b)⁻¹ := (hν.2.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hνs : ν ≤ ν_src := (hν.2.trans (min_le_right _ _)).trans (min_le_right _ _)
  obtain ⟨b_cl, G_cl, f, a_zero, M_f, ha0, hMf, hb_cl, hbcl_zero, _hGcl_zero, hf_zero,
    _hb0_eq, hG0_eq_cl, hsrc_Ioc, hf_cont, hf_ae_pair⟩ :=
    hSrc ν ⟨hν0, hνs⟩ tr μ A_m F b₀ G₀ b_sol G_sol hF hd
  obtain ⟨k_ker, ω_duh, u_duh, G_duh, huduh_meas, hGduh_meas, huduh_zero, _hGduh_zero,
    ⟨M_duh, hMduh, hduh_bd⟩, hduh_all, hduh_eq⟩ :=
    CoreDuhamelNiceAux.niceFlowKernelConstruct P hP K hK b hb ν hν0 hν1 hνb tr hflow μ hd.2.1
      C_clock hclock f a_zero M_f ha0 hMf hf_zero
      (fun t ht => ⟨(hsrc_Ioc t ht).2.2.1, (hsrc_Ioc t ht).2.2.2.1, (hsrc_Ioc t ht).2.2.2.2.1⟩)
      hf_cont
  have hae_pert := CoreDuhamelNiceAux.nicePerturbVortEq P hP K hK b hb ν hν0 hν1 hνb tr μ A_m F
    b₀ b_sol b_cl u_duh G₀ G_sol G_cl G_duh f ω_duh a_zero M_duh hd ha0 hMduh hb_cl hbcl_zero
    hG0_eq_cl
    (fun t ht =>
      have ht' := hsrc_Ioc t ⟨ht.1, ht.2.le⟩
      ⟨ht'.1, ht'.2.2.1, ht'.2.2.2.2.2⟩)
    huduh_meas hGduh_meas huduh_zero hduh_bd
    (fun s hs =>
      have hs' := hduh_all s hs
      ⟨hs'.1, hs'.2.2.1, hs'.2.2.2.1, hs'.2.2.2.2.1, hs'.2.2.2.2.2.1⟩)
    (fun ψ s₁ s₂ R₁ hs₁ hs₁₂ hs₂ hR₁ hψ_sm hψ_per hψ_supp => by
      have hd_eq : ∀ ρ x,
          ((deriv (fun ρ' => ψ ρ' x) ρ : ℝ) : ℂ) = deriv (fun ρ' => (ψ ρ' x : ℂ)) ρ := by
        intro ρ x
        let m_s : ℝ → ℝ := fun ρ' => ψ ρ' x
        have hm_sm := hψ_sm.comp (contDiff_id.prodMk (contDiff_const (c := x)))
        have hm_diff : Differentiable ℝ m_s := hm_sm.differentiable (by simp)
        have h2 : HasDerivAt m_s (deriv m_s ρ) ρ := (hm_diff ρ).hasDerivAt
        have h3 : HasDerivAt (fun ρ' => (ψ ρ' x : ℂ)) ((deriv m_s ρ : ℝ) : ℂ) ρ :=
          Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt ρ h2
        exact h3.deriv.symm
      simp_rw [hd_eq]
      exact hduh_eq ψ s₁ s₂ R₁ hs₁ hs₁₂ hs₂ hR₁ hψ_sm hψ_per hψ_supp)
  refine ⟨f, ?_, ?_⟩
  · filter_upwards [hf_ae_pair] with t ht ht_mem
    have ht' := hsrc_Ioc t ⟨ht_mem.1, ht_mem.2.le⟩
    exact ⟨ht'.2.2.1, ht'.2.2.2.1, ht ht_mem⟩
  · filter_upwards [hae_pert] with s hs hs_mem
    have hs' := hduh_all s hs_mem
    exact ⟨k_ker s, hs'.2.2.2.2.2.2.1, hs'.2.2.2.2.2.2.2.1,
      (hs hs_mem).trans hs'.2.2.2.2.2.2.2.2⟩

end UnforcedLeray.Short.IIIa
