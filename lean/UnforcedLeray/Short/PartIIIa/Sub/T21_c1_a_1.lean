import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff

/-- Pointwise identity for the angular-two profile on the positive real axis. -/
theorem seedPlanar_ofReal_eq (h : ℝ → ℂ) (r : ℝ) (hr : 0 < r) :
    UnforcedLeray.Short.PartI.seedPlanar h (r : ℂ) = h r := by
  have hn : ‖(r : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hz : (r : ℂ) / ((r : ℝ) : ℂ) = 1 := div_self (by exact_mod_cast hr.ne')
  unfold UnforcedLeray.Short.PartI.seedPlanar UnforcedLeray.Planar.NUE.Ang.ofProfile
    UnforcedLeray.Planar.NUE.Ang.angPhase
  rw [hn, hz, one_zpow, mul_one]

theorem seedSmoothRep_proof : UnforcedLeray.Short.IIIa.SeedSmoothRep := by
  unfold UnforcedLeray.Short.IIIa.SeedSmoothRep
  intro hMR hX
  obtain ⟨lam, h, hh, ℓ, hS⟩ := hX
  obtain ⟨_, _, h', hae, hsm, hder, _, _, _, _, _, _⟩ := hMR lam h hh ℓ hS
  have hae' : h' =ᵐ[UnforcedLeray.B0010.xGMeasure] h :=
    UnforcedLeray.B0012.xG_ac.ae_le hae
  have hh' : MemLp h' 2 UnforcedLeray.B0010.xGMeasure := hh.ae_eq hae'.symm
  have hLp : hh'.toLp h' = hh.toLp h := MemLp.toLp_congr hh' hh hae'
  have hS' : UnforcedLeray.Short.PartI.IsSeedXG lam (hh'.toLp h') ℓ := by
    rw [hLp]; exact hS
  have hcd : ContDiffOn ℝ ∞ (fun r : ℝ => UnforcedLeray.Short.PartI.seedPlanar h' (r : ℂ))
      (Ioi 0) :=
    (hsm.comp Complex.ofRealCLM.contDiff).contDiffOn.mono (subset_univ _)
  have hcd' : ContDiffOn ℝ ∞ h' (Ioi 0) :=
    hcd.congr (fun r hr => (seedPlanar_ofReal_eq h' r hr).symm)
  obtain ⟨C, N, hC⟩ := hder 0
  refine ⟨lam, h', hh', ℓ, hS', hsm, hcd', C, N, fun y => ?_⟩
  have := hC y
  rwa [norm_iteratedFDeriv_zero] at this
