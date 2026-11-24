import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_2_3
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.PsiJets.Core

/-!
# Part II-b, leaf `PartII-b:G4/3/6/2/3/1`: `PsiEtaSwap`

Source of record: `the November 2 reference manuscript` 261-291 (`v = ∇^⊥ψ`).
For `s > 0`, `∂_η ψ = -v₀` (`perpendicularGradient`), and `∂_η ∂_s^l ψ = ∂_s^l ∂_η ψ`
by `psi_swap_core` (mixed partials commute with age derivatives, `PsiJets/Core.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

theorem psiEtaSwap_core : PsiEtaSwap := by
  intro ψ v hsp l s hs q t
  obtain ⟨hΨ, hV, hst⟩ := hsp
  have hKq : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => ψ x.1 (q, x.2))
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) :=
    hΨ.comp (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)).contDiffOn
      (fun x hx => ⟨hx.1, Set.mem_univ _⟩)
  have hcore := psi_swap_core (fun x : ℝ × ℝ => ψ x.1 (q, x.2)) hKq l s hs t
  have hval : iteratedDeriv l (fun r => deriv (fun τ' => ψ r (q, τ')) t) s =
      -(iteratedDeriv l (fun r => v r (q, t)) s 0) := by
    have hfg : (fun r => deriv (fun τ' => ψ r (q, τ')) t) =ᶠ[𝓝 s]
        (fun r => -(v r (q, t) 0)) := by
      filter_upwards [Ioi_mem_nhds hs] with r hr
      have hpY : deriv (fun τ' => ψ r (q, τ')) t =
          UnforcedLeray.GaussianVortex.partialY (ψ r) (q, t) := rfl
      rw [hpY, hst r (show 0 < r from hr) (q, t)]
      simp [UnforcedLeray.GaussianVortex.perpendicularGradient, UnforcedLeray.Train.toVec_zero]
    rw [hfg.iteratedDeriv_eq l, iteratedDeriv_fun_neg]
    have hp := psi_iteratedDeriv_apply (fun x => v x.1 x.2) hV 0 l hs (q, t)
    dsimp only at hp
    rw [hp]
  rw [← hval]
  exact hcore

end UnforcedLeray.Short.IIb

/-- **Mixed-partial swap** (SP 261-291), leaf `PartII-b:G4/3/6/2/3/1`. -/
theorem psiEtaSwap_proof : UnforcedLeray.Short.IIb.PsiEtaSwap :=
  UnforcedLeray.Short.IIb.psiEtaSwap_core
