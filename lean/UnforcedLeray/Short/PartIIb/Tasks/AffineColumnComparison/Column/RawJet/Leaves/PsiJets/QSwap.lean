import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_2_3
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.PsiJets.Core

/-!
# Part II-b, leaf `PartII-b:G4/3/6/2/3/2`: `PsiQSwap`

Source of record: `the November 2 reference manuscript` 261-291 (`v = ∇^⊥ψ`).
For `s > 0`, `∂_q ψ = v₁` (`perpendicularGradient`), and `∂_q ∂_s^l ψ = ∂_s^l ∂_q ψ`
by `psi_swap_core` (mixed partials commute with age derivatives, `PsiJets/Core.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

theorem psiQSwap_core : PsiQSwap := by
  intro ψ v hsp l s hs q t
  obtain ⟨hΨ, hV, hst⟩ := hsp
  have hKt : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => ψ x.1 (x.2, t))
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) :=
    hΨ.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)).contDiffOn
      (fun x hx => ⟨hx.1, Set.mem_univ _⟩)
  have hcore := psi_swap_core (fun x : ℝ × ℝ => ψ x.1 (x.2, t)) hKt l s hs q
  have hval : iteratedDeriv l (fun r => deriv (fun τ' => ψ r (τ', t)) q) s =
      iteratedDeriv l (fun r => v r (q, t)) s 1 := by
    have hfg : (fun r => deriv (fun τ' => ψ r (τ', t)) q) =ᶠ[𝓝 s]
        (fun r => v r (q, t) 1) := by
      filter_upwards [Ioi_mem_nhds hs] with r hr
      have hpX : deriv (fun τ' => ψ r (τ', t)) q =
          UnforcedLeray.GaussianVortex.partialX (ψ r) (q, t) := rfl
      rw [hpX, hst r (show 0 < r from hr) (q, t)]
      simp [UnforcedLeray.GaussianVortex.perpendicularGradient, UnforcedLeray.Train.toVec_one]
    rw [hfg.iteratedDeriv_eq l]
    have hp := psi_iteratedDeriv_apply (fun x => v x.1 x.2) hV 1 l hs (q, t)
    dsimp only at hp
    exact hp
  rw [← hval]
  exact hcore

end UnforcedLeray.Short.IIb

/-- **Mixed-partial swap in `q`** (SP 261-291), leaf `PartII-b:G4/3/6/2/3/2`. -/
theorem psiQSwap_proof : UnforcedLeray.Short.IIb.PsiQSwap :=
  UnforcedLeray.Short.IIb.psiQSwap_core
