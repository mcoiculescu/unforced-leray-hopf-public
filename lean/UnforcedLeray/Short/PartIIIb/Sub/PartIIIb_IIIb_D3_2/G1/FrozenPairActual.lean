import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.Org
import UnforcedLeray.Short.PartIIIb.Concrete.YoungBlocks
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Setting
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.FlatPin
import UnforcedLeray.Short.PartIIIb.Proofs.Young.Blocks
import UnforcedLeray.Short.PartIIIb.Proofs.Young.FrozenPairC

/-!
# `ORG:D3/2/G1/2`: the frozen pair for actual flat sequences (source 4407-4412)

Shift the index by `M` so that all the `∀ n` hypotheses of the concrete Young theorem hold, apply
`youngFrozenPairC_holds` through `blockSetup_of_laws` and `blocksFromRetained_holds`, and unshift.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif

open ConcreteYF

namespace G1

/-- Index shift of `RetainedBlocks` (the body is stated with `pk n`, `ν n`, `δ n`). -/
theorem retainedBlocks_shift_frozen (pk : ℕ → YoungPkg) (ν : ℕ → ℝ) (lam κ : ℂ) (Sg α : ℝ)
    (δ : ℕ → ℝ) (M : ℕ) (h : RetainedBlocks pk ν lam κ Sg α δ) :
    RetainedBlocks (fun n => pk (n + M)) (fun n => ν (n + M)) lam κ Sg α (fun n => δ (n + M)) := by
  unfold RetainedBlocks at h ⊢
  obtain ⟨C, g, N, hC, hg, hR⟩ := h
  refine ⟨C, g, N, hC, hg, fun n hn => ?_⟩
  exact hR (n + M) (by omega)

/-- **The frozen pair for actual flat sequences** (source 4407-4412). -/
theorem youngFrozenPair_actual (D : SeqData) (h : G1.YoungSourceFacts D) : ForActual D fun S => YoungFrozenPair (fun n => (S n).pk) (nu D) D.Pl.eigenvalue D.Pl.kappa 2 1.1 := by
  unfold ForActual
  intro dm dp hD κ hκ m hfact hm S hS
  obtain ⟨N0, δ, ⟨Cb, hb⟩, ⟨Cd, hd⟩, hR⟩ := h dm dp hD κ hκ m hm S hS
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp hS
  obtain ⟨M, hM0, hM1⟩ : ∃ M, N0 ≤ M ∧ N1 ≤ M := ⟨N0 + N1, by omega, by omega⟩
  -- the laws of the shifted packages
  have hLaw : ∀ n, ∃ f : (S (n + M)).pk.X → (S (n + M)).pk.X, YoungLaws (S (n + M)).pk f := by
    intro n
    obtain ⟨FI, hFI⟩ := hN1 (n + M) (by omega)
    have hpk : (S (n + M)).pk = FlatSettingInst.actualPk FI :=
      congrArg ConcreteYF.FlatSetting.pk hFI
    rw [hpk]
    exact ⟨FlatSettingInst.conjX, FlatSettingInst.youngLaws_actualPk FI⟩
  choose conjX hconj using hLaw
  have hνpos : ∀ n, 0 < nu D (n + M) := fun n =>
    UnforcedLeray.Short.PartIIIb.Concrete.retNu_pos D.Pl D.σ₀ (n + M)
  have hνlim : Tendsto (fun n => nu D (n + M)) atTop (𝓝 0) :=
    (UnforcedLeray.Short.PartIIIb.Concrete.retNu_tendsto (Pl := D.Pl) D.σ₀ hD.omega_ne).comp
      (tendsto_add_atTop_nat M)
  have hHyp : YoungHyp (fun n => nu D (n + M)) D.Pl.eigenvalue 2 1.1 := by
    unfold YoungHyp
    exact ⟨hνpos, hνlim, hD.gamma_pos, by norm_num, by norm_num⟩
  have hBd : YoungBounded (fun n => (S (n + M)).pk) (fun n => nu D (n + M)) 2 := by
    unfold YoungBounded
    exact ⟨Cb, fun n s hs j => hb (n + M) (by omega) s hs j⟩
  have hDelta : DeltaSmall (fun n => nu D (n + M)) (fun n => δ (n + M)) := by
    unfold DeltaSmall
    exact ⟨Cd, fun n => hd (n + M) (by omega)⟩
  have hR' := retainedBlocks_shift_frozen (fun n => (S n).pk) (nu D) D.Pl.eigenvalue D.Pl.kappa 2 1.1
    δ M hR
  have hBS : BlockSetup (fun n => (S (n + M)).pk) (fun n => nu D (n + M)) D.Pl.eigenvalue
      D.Pl.kappa 2 1.1 (fun n => δ (n + M)) :=
    blockSetup_of_laws (fun n => (S (n + M)).pk) conjX (fun n => nu D (n + M)) D.Pl.eigenvalue
      D.Pl.kappa 2 1.1 (fun n => δ (n + M)) hconj hHyp hBd hDelta hR'
  have hE := blocksFromRetained_holds (fun n => (S (n + M)).pk) (fun n => nu D (n + M))
    D.Pl.eigenvalue D.Pl.kappa 2 1.1 (fun n => δ (n + M)) hBS
  have hFP : YoungFrozenPair (fun n => (S (n + M)).pk) (fun n => nu D (n + M))
      D.Pl.eigenvalue D.Pl.kappa 2 1.1 :=
    youngFrozenPairC_holds (fun n => (S (n + M)).pk) conjX (fun n => nu D (n + M))
      D.Pl.eigenvalue D.Pl.kappa 2 1.1 hconj hHyp hBd hE
  exact youngFrozenPair_of_shift (fun n => (S n).pk) (nu D) D.Pl.eigenvalue D.Pl.kappa 2 1.1 M hFP

end G1

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif
