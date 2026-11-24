import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2.NearOrg
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletProfileJets.CutStreamJets
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7_4.RingStreamJetsDecay
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7_4.CutStreamSVanish
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletContDiff

/-!
# `InletProfileJets3`: jets of order `≤ 3` of the inlet profile

Source `the November 2 reference manuscript` lines 2347-2369, 2545-2549.
Proof as `inletJetDecay_of` (`Short/PartII-b/Sub/PartII-b_G4_3_7_4.lean`) with `2` replaced by `3`:
`cutStreamJets` at `j = 4`, `ringStreamJetsDecay` at `j = 3`, `cutStreamSVanish`, `ageCutoff_eq_zero`
and `inletCD_ringStreamProfile`. The constants `M` and `κ` may depend on `p`, so no
`p.ageCut = Sig` hypothesis is needed; the smoothness and vanishing of the inlet profile are
those of `inletProfileSmoothVanish` with `ν₀ = 1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.Axi

theorem inletProfileJets3 : InletProfileJets3 := by
  intro lam q hq dm dp hdm
  obtain ⟨C3, κ0, N, hC3, hκ0, h3'⟩ := UnforcedLeray.Short.IIb.cutStreamJets lam q hq 4
  obtain ⟨C4, hC4, h4'⟩ := UnforcedLeray.Short.IIb.ringStreamJetsDecay 3
  refine ⟨1, one_pos, le_refl _, ?_⟩
  intro p d hreg hν hmode i
  have hνpos : 0 < p.ν := p.ν_pos
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  have hcpos : 0 < p.c := by linarith
  have hR1 : 1 ≤ p.R := by
    have hε : p.ε ≤ 1 := by
      rw [hreg.eps_eq]
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ d / p.ν := div_nonneg (by linarith [hreg.dm_pos, hreg.dm_le]) hνpos.le
      rw [neg_div]; linarith
    show 1 ≤ p.ε⁻¹
    exact one_le_inv₀ p.ε_pos |>.mpr hε
  have hH : 0 < p.H := p.H_pos
  have hHi : 0 ≤ p.H⁻¹ := inv_nonneg.2 hH.le
  obtain ⟨hcutsm, hcut⟩ := h3' p hmode hc1 hH i
  have hM0 : 0 ≤ C3 * (1 + p.H⁻¹) ^ 4 * p.c ^ N :=
    mul_nonneg (mul_nonneg hC3.le (pow_nonneg (by linarith) 4)) (pow_nonneg hcpos.le N)
  have hring := h4' p.R (p.H / 2) p.c κ0 (C3 * (1 + p.H⁻¹) ^ 4 * p.c ^ N) (p.cutStream i)
    hR1 (half_pos hH) hcpos hκ0 hM0
    hcutsm
    (by
      intro x hx
      unfold Params.cutStream
      simp [ageCutoff_eq_zero hH (show p.H / 2 ≤ x.1 from hx.le)])
    (fun x hx => UnforcedLeray.Short.IIb.cutStreamSVanish lam q hq p hmode hc1 hH i x hx)
    (fun l hl x => hcut l hl x)
  have hκpos : 0 < κ0 / (2 * p.c) := div_pos hκ0 (by linarith)
  refine ⟨C4 * (1 + p.H / 2) * (1 + p.c / κ0) * (C3 * (1 + p.H⁻¹) ^ 4 * p.c ^ N),
    κ0 / (2 * p.c), ?_, hκpos, ?_, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (mul_nonneg hC4.le (by linarith))
      (by have := div_nonneg hcpos.le hκ0.le; linarith)) hM0
  · unfold Params.inletProfile
    exact UnforcedLeray.Short.IIb.inletCD_ringStreamProfile hcutsm
  · intro x hx
    have hcut0 : p.cutStream i x = 0 := by
      unfold Params.cutStream
      simp [ageCutoff_eq_zero hH hx.le]
    have hev : ∀ᶠ y in 𝓝 x, p.H / 2 < y.1 :=
      (continuous_fst.tendsto x).eventually (lt_mem_nhds hx)
    have hfun : p.cutStream i =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [hev] with y hy
      unfold Params.cutStream
      simp [ageCutoff_eq_zero hH hy.le]
    have hfd : fderiv ℝ (p.cutStream i) x = 0 := by
      rw [hfun.fderiv_eq]
      simp
    have hdS : Axi.dS (p.cutStream i) x = 0 := by
      unfold Axi.dS
      rw [hfd]
      simp
    have hdQ : Axi.dQ (p.cutStream i) x = 0 := by
      unfold Axi.dQ
      rw [hfd]
      simp
    have hdE : Axi.dEta (p.cutStream i) x = 0 := by
      unfold Axi.dEta
      rw [hfd]
      simp
    simp [Params.inletProfile, Axi.ringStreamProfile, hdS, hdQ, hdE, hcut0]
  · intro l hl x
    have hmain := hring l (by omega) x
    rw [show -((κ0 / 2) * |x.2.2| / p.c) = -((κ0 / (2 * p.c)) * |x.2.2|) by ring] at hmain
    exact hmain

end UnforcedLeray.Short.PartIIIb.Concrete
