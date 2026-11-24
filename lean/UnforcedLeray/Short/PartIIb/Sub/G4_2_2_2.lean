import UnforcedLeray.Short.PartIIb.Sub.G4_2_2_1

/-!
# PartII-b:G4/2/2/2 — `GreenRemDecay` from tail integrals

Source: the November 2 reference manuscript
lines 2349-2352.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

theorem greenRemDecay_of (hTail : GreenRemTail) (hTailG : GaussTail) (hMul : GaussMulPoly)
    (hLin : GaussLin) (hZ : PolyZpow) : GreenRemDecay := by
  intro lam q hq hG j
  have hqs := hq.smooth
  obtain ⟨hT1s, hT1g⟩ := hTailG q 3 hqs hG
  obtain ⟨hT2s, hT2g⟩ := hTailG q (-1) hqs hG
  set T1 : ℝ → ℂ := fun r => ∫ s in Ioi r, (s : ℂ) ^ (3 : ℤ) * q s with hT1
  set T2 : ℝ → ℂ := fun r => ∫ s in Ioi r, (s : ℂ) ^ (-1 : ℤ) * q s with hT2
  have hz1 := hZ (-2)
  have hz2 := hZ 2
  have hS1 : ContDiffOn ℝ ∞ (fun r => T1 r * (r : ℂ) ^ (-2 : ℤ)) (Ioi 0) := hT1s.mul hz1.1
  have hS2 : ContDiffOn ℝ ∞ (fun r => T2 r * (r : ℂ) ^ (2 : ℤ)) (Ioi 0) := hT2s.mul hz2.1
  have hA : ∀ i, GaussAt (fun r => T1 r * (r : ℂ) ^ (-2 : ℤ)) i := fun i =>
    hMul T1 _ (i + 1) hT1s hz1.1 (fun i _ => hT1g i) (fun i _ => hz1.2 i) i (by omega)
  have hB : ∀ i, GaussAt (fun r => T2 r * (r : ℂ) ^ (2 : ℤ)) i := fun i =>
    hMul T2 _ (i + 1) hT2s hz2.1 (fun i _ => hT2g i) (fun i _ => hz2.2 i) i (by omega)
  have hC := hLin (1 / 4) (-(1 / 4)) _ _ (j + 1) hS1 hS2 (fun i _ => hA i) (fun i _ => hB i) j
    (by omega)
  obtain ⟨C, κ, hκ, hb⟩ := hC
  refine ⟨C, κ, hκ, fun r hr => ?_⟩
  have heq : greenRem q =ᶠ[𝓝 r] fun s : ℝ => (1 / 4 : ℂ) * (T1 s * (s : ℂ) ^ (-2 : ℤ)) +
      (-(1 / 4 : ℂ)) * (T2 s * (s : ℂ) ^ (2 : ℤ)) := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < r by linarith)] with s hs
    rw [hTail q hq.memXG s hs]
    have e1 : (s : ℂ) ^ (-2 : ℤ) = ((s : ℂ) ^ 2)⁻¹ := by simp [zpow_neg]
    have e2 : (s : ℂ) ^ (2 : ℤ) = (s : ℂ) ^ 2 := by norm_cast
    have e3 : T1 s = ∫ t in Ioi s, (t : ℂ) ^ 3 * q t := by
      simp only [hT1]; norm_cast
    have e4 : T2 s = ∫ t in Ioi s, (t : ℂ)⁻¹ * q t := by
      simp only [hT2, zpow_neg_one]
    rw [e1, e2, e3, e4]
    ring
  rw [heq.iteratedDeriv_eq]
  exact hb r hr

end UnforcedLeray.Short.IIb
