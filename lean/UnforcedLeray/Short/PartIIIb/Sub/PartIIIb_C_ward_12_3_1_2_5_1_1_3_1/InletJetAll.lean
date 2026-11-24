import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.FarOrg
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletProfileJets.CutStreamJets
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7_4.RingStreamJetsDecay
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7_4.CutStreamSVanish
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletContDiff

/-!
# Part III-b, task `PartIII-b:C/ward/12/3/1/2/5/1/1/3/1/1/2` (`InletJetAll`)

All-order version of `IIb.inletJetDecay_of` (`Short/PartII-b/Sub/PartII-b_G4_3_7_4.lean`), with the
order `2` replaced by `j` and without the `ν`-bookkeeping. Source of record:
`the November 2 reference manuscript`, lines 2347-2369.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cons.C03.Concrete

theorem inletJetAll : InletJetAll := by
  intro lam q hq p hmode hc1 hR1 i j
  obtain ⟨C3, κ, N, hC3, hκ, h3'⟩ := UnforcedLeray.Short.IIb.cutStreamJets lam q hq (j + 1)
  obtain ⟨C4, hC4, h4'⟩ := UnforcedLeray.Short.IIb.ringStreamJetsDecay j
  have hH : 0 < p.H := p.H_pos
  have hc0 : 0 < p.c := by linarith
  obtain ⟨hcutsm, hcut⟩ := h3' p hmode hc1 hH i
  have hinv : 0 ≤ p.H⁻¹ := inv_nonneg.2 hH.le
  set M : ℝ := C3 * (1 + p.H⁻¹) ^ (j + 1) * p.c ^ N with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact mul_nonneg (mul_nonneg hC3.le (pow_nonneg (by linarith) _)) (pow_nonneg hc0.le _)
  have hring := h4' p.R (p.H / 2) p.c κ M (p.cutStream i) hR1 (half_pos hH) hc0 hκ hM0
    hcutsm
    (by
      intro x hx
      show ageCutoff p.H x.1 * p.frozenStream i x.2 = 0
      rw [ageCutoff_eq_zero hH hx.le, zero_mul])
    (fun x hx => UnforcedLeray.Short.IIb.cutStreamSVanish lam q hq p hmode hc1 hH i x hx)
    (fun l hl x => hcut l hl x)
  refine ⟨C4 * (1 + p.H / 2) * (1 + p.c / κ) * M, κ / (2 * p.c), div_pos hκ (by linarith), ?_, ?_⟩
  · exact UnforcedLeray.Short.IIb.inletCD_ringStreamProfile (R := p.R) (φ := p.cutStream i) hcutsm
  · intro l hl m
    have hbound := hring l hl m
    have he : -((κ / 2) * |m.2.2| / p.c) = -((κ / (2 * p.c)) * |m.2.2|) := by
      field_simp
    rw [he] at hbound
    exact hbound

end UnforcedLeray.Short.PartIIIb.Concrete
