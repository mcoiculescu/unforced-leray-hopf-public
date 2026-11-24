import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1_2_8_1

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `Dc` only depends on the germ at `q` (source 5022-5023, 5034-5039). -/
theorem dcLocal : DcLocalP := by
  unfold DcLocalP
  intro ν μ F G q h
  have hF : fderiv ℝ F =ᶠ[nhds q] fderiv ℝ G := h.fderiv
  have hdQ : UnforcedLeray.Axi.dQ F =ᶠ[nhds q] UnforcedLeray.Axi.dQ G :=
    hF.mono fun p hp => by simp only [UnforcedLeray.Axi.dQ, hp]
  have hdE : UnforcedLeray.Axi.dEta F =ᶠ[nhds q] UnforcedLeray.Axi.dEta G :=
    hF.mono fun p hp => by simp only [UnforcedLeray.Axi.dEta, hp]
  have hval : F q = G q := h.eq_of_nhds
  have hS : UnforcedLeray.Axi.dS F q = UnforcedLeray.Axi.dS G q := by
    show fderiv ℝ F q (1, (0, 0)) = fderiv ℝ G q (1, (0, 0))
    rw [h.fderiv_eq]
  have hQQ : UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dQ F) q
      = UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dQ G) q := by
    show fderiv ℝ (UnforcedLeray.Axi.dQ F) q (0, (1, 0)) = fderiv ℝ (UnforcedLeray.Axi.dQ G) q (0, (1, 0))
    rw [hdQ.fderiv_eq]
  have hEE : UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta F) q
      = UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta G) q := by
    show fderiv ℝ (UnforcedLeray.Axi.dEta F) q (0, (0, 1)) = fderiv ℝ (UnforcedLeray.Axi.dEta G) q (0, (0, 1))
    rw [hdE.fderiv_eq]
  simp only [Dc, lapQE]
  rw [hS, hval, hQQ, hEE]

end UnforcedLeray.Short.PartIIIb.Concrete
