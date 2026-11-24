import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1_2_8_1

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `(1-𝒦)ψ` is `C²` at `q` when `ψ` is `C⁴` on the open set `s > 0` (source 4979-4980, 5034-5039). -/
theorem thetaScalSmooth : ThetaScalSmoothP := by
  unfold ThetaScalSmoothP
  intro ψ q hq hp
  have hU : IsOpen ((Ioi (0:ℝ)) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hmem : q ∈ (Ioi (0:ℝ)) ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hq, mem_univ _⟩
  have h4 : ContDiffAt ℝ 4 ψ q := hp.contDiffAt (hU.mem_nhds hmem)
  have h2 : ContDiffAt ℝ 2 ψ q := h4.of_le (by norm_num)
  have h3f : ContDiffAt ℝ 3 (fderiv ℝ ψ) q := h4.fderiv_right (by norm_num)
  have hdS3 : ContDiffAt ℝ 3 (fun p => UnforcedLeray.Axi.dS ψ p) q := by
    unfold UnforcedLeray.Axi.dS
    exact h3f.clm_apply contDiffAt_const
  have hdE3 : ContDiffAt ℝ 3 (fun p => UnforcedLeray.Axi.dEta ψ p) q := by
    unfold UnforcedLeray.Axi.dEta
    exact h3f.clm_apply contDiffAt_const
  have hdS2 : ContDiffAt ℝ 2 (fun p => UnforcedLeray.Axi.dS ψ p) q := hdS3.of_le (by norm_num)
  have hdE2 : ContDiffAt ℝ 2 (fun p => UnforcedLeray.Axi.dEta ψ p) q := hdE3.of_le (by norm_num)
  have hs : ContDiffAt ℝ 2 (fun p : Chart => 2 * p.1) q := contDiffAt_const.mul contDiffAt_fst
  have hη : ContDiffAt ℝ 2 (fun p : Chart => p.2.2) q := by fun_prop
  unfold thetaScal Kc
  exact h2.sub ((hs.smul hdS2).add (hη.smul hdE2))

end UnforcedLeray.Short.PartIIIb.Concrete
