import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1_2_8_1

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `s`-derivative of `F` along the line `t ↦ (t, x)` is `dS F (s, x)` (source 4979). -/
theorem L4_hasDerivAt_line (F : Chart → ℝ) (s : ℝ) (x : ℝ × ℝ) (hF : DifferentiableAt ℝ F (s, x)) :
    HasDerivAt (fun t : ℝ => F (t, x)) (UnforcedLeray.Axi.dS F (s, x)) s := by
  have hl : HasDerivAt (fun t : ℝ => ((t, x) : Chart)) ((1 : ℝ), (0 : ℝ × ℝ)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  exact hF.hasFDerivAt.comp_hasDerivAt s hl

/-- `s ∂_s φ = w0 - η w02 - 2 w00` for `φ = (1-𝒦)ψ` (source 4979-4980, 5034-5039). -/
theorem thetaScalDS : ThetaScalDSP := by
  unfold ThetaScalDSP
  intro ψ q hq hp
  obtain ⟨s, x⟩ := q
  have hU : IsOpen ((Ioi (0:ℝ)) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hmem : (s, x) ∈ (Ioi (0:ℝ)) ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hq, mem_univ _⟩
  have h4 : ContDiffAt ℝ 4 ψ (s, x) := hp.contDiffAt (hU.mem_nhds hmem)
  have h3f : ContDiffAt ℝ 3 (fderiv ℝ ψ) (s, x) := h4.fderiv_right (by norm_num)
  have hψd : DifferentiableAt ℝ ψ (s, x) := h4.differentiableAt (by norm_num)
  have hdSd : DifferentiableAt ℝ (UnforcedLeray.Axi.dS ψ) (s, x) := by
    unfold UnforcedLeray.Axi.dS
    exact (h3f.differentiableAt (by norm_num)).clm_apply (differentiableAt_const _)
  have hdEd : DifferentiableAt ℝ (UnforcedLeray.Axi.dEta ψ) (s, x) := by
    unfold UnforcedLeray.Axi.dEta
    exact (h3f.differentiableAt (by norm_num)).clm_apply (differentiableAt_const _)
  have hfst : DifferentiableAt ℝ (fun p : Chart => p.1) (s, x) := differentiableAt_fst
  have hη : DifferentiableAt ℝ (fun p : Chart => p.2.2) (s, x) := by fun_prop
  have hθd : DifferentiableAt ℝ (thetaScal ψ) (s, x) := by
    unfold thetaScal Kc
    exact hψd.sub (((differentiableAt_const (2 : ℝ)).mul hfst).smul hdSd
      |>.add (hη.smul hdEd))
  have hA := L4_hasDerivAt_line ψ s x hψd
  have hB : HasDerivAt (fun t : ℝ => UnforcedLeray.Axi.dS ψ (t, x))
      (UnforcedLeray.Axi.dS (UnforcedLeray.Axi.dS ψ) (s, x)) s :=
    L4_hasDerivAt_line _ s x hdSd
  have hC : HasDerivAt (fun t : ℝ => UnforcedLeray.Axi.dEta ψ (t, x))
      (UnforcedLeray.Axi.dS (UnforcedLeray.Axi.dEta ψ) (s, x)) s :=
    L4_hasDerivAt_line _ s x hdEd
  have hT := L4_hasDerivAt_line (thetaScal ψ) s x hθd
  have hL : HasDerivAt (fun t : ℝ => thetaScal ψ (t, x))
      (UnforcedLeray.Axi.dS ψ (s, x) - ((2 * 1) * UnforcedLeray.Axi.dS ψ (s, x)
        + (2 * s) * UnforcedLeray.Axi.dS (UnforcedLeray.Axi.dS ψ) (s, x)
        + x.2 * UnforcedLeray.Axi.dS (UnforcedLeray.Axi.dEta ψ) (s, x))) s := by
    unfold thetaScal Kc
    exact hA.sub ((((hasDerivAt_id' s).const_mul 2).mul hB).add (hC.const_mul x.2))
  have hSd := hT.unique hL
  have hF2 : DifferentiableAt ℝ (fun p : Chart => p.1 * UnforcedLeray.Axi.dS ψ p) (s, x) :=
    hfst.mul hdSd
  have hM := L4_hasDerivAt_line _ s x hF2
  have hM' : HasDerivAt (fun t : ℝ => t * UnforcedLeray.Axi.dS ψ (t, x))
      ((1 : ℝ) * UnforcedLeray.Axi.dS ψ (s, x) + s * UnforcedLeray.Axi.dS (UnforcedLeray.Axi.dS ψ) (s, x)) s :=
    (hasDerivAt_id' s).mul hB
  have hMd := hM.unique hM'
  simp only [wordW, opW, smul_eq_mul]
  rw [hSd, hMd]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
