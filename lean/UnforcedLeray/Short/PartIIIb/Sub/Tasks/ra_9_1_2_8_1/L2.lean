import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1_2_8_1

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `Dc` of `(0, φ)` is `(0, Dc φ)` for `φ` of class `C²` at `q` (source 5034-5039). -/
theorem dcToMer : DcToMerP := by
  unfold DcToMerP
  intro ν μ φ q hφ
  have hT : ∀ a : ℝ, toMer (0, a) = a • toMer (0, 1) := by
    intro a
    ext i
    fin_cases i <;> simp [toMer]
  have hfun : (fun p => toMer (0, φ p)) = fun p => φ p • toMer (0, 1) :=
    funext fun p => hT (φ p)
  rw [hfun]
  have hev : ∀ᶠ p in nhds q, DifferentiableAt ℝ φ p :=
    (hφ.eventually (by norm_num)).mono fun p hp => hp.differentiableAt (by norm_num)
  have hdiffq : DifferentiableAt ℝ φ q := hφ.differentiableAt (by norm_num)
  have hdQφ : DifferentiableAt ℝ (UnforcedLeray.Axi.dQ φ) q :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
      (differentiableAt_const _)
  have hdEφ : DifferentiableAt ℝ (UnforcedLeray.Axi.dEta φ) q :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
      (differentiableAt_const _)
  have hS : UnforcedLeray.Axi.dS (fun p => φ p • toMer (0, 1)) q
      = UnforcedLeray.Axi.dS φ q • toMer (0, 1) := by
    show fderiv ℝ (fun p => φ p • toMer (0, 1)) q (1, (0, 0))
      = fderiv ℝ φ q (1, (0, 0)) • toMer (0, 1)
    rw [fderiv_smul_const hdiffq]
    simp
  have hdQ : UnforcedLeray.Axi.dQ (fun p => φ p • toMer (0, 1))
      =ᶠ[nhds q] fun p => UnforcedLeray.Axi.dQ φ p • toMer (0, 1) := by
    filter_upwards [hev] with p hp
    show fderiv ℝ (fun p => φ p • toMer (0, 1)) p (0, (1, 0))
      = fderiv ℝ φ p (0, (1, 0)) • toMer (0, 1)
    rw [fderiv_smul_const hp]
    simp
  have hdE : UnforcedLeray.Axi.dEta (fun p => φ p • toMer (0, 1))
      =ᶠ[nhds q] fun p => UnforcedLeray.Axi.dEta φ p • toMer (0, 1) := by
    filter_upwards [hev] with p hp
    show fderiv ℝ (fun p => φ p • toMer (0, 1)) p (0, (0, 1))
      = fderiv ℝ φ p (0, (0, 1)) • toMer (0, 1)
    rw [fderiv_smul_const hp]
    simp
  have hQQ : UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dQ (fun p => φ p • toMer (0, 1))) q
      = UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dQ φ) q • toMer (0, 1) := by
    show fderiv ℝ (UnforcedLeray.Axi.dQ (fun p => φ p • toMer (0, 1))) q (0, (1, 0))
      = fderiv ℝ (UnforcedLeray.Axi.dQ φ) q (0, (1, 0)) • toMer (0, 1)
    rw [hdQ.fderiv_eq, fderiv_smul_const hdQφ]
    simp
  have hEE : UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta (fun p => φ p • toMer (0, 1))) q
      = UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta φ) q • toMer (0, 1) := by
    show fderiv ℝ (UnforcedLeray.Axi.dEta (fun p => φ p • toMer (0, 1))) q (0, (0, 1))
      = fderiv ℝ (UnforcedLeray.Axi.dEta φ) q (0, (0, 1)) • toMer (0, 1)
    rw [hdE.fderiv_eq, fderiv_smul_const hdEφ]
    simp
  rw [hT (DcR ν μ φ q)]
  unfold Dc lapQE DcR
  simp only [hS, hQQ, hEE]
  module

end UnforcedLeray.Short.PartIIIb.Concrete
