import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.CurlRegularity
import UnforcedLeray.Units.B0238
import UnforcedLeray.Units.B0579

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.IIb.CCP

open UnforcedLeray UnforcedLeray.Short.PartI
open UnforcedLeray.Train (Vec toVec)

/-- Uniform bounds of the train velocity and of the gradient of its vorticity on
`[0,H] × (centered cell ∩ strip)`. -/
theorem train_strip_bounds {ν c : ℝ} (tr : B0140.TrainSol ν c) (H R : ℝ) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc 0 H, ∀ x : B0579.Plane, |x.1| ≤ c / 2 → |x.2| ≤ R →
      |tr.v r x 0| ≤ C ∧ |tr.v r x 1| ≤ C ∧
      |B0579.pd 0 (B0238.Ec tr r) x| ≤ C ∧ |B0579.pd 1 (B0238.Ec tr r) x| ≤ C := by
  set T : ℝ := H + 1 with hT
  have hT0 : 0 < T := by linarith
  set S : Set (ℝ × Cyl.Plane) := Icc 0 T ×ˢ (univ : Set Cyl.Plane) with hS
  have huniq : UniqueDiffOn ℝ S := UniqueDiffOn.prod (uniqueDiffOn_Icc hT0) uniqueDiffOn_univ
  have hsm : ContDiffOn ℝ ∞ (fun x : ℝ × Cyl.Plane => tr.v x.1 x.2) S :=
    tr.isTrain.smooth_v.mono (prod_mono Icc_subset_Ici_self (subset_refl _))
  have hF1 := crFc_contDiffOn hsm 1
  have hF0 := crFc_contDiffOn hsm 0
  set E' : ℝ × Cyl.Plane → ℝ := fun x => fderivWithin ℝ (crFc tr.v 1) S x crEQ -
      fderivWithin ℝ (crFc tr.v 0) S x crEE with hE'
  have hE'sm : ContDiffOn ℝ ∞ E' S := by
    have h1 : ContDiffOn ℝ ∞ (fderivWithin ℝ (crFc tr.v 1) S) S :=
      hF1.fderivWithin huniq (by simp)
    have h0 : ContDiffOn ℝ ∞ (fderivWithin ℝ (crFc tr.v 0) S) S :=
      hF0.fderivWithin huniq (by simp)
    exact (h1.clm_apply contDiffOn_const).sub (h0.clm_apply contDiffOn_const)
  have hcurl : ∀ r ∈ Icc (0 : ℝ) T, B0238.Ec tr r = fun z => E' (r, z) := by
    intro r hr
    funext z
    exact crCurl_within hsm hr
  have hpd : ∀ r ∈ Icc (0 : ℝ) T, ∀ (z : Cyl.Plane) (j : Fin 2),
      B0579.pd j (B0238.Ec tr r) z = fderivWithin ℝ E' S (r, z) (0, B0579.dir j) := by
    intro r hr z j
    have hmem : ((r, z) : ℝ × Cyl.Plane) ∈ S := ⟨hr, mem_univ _⟩
    have hd : HasFDerivWithinAt E' (fderivWithin ℝ E' S (r, z)) S (r, z) :=
      ((hE'sm.differentiableOn (by simp)) _ hmem).hasFDerivWithinAt
    have hι : HasFDerivAt (fun y : Cyl.Plane => ((r, y) : ℝ × Cyl.Plane))
        ((0 : Cyl.Plane →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Cyl.Plane)) z :=
      (hasFDerivAt_const r z).prodMk (hasFDerivAt_id z)
    have hcomp := hd.comp z (hι.hasFDerivWithinAt (s := Set.univ)) (fun y _ => ⟨hr, mem_univ _⟩)
    have hfd : HasFDerivAt (fun y : Cyl.Plane => E' (r, y))
        ((fderivWithin ℝ E' S (r, z)).comp
          ((0 : Cyl.Plane →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Cyl.Plane))) z :=
      hasFDerivWithinAt_univ.mp hcomp
    unfold B0579.pd
    rw [hcurl r hr, hfd.fderiv]
    simp
  have hcontG : ∀ j : Fin 2, ContinuousOn
      (fun y => fderivWithin ℝ E' S y (0, B0579.dir j)) S := fun j =>
    (hE'sm.continuousOn_fderivWithin huniq (by simp)).clm_apply continuousOn_const
  set Kset : Set (ℝ × Cyl.Plane) :=
    Icc 0 H ×ˢ (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R) with hK
  have hKc : IsCompact Kset :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hKS : Kset ⊆ S := fun y hy =>
    ⟨⟨hy.1.1, hy.1.2.trans (by linarith)⟩, mem_univ _⟩
  have hb : ∀ f : ℝ × Cyl.Plane → ℝ, ContinuousOn f S → ∃ C : ℝ, ∀ y ∈ Kset, |f y| ≤ C := by
    intro f hf
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hf.mono hKS)
    exact ⟨C, fun y hy => by simpa using hC y hy⟩
  obtain ⟨C1, h1⟩ := hb _ hF1.continuousOn
  obtain ⟨C0, h0⟩ := hb _ hF0.continuousOn
  obtain ⟨Cq, hq⟩ := hb _ (hcontG 0)
  obtain ⟨Ce, he⟩ := hb _ (hcontG 1)
  refine ⟨max (max C1 C0) (max (max Cq Ce) 0), le_max_of_le_right (le_max_right _ _),
    fun r hr x hx1 hx2 => ?_⟩
  have hrT : r ∈ Icc (0 : ℝ) T := ⟨hr.1, by linarith [hr.2]⟩
  have hy : ((r, x) : ℝ × Cyl.Plane) ∈ Kset :=
    ⟨hr, abs_le.mp hx1, abs_le.mp hx2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (h0 _ hy).trans (le_trans (le_max_right _ _) (le_max_left _ _))
  · exact (h1 _ hy).trans (le_trans (le_max_left _ _) (le_max_left _ _))
  · rw [hpd r hrT x 0]
    exact (hq _ hy).trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
      (le_max_right _ _))
  · rw [hpd r hrT x 1]
    exact (he _ hy).trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_max_right _ _))

end UnforcedLeray.Short.IIb.CCP
