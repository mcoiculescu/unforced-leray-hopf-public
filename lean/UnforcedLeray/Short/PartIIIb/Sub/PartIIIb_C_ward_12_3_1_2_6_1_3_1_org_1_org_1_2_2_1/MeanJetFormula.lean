import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_2_2_1
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.HmeanDerivS
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.PressureMeanIdentity

/-!
# `MeanJetFormula` (SP 509-511: `S = \bar ψ`, differentiation under the horizontal mean)

Source: `the November 2 reference manuscript`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Set Filter Topology MeasureTheory
open scoped ContDiff
open UnforcedLeray.Cyl (Plane)

/-- The `b`-th Fréchet derivative on `(0,1)^b` is the `b`-th `η`-derivative on the line. -/
theorem mjf_line (G : Plane → ℝ) (hG : ContDiff ℝ ∞ G) (b : ℕ) (q η : ℝ) :
    (iteratedFDeriv ℝ b G (q, η)) (fun _ => ((0 : ℝ), (1 : ℝ))) =
      iteratedDeriv b (fun e => G (q, e)) η := by
  let L : ℝ →L[ℝ] Plane := (0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ)
  have hH : ContDiff ℝ ∞ (fun w : Plane => G (w + (q, 0))) :=
    hG.comp (contDiff_id.add contDiff_const)
  have e1 : (fun e : ℝ => G (q, e)) = (fun w : Plane => G (w + (q, 0))) ∘ L := by
    funext e; simp [L]
  rw [e1, iteratedDeriv_eq_iteratedFDeriv,
    L.iteratedFDeriv_comp_right hH η (by exact_mod_cast le_top)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_comp_add_right]
  simp [L]

/-- `η`-derivatives of the horizontal mean. -/
theorem mjf_iter_eta (c : ℝ) : ∀ (b : ℕ) (G : Plane → ℝ), ContDiff ℝ ∞ G → ∀ η : ℝ,
    iteratedDeriv b (fun e => Short.PartI.hmean c G e) η =
      Short.PartI.hmean c (fun z => iteratedDeriv b (fun e => G (z.1, e)) z.2) η := by
  intro b
  induction b with
  | zero => intro G _ η; simp
  | succ b ih =>
    intro G hG η
    have hd : deriv (fun e => Short.PartI.hmean c G e) =
        fun e => Short.PartI.hmean c (fun z => Cyl.partialEta G z) e :=
      funext fun e => (Short.PartI.pmi_hasDerivAt_hmean_eta hG e).deriv
    have hfun : (fun z : Plane => iteratedDeriv b (fun e => Cyl.partialEta G (z.1, e)) z.2) =
        fun z => iteratedDeriv (b + 1) (fun e => G (z.1, e)) z.2 := by
      funext z; rw [iteratedDeriv_succ']; rfl
    rw [iteratedDeriv_succ', hd, ih _ (Short.PartI.pmi_partialEta_contDiff hG), hfun]

/-- joint smoothness of the age derivatives. -/
theorem mjf_age_smooth : ∀ (k : ℕ) (f : ℝ → Plane → ℝ),
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => f x.1 x.2) (Ioi 0 ×ˢ univ) →
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => iteratedDeriv k (fun r => f r x.2) x.1)
      (Ioi 0 ×ˢ univ) := by
  intro k
  induction k with
  | zero => intro f hf; simpa using hf
  | succ k ih =>
    intro f hf
    have hg := ih f hf
    have hopen : IsOpen ((Ioi (0 : ℝ)) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
    have hfd := (hg.fderiv_of_isOpen (m := ∞) hopen (by simp)).clm_apply
      (contDiffOn_const (c := ((1 : ℝ), (0 : Plane))))
    refine hfd.congr ?_
    intro x hx
    obtain ⟨hs, -⟩ := hx
    have hdiff : DifferentiableAt ℝ
        (fun x : ℝ × Plane => iteratedDeriv k (fun r => f r x.2) x.1) x :=
      (hg.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds ⟨hs, mem_univ _⟩)
    have h1 : HasDerivAt (fun r : ℝ => (r, x.2)) ((1 : ℝ), (0 : Plane)) x.1 :=
      (hasDerivAt_id x.1).prodMk (hasDerivAt_const _ _)
    have h2 := hdiff.hasFDerivAt.comp_hasDerivAt x.1 (by simpa using h1)
    rw [iteratedDeriv_succ]
    exact h2.deriv

/-- the age derivatives commute with the horizontal mean. -/
theorem mjf_age_mean (c : ℝ) (hc : 0 < c) : ∀ (k : ℕ) (f : ℝ → Plane → ℝ),
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => f x.1 x.2) (Ioi 0 ×ˢ univ) →
    ∀ s : ℝ, 0 < s → ∀ η : ℝ,
      iteratedDeriv k (fun r => Short.PartI.hmean c (f r) η) s =
        Short.PartI.hmean c (fun z => iteratedDeriv k (fun r => f r z) s) η := by
  intro k
  induction k with
  | zero => intro f _ s _ η; simp
  | succ k ih =>
    intro f hf s hs η
    have hev : iteratedDeriv k (fun r => Short.PartI.hmean c (f r) η) =ᶠ[𝓝 s]
        fun r => Short.PartI.hmean c (fun z => iteratedDeriv k (fun r' => f r' z) r) η := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using ih f hf r hr η
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have := Short.PartI.hmeanDerivS c hc (fun r z => iteratedDeriv k (fun r' => f r' z) r)
      (mjf_age_smooth k f hf) s hs η
    rw [this]
    congr 2
    funext z
    rw [iteratedDeriv_succ]

theorem meanJetFormula : MeanJetFormula := by
  intro ν c hν hc tr htr b ℓ s hs η
  have hψ := Short.PartI.trainStreamSmooth ν c hν hc tr htr
  have hG : ContDiff ℝ ∞ (fun z : Plane => iteratedDeriv ℓ (fun r => tr.ψ r z) s) := by
    have := (mjf_age_smooth ℓ tr.ψ hψ).comp
      ((contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ fun z : Plane => (s, z)).contDiffOn
        (s := univ)) (fun z _ => ⟨hs, mem_univ _⟩)
    exact contDiffOn_univ.1 this
  have h1 : (fun e => iteratedDeriv ℓ (fun r => Short.PartI.meanStream tr r e) s) =
      fun e => Short.PartI.hmean c (fun z => iteratedDeriv ℓ (fun r => tr.ψ r z) s) e :=
    funext fun e => mjf_age_mean c hc ℓ tr.ψ hψ s hs e
  rw [h1, mjf_iter_eta c b _ hG η]
  unfold Short.PartI.hmean
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun q _ => ?_
  simp only
  rw [← mjf_line _ hG b q η]
  rfl

end UnforcedLeray.Short.PartIIIb.Concrete
