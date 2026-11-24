import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_11_4
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.PsiRingSmooth

/-!
# `PartIII-b:C/inst/11/4` leaf 4: `PsipADsContOn`

On `{s > 0}`, `∂_s ψ^p_A(s,x) = fderiv ψ^p_A` at `(s,x)` in the direction `(1, 0)`, which is
continuous there because the profile `psiRing` is jointly `C²` on `{s > 0}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Slice in the radial-time variable: the `s`-derivative of `s' ↦ f(s',x)`. -/
theorem deriv_slice_s_L4_4 (f : Chart → ℝ) (s : ℝ) (x : ℝ × ℝ)
    (hf : DifferentiableAt ℝ f (s, x)) :
    deriv (fun s' => f (s', x)) s = fderiv ℝ f (s, x) (1, 0) := by
  have hg : HasDerivAt (fun s' : ℝ => ((s', x) : Chart)) ((1 : ℝ), (0 : ℝ × ℝ)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  have hc := HasFDerivAt.comp_hasDerivAt (x := s) hf.hasFDerivAt hg
  exact hc.deriv

/-- `ψ^p_A` is `C²` (hence differentiable) at `(s,x)` with `s > 0`. -/
theorem diffAt_of_contDiffOn_L4_4 (f : Chart → ℝ) (hf : ContDiffOn ℝ 2 f (Ioi 0 ×ˢ univ))
    (s : ℝ) (hs : 0 < s) (x : ℝ × ℝ) : DifferentiableAt ℝ f (s, x) :=
  (hf.differentiableOn (by norm_num)).differentiableAt
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨Set.mem_Ioi.2 hs, Set.mem_univ _⟩)

/-- `PsipADsContOn`: the `s`-derivative of `ψ^p_A` is a continuous function on `{s > 0}`. -/
theorem psipADsContOn (as : ℝ) (χf : ℝ → ℝ) : PsipADsContOn as χf := by
  intro hχ ν hν A hA
  have hC : ContDiffOn ℝ 2 (psiRing ν χf A) (Ioi 0 ×ˢ univ) :=
    psiRingSmooth_proof as χf hχ ν hν A hA
  have hUo : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hD : ContinuousOn (fun p : Chart => fderiv ℝ (psiRing ν χf A) p) (Ioi 0 ×ˢ univ) :=
    hC.continuousOn_fderiv_of_isOpen hUo (by norm_num)
  have hE : ContinuousOn (fun p : Chart => fderiv ℝ (psiRing ν χf A) p (1, 0))
      (Ioi 0 ×ˢ univ) := hD.clm_apply continuousOn_const
  refine ⟨fun p => fderiv ℝ (psiRing ν χf A) p (1, 0), ?_, ?_⟩
  · exact hE.mono fun p hp => ⟨Set.mem_Ioi.2 hp, Set.mem_univ _⟩
  · intro p hp
    exact deriv_slice_s_L4_4 (psiRing ν χf A) p.1 p.2
      (diffAt_of_contDiffOn_L4_4 _ hC p.1 hp p.2)

end UnforcedLeray.Short.PartIIIb.Concrete
