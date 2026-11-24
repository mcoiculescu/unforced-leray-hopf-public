import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_11_4
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.PsiRingSmooth

/-!
# `PartIII-b:C/inst/11/4` leaf 3: `PsipADxContOn`

On `{s > 0}`, `∂_η ψ^p_A(s,x) = fderiv ψ^p_A` at `(s,x)` in the direction `(0, e_1)`, and the
derivative of the jointly `C²` profile `psiRing` is continuous there (`psiRingSmooth_proof`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Slice in the meridional variable: the `x`-derivative of `y ↦ f(s,y)`. -/
theorem fderiv_slice_y_L4_3 (f : Chart → ℝ) (s : ℝ) (x v : ℝ × ℝ)
    (hf : DifferentiableAt ℝ f (s, x)) :
    fderiv ℝ (fun y => f (s, y)) x v = fderiv ℝ f (s, x) (0, v) := by
  have hg : HasFDerivAt (fun y : ℝ × ℝ => ((s, y) : Chart))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) x :=
    (hasFDerivAt_const s x).prodMk (hasFDerivAt_id x)
  have hc := hf.hasFDerivAt.comp x hg
  have he : (fun y => f (s, y)) = f ∘ (fun y : ℝ × ℝ => ((s, y) : Chart)) := rfl
  rw [he, hc.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]

/-- `ψ^p_A` is `C²` (hence differentiable) at `(s,x)` with `s > 0`. -/
theorem diffAt_of_contDiffOn_L4_3 (f : Chart → ℝ) (hf : ContDiffOn ℝ 2 f (Ioi 0 ×ˢ univ))
    (s : ℝ) (hs : 0 < s) (x : ℝ × ℝ) : DifferentiableAt ℝ f (s, x) :=
  (hf.differentiableOn (by norm_num)).differentiableAt
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨Set.mem_Ioi.2 hs, Set.mem_univ _⟩)

/-- `PsipADxContOn`: the `η`-derivative of `ψ^p_A` is a continuous function on `{s > 0}`. -/
theorem psipADxContOn (as : ℝ) (χf : ℝ → ℝ) : PsipADxContOn as χf := by
  intro hχ ν hν A hA
  have hC : ContDiffOn ℝ 2 (psiRing ν χf A) (Ioi 0 ×ˢ univ) :=
    psiRingSmooth_proof as χf hχ ν hν A hA
  have hUo : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hD : ContinuousOn (fun p : Chart => fderiv ℝ (psiRing ν χf A) p) (Ioi 0 ×ˢ univ) :=
    hC.continuousOn_fderiv_of_isOpen hUo (by norm_num)
  have hE : ContinuousOn (fun p : Chart => fderiv ℝ (psiRing ν χf A) p (0, ei 1))
      (Ioi 0 ×ˢ univ) := hD.clm_apply continuousOn_const
  refine ⟨fun p => fderiv ℝ (psiRing ν χf A) p (0, ei 1), ?_, ?_⟩
  · exact hE.mono fun p hp => ⟨Set.mem_Ioi.2 hp, Set.mem_univ _⟩
  · intro p hp
    exact fderiv_slice_y_L4_3 (psiRing ν χf A) p.1 p.2 (ei 1)
      (diffAt_of_contDiffOn_L4_3 _ hC p.1 hp p.2)

end UnforcedLeray.Short.PartIIIb.Concrete
