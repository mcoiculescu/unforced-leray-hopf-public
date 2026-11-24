import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_11_4
import UnforcedLeray.Short.PartIIIb.Concrete.HpJGradProof
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.PsiRingSmooth

/-!
# `PartIII-b:C/inst/11/4` leaf 1: `HpAContOn`

`h^p_A = J ∇ψ^p_A` (`hpIsJGrad_proof`), and `ψ^p_A` is jointly `C²` on `{s > 0}`
(`psiRingSmooth_proof`), so the meridional gradient of `ψ^p_A` is continuous there.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Slice in the meridional variable: the `x`-derivative of `y ↦ f(s,y)`. -/
theorem fderiv_slice_y_L4_1 (f : Chart → ℝ) (s : ℝ) (x v : ℝ × ℝ)
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
theorem diffAt_of_contDiffOn_L4_1 (f : Chart → ℝ) (hf : ContDiffOn ℝ 2 f (Ioi 0 ×ˢ univ))
    (s : ℝ) (hs : 0 < s) (x : ℝ × ℝ) : DifferentiableAt ℝ f (s, x) :=
  (hf.differentiableOn (by norm_num)).differentiableAt
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨Set.mem_Ioi.2 hs, Set.mem_univ _⟩)

/-- `HpAContOn`: the leaf for `h^p_A`, from `h^p_A = J ∇ψ^p_A` and joint `C²` of `ψ^p_A`. -/
theorem hpAContOn (as : ℝ) (χf : ℝ → ℝ) : HpAContOn as χf := by
  intro hχ ν hν A hA
  have hC : ContDiffOn ℝ 2 (psiRing ν χf A) (Ioi 0 ×ˢ univ) := psiRingSmooth_proof as χf hχ ν hν A hA
  have hUo : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hD : ContinuousOn (fun p : Chart => fderiv ℝ (psiRing ν χf A) p) (Ioi 0 ×ˢ univ) :=
    hC.continuousOn_fderiv_of_isOpen hUo (by norm_num)
  have hF : ∀ k : Fin 2, ContinuousOn (fun p : Chart => fderiv ℝ (psiRing ν χf A) p (0, ei k))
      (Ioi 0 ×ˢ univ) := fun k => hD.clm_apply continuousOn_const
  have hJ : Continuous Jrot := by unfold Jrot; fun_prop
  have hG : ContinuousOn (fun p : Chart => Jrot (fderiv ℝ (psiRing ν χf A) p (0, ei 0),
      fderiv ℝ (psiRing ν χf A) p (0, ei 1))) (Ioi 0 ×ˢ univ) :=
    hJ.comp_continuousOn ((hF 0).prodMk (hF 1))
  have hG' : ContinuousOn (fun p : Chart => hpA ν χf A p.1 p.2) (Ioi 0 ×ˢ univ) := by
    refine hG.congr ?_
    intro p hp
    dsimp only
    have hp1 : 0 < p.1 := Set.mem_Ioi.1 hp.1
    have hdf := diffAt_of_contDiffOn_L4_1 _ hC p.1 hp1 p.2
    have h0 : fderiv ℝ (psipA ν χf A p.1) p.2 (ei 0) =
        fderiv ℝ (psiRing ν χf A) (p.1, p.2) (0, ei 0) :=
      fderiv_slice_y_L4_1 (psiRing ν χf A) p.1 p.2 (ei 0) hdf
    have h1 : fderiv ℝ (psipA ν χf A p.1) p.2 (ei 1) =
        fderiv ℝ (psiRing ν χf A) (p.1, p.2) (0, ei 1) :=
      fderiv_slice_y_L4_1 (psiRing ν χf A) p.1 p.2 (ei 1) hdf
    rw [(hpIsJGrad_proof ν hν χf A).2 p.1 hp1 p.2]
    unfold mgrad
    rw [h0, h1]
  exact hG'.mono fun p hp => ⟨Set.mem_Ioi.2 hp, Set.mem_univ _⟩

end UnforcedLeray.Short.PartIIIb.Concrete
