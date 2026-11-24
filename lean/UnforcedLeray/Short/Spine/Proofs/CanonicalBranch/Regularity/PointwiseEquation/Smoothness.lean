import UnforcedLeray.Short.Spine.Sub.SP_CAN4_5

/-!
# Spine: proof of `SmoothnessFacts` (leaf 5 of `Spine:SP-CAN/4/5`)

Source of record: `the November 2 reference manuscript`, line 1086 (the jointly
smooth representative `W` is smooth for positive `θ`). The proof is elementary calculus:

* slices `W θ` are `C^∞` on `(0, ∞)` by composing with the smooth map `t ↦ (θ, t)`;
* `r ↦ deriv (fun t => W t r) θ` is the continuous function `fderiv ℝ F (θ, r) (1, 0)`, where
  `F z = W z.1 z.2` is `C^∞` on the open set `(0, ∞) ×ˢ (0, ∞)`;
* `oscillatorD g` is built from `g`, `deriv g`, `deriv (deriv g)` and the continuous functions
  `r ↦ r`, `r ↦ r⁻¹` on `(0, ∞)`.

No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b

/-- **Leaf 5, elementary smoothness facts** (`SmoothnessFacts`, `Sub/SP_CAN4_5.lean`). -/
theorem smoothnessFacts_proof : SmoothnessFacts := by
  refine ⟨fun W hW => ⟨fun θ hθ => ?_, fun θ hθ => ?_⟩, fun g hg => ?_⟩
  · -- the slice `r ↦ W θ r` is `C^∞` on `(0, ∞)`
    have hmap : ContDiff ℝ ∞ (fun t : ℝ => ((θ, t) : ℝ × ℝ)) :=
      contDiff_const.prodMk contDiff_id
    have hcomp := hW.comp hmap.contDiffOn (fun t ht => Set.mk_mem_prod hθ ht)
    exact hcomp
  · -- the `θ`-derivative is the continuous directional derivative `fderiv ℝ F (θ, r) (1, 0)`
    have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := isOpen_Ioi.prod isOpen_Ioi
    have hdiffAt : ∀ x ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ),
        DifferentiableAt ℝ (fun z : ℝ × ℝ => W z.1 z.2) x :=
      fun x hx => ((hW x hx).contDiffAt (hopen.mem_nhds hx)).differentiableAt (by simp)
    have hfd : ContinuousOn (fderiv ℝ (fun z : ℝ × ℝ => W z.1 z.2))
        (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
      hW.continuousOn_fderiv_of_isOpen hopen (by simp)
    have hline : Continuous (fun r : ℝ => ((θ, r) : ℝ × ℝ)) :=
      continuous_const.prodMk continuous_id
    have hθ' : ContinuousOn (fun r : ℝ => fderiv ℝ (fun z : ℝ × ℝ => W z.1 z.2) (θ, r))
        (Ioi (0 : ℝ)) :=
      hfd.comp hline.continuousOn (fun r hr => Set.mk_mem_prod hθ hr)
    have hd : ContinuousOn
        (fun r : ℝ => fderiv ℝ (fun z : ℝ × ℝ => W z.1 z.2) (θ, r) ((1 : ℝ), (0 : ℝ)))
        (Ioi (0 : ℝ)) :=
      hθ'.clm_apply continuousOn_const
    refine hd.congr ?_
    intro r hr
    have hpt : (θ, r) ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := Set.mk_mem_prod hθ hr
    have hF : HasFDerivAt (fun z : ℝ × ℝ => W z.1 z.2)
        (fderiv ℝ (fun z : ℝ × ℝ => W z.1 z.2) (θ, r)) (θ, r) :=
      (hdiffAt (θ, r) hpt).hasFDerivAt
    have hline' : HasDerivAt (fun t : ℝ => ((t, r) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) θ :=
      HasDerivAt.prodMk (hasDerivAt_id' θ) (hasDerivAt_const _ _)
    exact (hF.comp_hasDerivAt θ hline').deriv
  · -- `oscillatorD g` is continuous on `(0, ∞)`
    have hg1 : ContDiffOn ℝ ∞ (deriv g) (Ioi 0) :=
      ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).1 hg).2
    have hg2 : ContDiffOn ℝ ∞ (deriv (deriv g)) (Ioi 0) :=
      ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).1 hg1).2
    have hcr : ContinuousOn (fun r : ℝ => (r : ℂ)) (Ioi 0) :=
      Complex.continuous_ofReal.continuousOn
    have hr0 : ∀ r ∈ Ioi (0 : ℝ), (r : ℂ) ≠ 0 := by
      intro r hr
      have hr' : (0 : ℝ) < r := Set.mem_Ioi.1 hr
      exact_mod_cast hr'.ne'
    have hsq0 : ∀ r ∈ Ioi (0 : ℝ), (r : ℂ) ^ 2 ≠ 0 := fun r hr => pow_ne_zero 2 (hr0 r hr)
    unfold oscillatorD
    exact ((((hg2.continuousOn.add (hg1.continuousOn.div hcr hr0)).sub
      ((continuousOn_const.mul hg.continuousOn).div (hcr.pow 2) hsq0)).add
      ((hcr.div_const 2).mul hg1.continuousOn)).add (continuousOn_const.mul hg.continuousOn))

end UnforcedLeray.Short.Spine
