import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2_1

/-!


Source: `the November 2 reference manuscript` lines 2100-2105.
The proof uses Schwarz symmetry of the second derivative of the jointly smooth function
`G(r, x) = U r x` at `(r, x)`, with `r` in the open interval `Ioo s t`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb

/-- Directional derivative of a gradient field: derivative of `z ↦ ∇φ(z)·w` in direction `v`. -/
theorem pdTimeDeriv_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : E → ℝ) (p : E) (hφ : DifferentiableAt ℝ (fderiv ℝ φ) p) (v w : E) :
    fderiv ℝ (fun z => fderiv ℝ φ z w) p v = fderiv ℝ (fderiv ℝ φ) p v w := by
  have hA : HasFDerivAt (fun z => fderiv ℝ φ z w)
      ((ContinuousLinearMap.apply ℝ ℝ w).comp (fderiv ℝ (fderiv ℝ φ) p)) p :=
    (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp p hφ.hasFDerivAt
  rw [hA.fderiv]
  simp

theorem pdTimeDeriv : UnforcedLeray.Short.IIb.PdTimeDeriv := by
  intro s t U A hU hA j r hr x
  set G : ℝ × B0579.Plane → ℝ := fun z => U z.1 z.2 with hGdef
  have hCD : ∀ z : ℝ × B0579.Plane, z.1 ∈ Ioo s t →
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G z := by
    intro z hz
    apply ContDiffOn.contDiffAt hU
    exact prod_mem_nhds (Icc_mem_nhds hz.1 hz.2) univ_mem
  have hGp : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G (r, x) := hCD (r, x) hr
  have hdG : DifferentiableAt ℝ G (r, x) := hGp.differentiableAt (by simp)
  have hdFG : DifferentiableAt ℝ (fderiv ℝ G) (r, x) :=
    (hGp.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have hsymm : IsSymmSndFDerivAt ℝ G (r, x) := hGp.isSymmSndFDerivAt (by simp)
  -- Step 1: the spatial partial is a directional derivative of `G` in the `(0, dir j)` direction.
  have F1 : ∀ r' ∈ Ioo s t,
      B0579.pd j (U r') x = fderiv ℝ G (r', x) (0, B0579.dir j) := by
    intro r' hr'
    have hd : DifferentiableAt ℝ G (r', x) := (hCD (r', x) hr').differentiableAt (by simp)
    have hc : HasFDerivAt (fun y => G (r', y))
        ((fderiv ℝ G (r', x)).comp (ContinuousLinearMap.inr ℝ ℝ B0579.Plane)) x :=
      hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right r' x)
    have hUr : U r' = fun y => G (r', y) := rfl
    unfold B0579.pd
    rw [hUr, hc.fderiv]
    simp
  -- Step 2: the `r`-derivative of this directional derivative.
  have hdFGw : DifferentiableAt ℝ (fun z => fderiv ℝ G z (0, B0579.dir j)) (r, x) :=
    hdFG.clm_apply (differentiableAt_const _)
  have hL : HasDerivAt (fun r' : ℝ => ((r', x) : ℝ × B0579.Plane)) ((1, 0) : ℝ × B0579.Plane) r :=
    (hasDerivAt_id r).prodMk (hasDerivAt_const r x)
  have hD1 : HasDerivAt (fun r' : ℝ => fderiv ℝ G (r', x) (0, B0579.dir j))
      (fderiv ℝ (fun z => fderiv ℝ G z (0, B0579.dir j)) (r, x) (1, 0)) r :=
    HasFDerivAt.comp_hasDerivAt (f := fun r' : ℝ => ((r', x) : ℝ × B0579.Plane)) r
      hdFGw.hasFDerivAt hL
  -- Step 3: the value of the derivative equals `∂_j ∂_r`-term, by symmetry.
  have hsw : fderiv ℝ (fderiv ℝ G) (r, x) (0, B0579.dir j) (1, 0) =
      fderiv ℝ (fderiv ℝ G) (r, x) (1, 0) (0, B0579.dir j) := hsymm.eq _ _
  -- Step 4: the `j`-partial of `∂_r U` equals the same second-derivative expression.
  have hAr : A r = fun y => fderiv ℝ G (r, y) (1, 0) := by
    funext y
    have hdy : DifferentiableAt ℝ G (r, y) := (hCD (r, y) hr).differentiableAt (by simp)
    have h1 : HasDerivAt (fun r' => G (r', y)) (fderiv ℝ G (r, y) (1, 0)) r := by
      have hl : HasDerivAt (fun r' : ℝ => ((r', y) : ℝ × B0579.Plane)) ((1, 0) : ℝ × B0579.Plane) r :=
        (hasDerivAt_id r).prodMk (hasDerivAt_const r y)
      exact hdy.hasFDerivAt.comp_hasDerivAt r hl
    have h2 : HasDerivAt (fun r' => U r' y) (A r y) r := hA r hr y
    exact h2.unique h1
  have hd2 : DifferentiableAt ℝ (fun z => fderiv ℝ G z (1, 0)) (r, x) :=
    hdFG.clm_apply (differentiableAt_const _)
  have hc2 : HasFDerivAt (fun y => fderiv ℝ G (r, y) (1, 0))
      ((fderiv ℝ (fun z => fderiv ℝ G z (1, 0)) (r, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ B0579.Plane)) x :=
    hd2.hasFDerivAt.comp x (hasFDerivAt_prodMk_right r x)
  have hH : B0579.pd j (A r) x = fderiv ℝ (fderiv ℝ G) (r, x) (0, B0579.dir j) (1, 0) := by
    have hpd : B0579.pd j (A r) x = fderiv ℝ (fun y => fderiv ℝ G (r, y) (1, 0)) x (B0579.dir j) := by
      rw [hAr]
      rfl
    rw [hpd, hc2.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    exact pdTimeDeriv_clm G (r, x) hdFG (0, B0579.dir j) (1, 0)
  -- Step 5: assemble the derivative of `r' ↦ ∂_j U r' x`.
  rw [hH]
  have hEv : (fun r' => B0579.pd j (U r') x) =ᶠ[𝓝 r]
      (fun r' => fderiv ℝ G (r', x) (0, B0579.dir j)) :=
    Filter.eventually_of_mem (Ioo_mem_nhds hr.1 hr.2) (fun r' hr' => F1 r' hr')
  have hfinal : HasDerivAt (fun r' => fderiv ℝ G (r', x) (0, B0579.dir j))
      (fderiv ℝ (fderiv ℝ G) (r, x) (0, B0579.dir j) (1, 0)) r := by
    rw [hsw, ← pdTimeDeriv_clm G (r, x) hdFG (1, 0) (0, B0579.dir j)]
    exact hD1
  exact hfinal.congr_of_eventuallyEq hEv

end UnforcedLeray.Short.IIb
