import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.Limit.CurlBound
import UnforcedLeray.Short.PartI.Sub.T04.APriori

/-!
# Part I, `PartI:T04/10/1/2/2/2`: vorticity jets are integrable on the cell

Source of record: `the November 2 reference manuscript`, lines 285-288.
For a class solution and `s ∈ [0,T]`, the curl of `v(s)` is smooth, its `k`-th derivative is
dominated by `C ‖D^{k+1} v(s)‖` (`curlJetBound_proof`), and `‖D^{k+1} v(s)‖²` is integrable on
the cell (`jet_l2`).

Statement: `cellVortJetIntegrable_proof : CellVortJetIntegrable`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- The curl of a smooth vector field is smooth: `curl u = cbCurlLam ∘ fderiv ℝ u`. -/
theorem cellVortJet_curl_contDiff {u : Plane → Vec} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (Cyl.curl u) := by
  have hdiff : Differentiable ℝ u := hu.differentiable (by simp)
  have hg : ContDiff ℝ ∞ (fderiv ℝ u) := (contDiff_infty_iff_fderiv.mp hu).2
  have hfun : Cyl.curl u = fun w => cbCurlLam (fderiv ℝ u w) := by
    funext w
    have h0 : HasDerivAt (fun q : ℝ => (q, w.2)) ((1 : ℝ), (0 : ℝ)) w.1 :=
      (hasDerivAt_id w.1).prodMk (hasDerivAt_const w.1 w.2)
    have h0' : HasDerivAt (fun η : ℝ => (w.1, η)) ((0 : ℝ), (1 : ℝ)) w.2 :=
      (hasDerivAt_const w.2 w.1).prodMk (hasDerivAt_id w.2)
    have h1 : HasDerivAt (fun q : ℝ => u (q, w.2)) (fderiv ℝ u (w.1, w.2) (1, 0)) w.1 :=
      (hdiff (w.1, w.2)).hasFDerivAt.comp_hasDerivAt w.1 h0
    have h1' : HasDerivAt (fun η : ℝ => u (w.1, η)) (fderiv ℝ u (w.1, w.2) (0, 1)) w.2 :=
      (hdiff (w.1, w.2)).hasFDerivAt.comp_hasDerivAt w.2 h0'
    have h2 : HasDerivAt (fun q : ℝ => u (q, w.2) 1)
        ((EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
          (fderiv ℝ u (w.1, w.2) (1, 0))) w.1 :=
      (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt
        w.1 h1
    have h2' : HasDerivAt (fun η : ℝ => u (w.1, η) 0)
        ((EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
          (fderiv ℝ u (w.1, w.2) (0, 1))) w.2 :=
      (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt
        w.2 h1'
    have e1 : UnforcedLeray.Cyl.partialQ (fun x => u x 1) w =
        fderiv ℝ u w (1, 0) 1 := h2.deriv
    have e2 : UnforcedLeray.Cyl.partialEta (fun x => u x 0) w =
        fderiv ℝ u w (0, 1) 0 := h2'.deriv
    unfold UnforcedLeray.Cyl.curl
    rw [e1, e2, cbCurlLam_apply]
  rw [hfun]
  exact cbCurlLam.contDiff.comp hg

/-- **Vorticity jets are square integrable on the cell** (lines 285-288): for a class solution,
`s ∈ [0,T]` and `k`, the function `z ↦ ‖D^k curl v(s) z‖²` is integrable on the cell. -/
theorem cellVortJetIntegrable_proof : CellVortJetIntegrable := by
  intro ν c T v p hν hc hcls s hs k
  obtain ⟨C, hC0, hCb⟩ := curlJetBound_proof k
  have hsm : ContDiff ℝ ∞ (v s) := hcls.classical.contDiff_slice hs
  obtain ⟨K, hK⟩ := hcls.jet_l2 (k + 1)
  have hint : IntegrableOn (fun z => ‖iteratedFDeriv ℝ (k + 1) (v s) z‖ ^ 2) (Cyl.cell c) :=
    (hK s hs).1
  have hcd : ContDiff ℝ ∞ (Cyl.curl (v s)) := cellVortJet_curl_contDiff hsm
  have hcont : Continuous (fun z => ‖iteratedFDeriv ℝ k (Cyl.curl (v s)) z‖ ^ 2) :=
    ((hcd.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm).pow 2
  refine Integrable.mono' (g := fun z => C ^ 2 * ‖iteratedFDeriv ℝ (k + 1) (v s) z‖ ^ 2)
    (hint.const_mul (C ^ 2)) hcont.aestronglyMeasurable ?_
  refine Eventually.of_forall fun z => ?_
  have hb : ‖iteratedFDeriv ℝ k (Cyl.curl (v s)) z‖ ≤ C * ‖iteratedFDeriv ℝ (k + 1) (v s) z‖ :=
    hCb (v s) hsm z
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  calc ‖iteratedFDeriv ℝ k (Cyl.curl (v s)) z‖ ^ 2
      ≤ (C * ‖iteratedFDeriv ℝ (k + 1) (v s) z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = C ^ 2 * ‖iteratedFDeriv ℝ (k + 1) (v s) z‖ ^ 2 := by ring

end UnforcedLeray.Short.PartI

end
