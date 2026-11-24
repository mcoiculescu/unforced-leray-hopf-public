import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_1_7_5

/-!
# `PartIII-a:T21/2/7/1/7/5/2`: continuity in age of `∂_j E_c(r)` at a fixed point

Proves `LocPdEcCont` (`Sub/PartIII-a_T21_2_7_1_7_5.lean`). Source: SP lines 270-288 (smooth train),
3052-3058.

Route. `E_c(r) = curl V(r)` and `V` is jointly smooth on `[0,∞) × ℝ²` (`smooth_v`). Writing each
spatial partial of `V_k(r, ·)` as the within-strip derivative of the joint map
(`fderiv_slice_apply`, the same slice identity as `hasFDerivAt_slice` in
`Sub/PartIII-a_T21_2_7_2_3.lean`, on `[0,∞)` instead of `[t,s)`) gives
`E_c(r, z) = F(r, z)` with `F` jointly smooth on the strip (`ecJoint_contDiffOn`). Then
`∂_j E_c(r)(x) = ∂_{dir j} F(r, ·)(x) = fderivWithin F (strip) (r,x) (0, dir j)`, which is continuous
in `(r, x)` on the strip, hence in `r`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace PdEc

/-- The strip `[0,∞) × ℝ²` of (age, position) pairs. -/
theorem strip_uniqueDiff : UniqueDiffOn ℝ (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
  (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ

/-- The slice derivative in the spatial variables of a jointly smooth function on the strip. -/
theorem hasFDerivAt_slice_Ici {f : ℝ × (ℝ × ℝ) → ℝ}
    (hj : ContDiffOn ℝ ∞ f (Ici (0 : ℝ) ×ˢ univ)) {r : ℝ} (hr : 0 ≤ r) (x : ℝ × ℝ) :
    HasFDerivAt (fun z : ℝ × ℝ => f (r, z))
      ((fderivWithin ℝ f (Ici (0 : ℝ) ×ˢ univ) (r, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) x := by
  have hmem : ((r, x) : ℝ × (ℝ × ℝ)) ∈ Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
    ⟨hr, mem_univ _⟩
  have h1 : HasFDerivWithinAt f (fderivWithin ℝ f (Ici (0 : ℝ) ×ˢ univ) (r, x))
      (Ici (0 : ℝ) ×ˢ univ) (r, x) :=
    ((hj _ hmem).differentiableWithinAt (by simp)).hasFDerivWithinAt
  have hι : HasFDerivAt (fun y : ℝ × ℝ => ((r, y) : ℝ × (ℝ × ℝ)))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) x :=
    (hasFDerivAt_const r x).prodMk (hasFDerivAt_id x)
  have hmaps : MapsTo (fun y : ℝ × ℝ => ((r, y) : ℝ × (ℝ × ℝ))) univ
      (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := fun y _ => ⟨hr, mem_univ y⟩
  have h2 := h1.comp x hι.hasFDerivWithinAt hmaps
  rw [hasFDerivWithinAt_univ] at h2
  exact h2

/-- Spatial derivative of a slice, as the within-strip derivative applied to `(0, e)`. -/
theorem fderiv_slice_apply {f : ℝ × (ℝ × ℝ) → ℝ}
    (hj : ContDiffOn ℝ ∞ f (Ici (0 : ℝ) ×ˢ univ)) {r : ℝ} (hr : 0 ≤ r) (x e : ℝ × ℝ) :
    fderiv ℝ (fun z : ℝ × ℝ => f (r, z)) x e =
      fderivWithin ℝ f (Ici (0 : ℝ) ×ˢ univ) (r, x) ((0 : ℝ), e) := by
  rw [(hasFDerivAt_slice_Ici hj hr x).fderiv]
  simp

/-- The `k`-th component of the train velocity as a function of (age, position). -/
def wComp {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (k : Fin 2) :
    ℝ × (ℝ × ℝ) → ℝ :=
  fun p => tr.v p.1 p.2 k

theorem wComp_contDiffOn {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (k : Fin 2) :
    ContDiffOn ℝ ∞ (wComp tr k) (Ici (0 : ℝ) ×ˢ univ) :=
  (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp_contDiffOn tr.isTrain.smooth_v

/-- The vorticity `curl V` in Fréchet form, as a jointly defined function on the strip. -/
def ecJoint {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) : ℝ × (ℝ × ℝ) → ℝ :=
  fun p => fderivWithin ℝ (wComp tr 1) (Ici (0 : ℝ) ×ˢ univ) p ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) -
    fderivWithin ℝ (wComp tr 0) (Ici (0 : ℝ) ×ˢ univ) p ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))

theorem ecJoint_contDiffOn {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) :
    ContDiffOn ℝ ∞ (ecJoint tr) (Ici (0 : ℝ) ×ˢ univ) := by
  have d1 : ContDiffOn ℝ ∞ (fderivWithin ℝ (wComp tr 1) (Ici (0 : ℝ) ×ˢ univ))
      (Ici (0 : ℝ) ×ˢ univ) :=
    (wComp_contDiffOn tr 1).fderivWithin strip_uniqueDiff (by simp)
  have d0 : ContDiffOn ℝ ∞ (fderivWithin ℝ (wComp tr 0) (Ici (0 : ℝ) ×ˢ univ))
      (Ici (0 : ℝ) ×ˢ univ) :=
    (wComp_contDiffOn tr 0).fderivWithin strip_uniqueDiff (by simp)
  have h1 := d1.clm_apply (contDiffOn_const (c := ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))))
  have h0 := d0.clm_apply (contDiffOn_const (c := ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))))
  exact h1.sub h0

theorem Ec_eq_ecJoint {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r) :
    UnforcedLeray.B0238.Ec tr r = fun z => ecJoint tr (r, z) := by
  funext z
  have hv : ContDiff ℝ 1 (tr.v r) :=
    (UnforcedLeray.B0238.contDiff_Vc tr hr).of_le (by exact_mod_cast le_top)
  have e1 : fderiv ℝ (fun w => tr.v r w 1) z ((1 : ℝ), (0 : ℝ)) =
      fderivWithin ℝ (wComp tr 1) (Ici (0 : ℝ) ×ˢ univ) (r, z) ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) :=
    fderiv_slice_apply (wComp_contDiffOn tr 1) hr z _
  have e0 : fderiv ℝ (fun w => tr.v r w 0) z ((0 : ℝ), (1 : ℝ)) =
      fderivWithin ℝ (wComp tr 0) (Ici (0 : ℝ) ×ˢ univ) (r, z) ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) :=
    fderiv_slice_apply (wComp_contDiffOn tr 0) hr z _
  show UnforcedLeray.Cyl.curl (tr.v r) z = ecJoint tr (r, z)
  rw [UnforcedLeray.B0238.curl_eq_fderiv hv z, e1, e0]
  rfl

/-- The continuity in age of `∂_j E_c` at a fixed point. -/
theorem pdEc_continuousOn {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (j : Fin 2)
    (x : ℝ × ℝ) :
    ContinuousOn (fun r => B0579.pd j (UnforcedLeray.B0238.Ec tr r) x) (Ici 0) := by
  have hC : ContinuousOn (fun p : ℝ × (ℝ × ℝ) =>
      fderivWithin ℝ (ecJoint tr) (Ici (0 : ℝ) ×ˢ univ) p ((0 : ℝ), B0579.dir j))
      (Ici (0 : ℝ) ×ˢ univ) :=
    ((ecJoint_contDiffOn tr).fderivWithin strip_uniqueDiff (m := ∞) (by simp)).continuousOn.clm_apply
      continuousOn_const
  have hf : ContinuousOn (fun r : ℝ => ((r, x) : ℝ × (ℝ × ℝ))) (Ici (0 : ℝ)) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hg : ContinuousOn (fun r : ℝ => fderivWithin ℝ (ecJoint tr) (Ici (0 : ℝ) ×ˢ univ)
      (r, x) ((0 : ℝ), B0579.dir j)) (Ici (0 : ℝ)) :=
    hC.comp hf (fun r hr => ⟨hr, mem_univ x⟩)
  refine hg.congr (fun r hr => ?_)
  unfold B0579.pd
  rw [Ec_eq_ecJoint tr hr]
  exact fderiv_slice_apply (ecJoint_contDiffOn tr) hr x (B0579.dir j)

end PdEc

/-- **(S2) Time continuity of the vorticity gradient, pointwise in space** (see `LocPdEcCont`). -/
theorem locPdEcCont : LocPdEcCont := by
  intro ν c tr j x
  exact PdEc.pdEc_continuousOn tr j x

end UnforcedLeray.Short.IIIa
