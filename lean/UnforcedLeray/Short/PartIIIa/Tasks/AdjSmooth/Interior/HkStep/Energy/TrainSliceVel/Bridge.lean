import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Defs

/-!
# Slices of a space-time field on `[0, ∞) × ℝ²` (bridge for `TrainSliceVel`, `TrainGradBdd`)

Source of record: `the November 2 reference manuscript` (SP) lines 270-288,
2866-2870 (slices of the train velocity), 3052-3058 (`TrainGradBdd`).

The bridge is an exact identity (no Faa di Bruno loss): the slice `x ↦ F (r, x)` is `F` composed
with the affine map `z ↦ (r, 0) + z` restricted to the inclusion `x ↦ (0, x)`, so its `i`-th
derivative is the `i`-th within derivative of `F` on `[0, ∞) × ℝ²` at `(r, x)` composed with
`inr` in every slot.  The boundary age `r = 0` is handled by `UniqueDiffOn` of the shifted set.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Pointwise

namespace UnforcedLeray.Short.IIIa

/-- **Exact slice identity (bridge).** For a field `F` smooth on `[0, ∞) × ℝ²` and `r ≥ 0`, the
`i`-th derivative of the slice `x ↦ F (r, x)` is bounded by the within derivative of `F` at `(r, x)`. -/
theorem slice_iteratedFDeriv_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ × (ℝ × ℝ) → E) (hF : ContDiffOn ℝ ∞ F (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
    {r : ℝ} (hr : 0 ≤ r) (i : ℕ) (x : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ i (fun y : ℝ × ℝ => F (r, y)) x‖ ≤
      ‖iteratedFDerivWithin ℝ i F (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (r, x)‖ := by
  have hs0U : UniqueDiffOn ℝ (Ici (-r) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (uniqueDiffOn_Ici (-r)).prod uniqueDiffOn_univ
  have hmaps : MapsTo (fun z : ℝ × (ℝ × ℝ) => ((r, (0 : ℝ × ℝ)) : ℝ × (ℝ × ℝ)) + z)
      (Ici (-r) ×ˢ (univ : Set (ℝ × ℝ))) (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
    intro z hz
    have h1 : -r ≤ z.1 := hz.1
    exact ⟨show (0:ℝ) ≤ r + z.1 by linarith, trivial⟩
  have hHr : ContDiffOn ℝ ∞
      (fun z : ℝ × (ℝ × ℝ) => F (((r, (0 : ℝ × ℝ)) : ℝ × (ℝ × ℝ)) + z))
      (Ici (-r) ×ˢ (univ : Set (ℝ × ℝ))) :=
    hF.comp (contDiff_const.add contDiff_id).contDiffOn hmaps
  have hpre : (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) ⁻¹' (Ici (-r) ×ˢ (univ : Set (ℝ × ℝ))) =
      (univ : Set (ℝ × ℝ)) := by
    ext y
    simp only [mem_preimage, mem_prod, mem_Ici, mem_univ, and_true, mem_univ, iff_true,
      ContinuousLinearMap.inr_apply, Prod.fst_zero]
    linarith
  have hset : ((r, (0 : ℝ × ℝ)) : ℝ × (ℝ × ℝ)) +ᵥ (Ici (-r) ×ˢ (univ : Set (ℝ × ℝ))) =
      Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := by
    ext ⟨p, q⟩
    constructor
    · intro h
      obtain ⟨z, hz, hzeq⟩ := Set.mem_vadd_set.1 h
      have h1 : -r ≤ z.1 := hz.1
      have e1 : r + z.1 = p := by
        have := congrArg Prod.fst hzeq
        simpa [vadd_eq_add] using this
      exact ⟨show (0:ℝ) ≤ p by linarith, trivial⟩
    · intro h
      have hp : (0:ℝ) ≤ p := h.1
      refine Set.mem_vadd_set.2 ⟨(p - r, q), ⟨show -r ≤ p - r by linarith, trivial⟩, ?_⟩
      rw [vadd_eq_add]
      ext <;> simp
  have hfun : (fun y : ℝ × ℝ => F (r, y)) =
      (fun z : ℝ × (ℝ × ℝ) => F (((r, (0 : ℝ × ℝ)) : ℝ × (ℝ × ℝ)) + z)) ∘
        (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) := by
    funext y
    simp
  have hx : ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) x ∈ Ici (-r) ×ˢ (univ : Set (ℝ × ℝ)) := by
    simp only [ContinuousLinearMap.inr_apply, mem_prod, mem_Ici, mem_univ, and_true, Prod.fst_zero]
    linarith
  have hkey := ContinuousLinearMap.iteratedFDerivWithin_comp_right
    (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) hHr hs0U
    (by rw [hpre]; exact uniqueDiffOn_univ) hx (i := i) (by simp)
  rw [hpre] at hkey
  have hcomp := iteratedFDerivWithin_comp_add_left (𝕜 := ℝ) (f := F) (s := Ici (-r) ×ˢ (univ : Set (ℝ × ℝ)))
    i ((r, (0 : ℝ × ℝ)) : ℝ × (ℝ × ℝ)) (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) x)
  rw [hset] at hcomp
  have hpt : ((r, (0 : ℝ × ℝ)) : ℝ × (ℝ × ℝ)) + ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) x = (r, x) := by
    simp
  rw [hpt] at hcomp
  have hEq : iteratedFDeriv ℝ i (fun y : ℝ × ℝ => F (r, y)) x =
      (iteratedFDerivWithin ℝ i F (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (r, x)).compContinuousLinearMap
        (fun _ : Fin i => ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) := by
    rw [← iteratedFDerivWithin_univ, hfun, hkey, ← hcomp]
  rw [hEq]
  have hnorm := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDerivWithin ℝ i F (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (r, x))
    (fun _ : Fin i => ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))
  simpa [ContinuousLinearMap.norm_inr] using hnorm

/-- The slice of a field smooth on `[0, ∞) × ℝ²` at `r ≥ 0` is smooth. -/
theorem slice_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ × (ℝ × ℝ) → E) (hF : ContDiffOn ℝ ∞ F (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
    {r : ℝ} (hr : 0 ≤ r) : ContDiff ℝ ∞ (fun y : ℝ × ℝ => F (r, y)) := by
  have h : ContDiffOn ℝ ∞ (fun y : ℝ × ℝ => F (r, y)) univ :=
    hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun y _ => (⟨show (0 : ℝ) ≤ r from hr, trivial⟩ : (r, y) ∈ Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
  exact contDiffOn_univ.1 h

theorem halfST_uniqueDiffOn : UniqueDiffOn ℝ (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
  (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ

/-! ## The curl of a slice as within derivatives of the space-time field -/

/-- `∂_q` of a slice is the within derivative of the space-time field in the direction `(0, (1,0))`. -/
theorem partialQ_eq_fderivWithin_half (G : ℝ × (ℝ × ℝ) → ℝ) {t : ℝ} (ht : 0 ≤ t) (z : ℝ × ℝ)
    (hG : DifferentiableWithinAt ℝ G (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (t, z)) :
    UnforcedLeray.Cyl.partialQ (fun w : ℝ × ℝ => G (t, w)) z =
      fderivWithin ℝ G (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (t, z) (0, (1, 0)) := by
  have hγ : HasDerivAt (fun q : ℝ => ((t, (q, z.2)) : ℝ × (ℝ × ℝ)))
      ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) z.1 :=
    HasDerivAt.prodMk (hasDerivAt_const _ _)
      (HasDerivAt.prodMk (hasDerivAt_id' _) (hasDerivAt_const _ _))
  have hmaps : MapsTo (fun q : ℝ => ((t, (q, z.2)) : ℝ × (ℝ × ℝ))) univ
      (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    fun q _ => ⟨show (0 : ℝ) ≤ t from ht, trivial⟩
  have hc := HasFDerivWithinAt.comp_hasDerivWithinAt (x := z.1)
    (f := fun q : ℝ => ((t, (q, z.2)) : ℝ × (ℝ × ℝ))) (l := G)
    (l' := fderivWithin ℝ G (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (t, z))
    hG.hasFDerivWithinAt hγ.hasDerivWithinAt hmaps
  exact (hasDerivWithinAt_univ.1 hc).deriv

/-- `∂_η` of a slice is the within derivative of the space-time field in the direction `(0, (0,1))`. -/
theorem partialEta_eq_fderivWithin_half (G : ℝ × (ℝ × ℝ) → ℝ) {t : ℝ} (ht : 0 ≤ t) (z : ℝ × ℝ)
    (hG : DifferentiableWithinAt ℝ G (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (t, z)) :
    UnforcedLeray.Cyl.partialEta (fun w : ℝ × ℝ => G (t, w)) z =
      fderivWithin ℝ G (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (t, z) (0, (0, 1)) := by
  have hγ : HasDerivAt (fun η : ℝ => ((t, (z.1, η)) : ℝ × (ℝ × ℝ)))
      ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) z.2 :=
    HasDerivAt.prodMk (hasDerivAt_const _ _)
      (HasDerivAt.prodMk (hasDerivAt_const _ _) (hasDerivAt_id' _))
  have hmaps : MapsTo (fun η : ℝ => ((t, (z.1, η)) : ℝ × (ℝ × ℝ))) univ
      (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    fun η _ => ⟨show (0 : ℝ) ≤ t from ht, trivial⟩
  have hc := HasFDerivWithinAt.comp_hasDerivWithinAt (x := z.2)
    (f := fun η : ℝ => ((t, (z.1, η)) : ℝ × (ℝ × ℝ))) (l := G)
    (l' := fderivWithin ℝ G (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (t, z))
    hG.hasFDerivWithinAt hγ.hasDerivWithinAt hmaps
  exact (hasDerivWithinAt_univ.1 hc).deriv

/-- The scalar curl of a train slice, `Ec tr t`, at `t ≥ 0`, as a difference of within derivatives of
the space-time components. -/
theorem Ec_eq_fderivWithin {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {t : ℝ} (ht : 0 ≤ t)
    (z : ℝ × ℝ) :
    UnforcedLeray.B0238.Ec tr t z =
      fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 1) (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))
          (t, z) (0, (1, 0)) -
        fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 0) (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))
          (t, z) (0, (0, 1)) := by
  have h1 : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 1)
      (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp_contDiffOn
      tr.isTrain.smooth_v
  have h0 : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 0)
      (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp_contDiffOn
      tr.isTrain.smooth_v
  have hm : (t, z) ∈ Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := ⟨show (0 : ℝ) ≤ t from ht, trivial⟩
  have e1 : UnforcedLeray.Cyl.partialQ (fun w : ℝ × ℝ => tr.v t w 1) z =
      fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 1) (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))
        (t, z) (0, (1, 0)) :=
    partialQ_eq_fderivWithin_half (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 1) ht z
      (h1.differentiableOn (by norm_num) _ hm)
  have e0 : UnforcedLeray.Cyl.partialEta (fun w : ℝ × ℝ => tr.v t w 0) z =
      fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 0) (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))
        (t, z) (0, (0, 1)) :=
    partialEta_eq_fderivWithin_half (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 0) ht z
      (h0.differentiableOn (by norm_num) _ hm)
  unfold UnforcedLeray.B0238.Ec UnforcedLeray.Cyl.curl
  rw [e1, e0]

/-- The scalar curl of the train is smooth on `[0, ∞) × ℝ²` (within). -/
theorem Ec_contDiffOn {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) :
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0238.Ec tr p.1 p.2)
      (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
  have h1 : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 1)
      (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp_contDiffOn
      tr.isTrain.smooth_v
  have h0 : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 0)
      (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp_contDiffOn
      tr.isTrain.smooth_v
  refine ContDiffOn.congr ?_ (fun p hp => Ec_eq_fderivWithin tr hp.1 p.2)
  refine ContDiffOn.sub ?_ ?_
  · exact (h1.fderivWithin halfST_uniqueDiffOn (m := ∞) (by simp)).clm_apply contDiffOn_const
  · exact (h0.fderivWithin halfST_uniqueDiffOn (m := ∞) (by simp)).clm_apply contDiffOn_const

end UnforcedLeray.Short.IIIa
