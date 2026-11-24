import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.PtOrg
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VelBand

/-!
# `PartIII-b:C/rep/8/2/3/2/6`: the fundamental theorem of calculus in `eta`, `EtaSegment`

Source of record: `the November 2 reference manuscript` 5484-5492 (calculus).
For fixed `s > 0`, `q`, the map `t |-> d^l_s F(s,(q,t))` has derivative bounded by the jet
`d^l_s DF(s,(q,t))` (`norm_iteratedFDeriv_one`); the mean value inequality on `uIcc a b` plus the
triangle inequality gives the claim. Template: `psiEtaSegment_proof`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)

/-- The slow-age slice `z |-> d^l_s F(s,z)` of a scalar field. -/
private def etaG (F : ℝ → Plane → ℝ) (l : ℕ) (s : ℝ) (z : Plane) : ℝ :=
  iteratedDeriv l (fun r => F r z) s

/-- **FTC in `eta`** (source 5484-5492, calculus). -/
theorem etaSegment : EtaSegment := by
  intro F hF l s hs q a b B hB
  have hgC : ∀ w : Plane, ContDiffAt ℝ 1 (etaG F l s) w := fun w =>
    UnforcedLeray.Short.IIb.vb_slice_contDiffAt (fun x : ℝ × Plane => F x.1 x.2) hF l 1 hs w
  have hgd : ∀ w : Plane, HasFDerivAt (etaG F l s) (fderiv ℝ (etaG F l s) w) w := fun w =>
    ((hgC w).differentiableAt (by norm_num)).hasFDerivAt
  have hdiff : ∀ t : ℝ,
      HasDerivAt (fun t' : ℝ => etaG F l s (q, t')) (fderiv ℝ (etaG F l s) (q, t) (0, 1)) t := by
    intro t
    have hl : HasDerivAt (fun t' : ℝ => ((q, t') : Plane)) ((0 : ℝ), (1 : ℝ)) t :=
      (hasDerivAt_const t q).prodMk (hasDerivAt_id' t)
    exact (hgd (q, t)).comp_hasDerivAt t hl
  have hnorm1 : ∀ w : Plane,
      ‖UnforcedLeray.Short.PartI.ageJet l 1 F s w‖ = ‖fderiv ℝ (etaG F l s) w‖ := by
    intro w
    unfold UnforcedLeray.Short.PartI.ageJet UnforcedLeray.Train.jet
    exact norm_iteratedFDeriv_one (𝕜 := ℝ) (etaG F l s) (x := w)
  have hz : ∀ w : Plane,
      ‖UnforcedLeray.Short.PartI.ageJet l 0 F s w‖ = ‖etaG F l s w‖ := by
    intro w
    unfold UnforcedLeray.Short.PartI.ageJet UnforcedLeray.Train.jet
    rw [norm_iteratedFDeriv_zero]
    rfl
  have hbound : ∀ t ∈ uIcc a b, ‖fderiv ℝ (etaG F l s) (q, t) (0, 1)‖ ≤ B := by
    intro t ht
    have h1 := hB t ht
    rw [hnorm1] at h1
    have h2 : ‖fderiv ℝ (etaG F l s) (q, t) (0, 1)‖ ≤
        ‖fderiv ℝ (etaG F l s) (q, t)‖ * ‖((0 : ℝ), (1 : ℝ))‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h3 : ‖((0 : ℝ), (1 : ℝ))‖ = 1 := by norm_num [Prod.norm_def]
    rw [h3, mul_one] at h2
    exact h2.trans h1
  have hdiffB : ‖etaG F l s (q, a) - etaG F l s (q, b)‖ ≤ B * ‖a - b‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun t' : ℝ => etaG F l s (q, t'))
      (f' := fun t : ℝ => fderiv ℝ (etaG F l s) (q, t) (0, 1))
      (s := uIcc a b) (C := B)
      (fun t _ => (hdiff t).hasDerivWithinAt) hbound (convex_uIcc a b)
      right_mem_uIcc left_mem_uIcc
  have hn := norm_sub_norm_le (etaG F l s (q, a)) (etaG F l s (q, b))
  rw [hz, hz]
  simp only [Real.norm_eq_abs] at hdiffB hn ⊢
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete
