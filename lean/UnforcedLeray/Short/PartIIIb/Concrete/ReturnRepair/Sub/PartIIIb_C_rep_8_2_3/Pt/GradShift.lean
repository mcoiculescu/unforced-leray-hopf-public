import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.PtOrg
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.TrainVelSmooth

/-!
# `PartIII-b:C/rep/8/2/3/2/5`: the gradient jet shift `gradJetShift_of`

Source of record: `the November 2 reference manuscript` 2045-2051 (`v = ∇^⊥ψ`) and
468-478 (`∇(p - p_c^p)`).  For a jointly smooth scalar field `F`, the velocity `v = ∇^⊥F` is a
stream pair with `F`; by `StreamShift`, `‖∂_s^ℓ D^{m+1}F‖ ≤ 2 ‖∂_s^ℓ D^m v‖`.  The rotation
`v = R ∘ gradS` is a linear isometry equivalence of the velocity space, so the age-spatial jets of
`v` and `∇F` have equal norms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)

/-- The rotation `(a,b) ↦ (-b,a)` of the velocity space, as a linear isometry equivalence. -/
def rotVec : UnforcedLeray.Train.Vec ≃ₗᵢ[ℝ] UnforcedLeray.Train.Vec where
  toFun w := UnforcedLeray.Train.toVec (-(w 1), w 0)
  invFun w := UnforcedLeray.Train.toVec (w 1, -(w 0))
  map_add' a b := by
    apply UnforcedLeray.Train.Vec.ext <;> simp <;> ring
  map_smul' c a := by
    apply UnforcedLeray.Train.Vec.ext <;> simp <;> ring
  left_inv w := by
    apply UnforcedLeray.Train.Vec.ext <;> simp
  right_inv w := by
    apply UnforcedLeray.Train.Vec.ext <;> simp
  norm_map' w := by
    show ‖UnforcedLeray.Train.toVec (-(w 1), w 0)‖ = ‖w‖
    have hw : w = UnforcedLeray.Train.toVec (w 0, w 1) := UnforcedLeray.Train.eq_toVec w
    rw [UnforcedLeray.Train.norm_toVec]
    conv_rhs => rw [hw]
    rw [UnforcedLeray.Train.norm_toVec]
    congr 1
    dsimp only
    ring

/-- Commuting a time-derivative with a fixed linear map on the velocity space. -/
theorem iteratedDeriv_linear_comm (Lc : UnforcedLeray.Train.Vec →ₗ[ℝ] UnforcedLeray.Train.Vec)
    (n : ℕ) (f : ℝ → UnforcedLeray.Train.Vec) {s : ℝ} (hf : ContDiffAt ℝ n f s) :
    iteratedDeriv n (fun r => Lc (f r)) s = Lc (iteratedDeriv n f s) := by
  set Lk := LinearMap.toContinuousLinearMap Lc with hLk
  have hfun : (fun r => Lc (f r)) = Lk ∘ f := rfl
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv, hfun]
  have key := ContinuousLinearMap.iteratedFDeriv_comp_left Lk hf (le_refl (n : WithTop ℕ∞))
  rw [key]
  rfl

/-- **Target** `gradJetShift_of`: the gradient jet shift from the stream shift (`GradJetShift`). -/
theorem gradJetShift_of (h : StreamShift) : GradJetShift := by
  intro F hF ℓ m s hs z
  have hX : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => UnforcedLeray.GaussianVortex.partialX (F x.1) x.2)
      (Ioi 0 ×ˢ (univ : Set Plane)) :=
    (UnforcedLeray.Short.IIb.trainVel_fderiv_dir_contDiffOn hF (1, 0)).congr
      (fun x hx => UnforcedLeray.Short.IIb.trainVel_partialX_eq hF hx.1 x.2)
  have hY : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => UnforcedLeray.GaussianVortex.partialY (F x.1) x.2)
      (Ioi 0 ×ˢ (univ : Set Plane)) :=
    (UnforcedLeray.Short.IIb.trainVel_fderiv_dir_contDiffOn hF (0, 1)).congr
      (fun x hx => UnforcedLeray.Short.IIb.trainVel_partialY_eq hF hx.1 x.2)
  have hpair : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => (-(UnforcedLeray.GaussianVortex.partialY (F x.1) x.2),
        UnforcedLeray.GaussianVortex.partialX (F x.1) x.2))
      (Ioi 0 ×ˢ (univ : Set Plane)) := hY.neg.prodMk hX
  set v : ℝ → Plane → UnforcedLeray.Train.Vec := fun r w =>
    UnforcedLeray.Train.toVec (UnforcedLeray.GaussianVortex.perpendicularGradient (F r) w) with hvd
  have hvS : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (Ioi 0 ×ˢ (univ : Set Plane)) :=
    (UnforcedLeray.Train.toVecL.toContinuousLinearMap.contDiff.comp_contDiffOn hpair).congr
      (fun x _ => rfl)
  have hsp : UnforcedLeray.Short.IIb.IsStreamPair F v := ⟨hF, hvS, fun s hs z => rfl⟩
  have h1 := h F v hsp ℓ m s hs z
  have hvG : ∀ r w, v r w = rotVec (UnforcedLeray.Train.gradS (F r) w) := fun r w => rfl
  have hcomm : ∀ w : Plane, iteratedDeriv ℓ (fun r => v r w) s =
      rotVec (iteratedDeriv ℓ (fun r => UnforcedLeray.Train.gradS (F r) w) s) := by
    intro w
    have hvw : ContDiffAt ℝ ℓ (fun r => v r w) s := by
      have h1' : ContDiffAt ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (s, w) :=
        hvS.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hs, mem_univ _⟩)
      have h2 : ContDiffAt ℝ ∞ (fun r : ℝ => (r, w)) s := contDiffAt_id.prodMk contDiffAt_const
      refine (h1'.comp s h2).of_le ?_
      exact_mod_cast le_top
    have e1 : (fun r => UnforcedLeray.Train.gradS (F r) w) =
        fun r => rotVec.symm (v r w) := by
      funext r
      rw [hvG r w, LinearIsometryEquiv.symm_apply_apply]
    have hG : iteratedDeriv ℓ (fun r => UnforcedLeray.Train.gradS (F r) w) s =
        rotVec.symm (iteratedDeriv ℓ (fun r => v r w) s) := by
      rw [e1]
      exact iteratedDeriv_linear_comm rotVec.symm.toLinearEquiv.toLinearMap ℓ (fun r => v r w) hvw
    rw [hG, LinearIsometryEquiv.apply_symm_apply]
  have hfunW : (fun w => iteratedDeriv ℓ (fun r => v r w) s) =
      rotVec ∘ (fun w => iteratedDeriv ℓ (fun r => UnforcedLeray.Train.gradS (F r) w) s) :=
    funext hcomm
  have hnorm : ‖UnforcedLeray.Short.PartI.ageJet ℓ m v s z‖ =
      ‖UnforcedLeray.Short.PartI.ageJet ℓ m (fun r w => UnforcedLeray.Train.gradS (F r) w) s z‖ := by
    show ‖iteratedFDeriv ℝ m (fun w => iteratedDeriv ℓ (fun r => v r w) s) z‖ =
      ‖iteratedFDeriv ℝ m (fun w => iteratedDeriv ℓ (fun r => UnforcedLeray.Train.gradS (F r) w) s) z‖
    rw [hfunW]
    exact rotVec.norm_iteratedFDeriv_comp_left _ z m
  calc ‖UnforcedLeray.Short.PartI.ageJet ℓ (m + 1) F s z‖
      ≤ 2 * ‖UnforcedLeray.Short.PartI.ageJet ℓ m v s z‖ := h1
    _ = 2 * ‖UnforcedLeray.Short.PartI.ageJet ℓ m (fun r w => UnforcedLeray.Train.gradS (F r) w) s z‖ := by
        rw [hnorm]

end UnforcedLeray.Short.PartIIIb.Concrete
