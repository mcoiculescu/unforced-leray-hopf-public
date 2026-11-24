import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.PtOrg
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.PsiJets.QSwap
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.PsiJets.EtaSwap
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VelBand

/-!
# `PartIII-b:C/rep/8/2/3/2/4`: the stream shift `streamShift`

Source of record: `the November 2 reference manuscript` 2045-2051 (`v = ∇^⊥ψ`).
For a stream pair `(ψ, v)` the age-spatial jet of `ψ` one order higher is the derivative of the
age slice `g z = ∂_s^ℓ ψ(s,z)`.  Its gradient is `z ↦ T(∂_s^ℓ v(s,z))` with the fixed linear map
`T w h = h₁ w₁ - h₂ w₀` of norm at most `2` (`PsiQSwap`, `PsiEtaSwap`), so the jets satisfy
`‖∂_s^ℓ D^{m+1} ψ‖ ≤ 2 ‖∂_s^ℓ D^m v‖`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)

/-- The linear map `w ↦ (h ↦ h₁ w₁ - h₂ w₀)` from the velocity space to the dual of the plane. -/
def streamVecMap : UnforcedLeray.Train.Vec →L[ℝ] (Plane →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => (w 1) • ContinuousLinearMap.fst ℝ ℝ ℝ - (w 0) • ContinuousLinearMap.snd ℝ ℝ ℝ
      map_add' := fun a b => by
        refine ContinuousLinearMap.ext (fun h => ?_)
        simp [PiLp.add_apply] <;> ring
      map_smul' := fun c a => by
        refine ContinuousLinearMap.ext (fun h => ?_)
        simp [PiLp.smul_apply] <;> ring }

theorem streamVecMap_apply (w : UnforcedLeray.Train.Vec) (h : Plane) :
    streamVecMap w h = h.1 * w 1 - h.2 * w 0 := by
  simp [streamVecMap] <;> ring

theorem streamVecMap_apply_le (w : UnforcedLeray.Train.Vec) (h : Plane) :
    ‖streamVecMap w h‖ ≤ 2 * ‖w‖ * ‖h‖ := by
  rw [streamVecMap_apply, Real.norm_eq_abs]
  have h1 : |w 1| ≤ ‖w‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le w 1
  have h0 : |w 0| ≤ ‖w‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le w 0
  have hh1 : |h.1| ≤ ‖h‖ := by simpa [Real.norm_eq_abs] using norm_fst_le h
  have hh2 : |h.2| ≤ ‖h‖ := by simpa [Real.norm_eq_abs] using norm_snd_le h
  calc |h.1 * w 1 - h.2 * w 0| ≤ |h.1 * w 1| + |h.2 * w 0| := abs_sub _ _
    _ = |h.1| * |w 1| + |h.2| * |w 0| := by rw [abs_mul, abs_mul]
    _ ≤ ‖h‖ * ‖w‖ + ‖h‖ * ‖w‖ :=
        add_le_add (mul_le_mul hh1 h1 (abs_nonneg _) (norm_nonneg _))
          (mul_le_mul hh2 h0 (abs_nonneg _) (norm_nonneg _))
    _ = 2 * ‖w‖ * ‖h‖ := by ring

theorem streamVecMap_le_two : ‖streamVecMap‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun w => ?_)
  exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun h => streamVecMap_apply_le w h)

/-- **Target** `streamShift`: the stream shift of the age jets (`StreamShift`). -/
theorem streamShift : StreamShift := by
  intro ψ v hsp ℓ m s hs z
  have hΨ := hsp.1
  have hV := hsp.2.1
  set g : Plane → ℝ := fun z'' => iteratedDeriv ℓ (fun r => ψ r z'') s with hgd
  set V : Plane → UnforcedLeray.Train.Vec := fun z'' => iteratedDeriv ℓ (fun r => v r z'') s
    with hVd
  have hgC : ∀ z' : Plane, ContDiffAt ℝ ((m + 1 : ℕ) : WithTop ℕ∞) g z' := fun z' =>
    UnforcedLeray.Short.IIb.vb_slice_contDiffAt (fun x : ℝ × Plane => ψ x.1 x.2) hΨ ℓ (m + 1) hs z'
  have hVC : ∀ z' : Plane, ContDiffAt ℝ (m : WithTop ℕ∞) V z' := fun z' =>
    UnforcedLeray.Short.IIb.vb_slice_contDiffAt (fun x : ℝ × Plane => v x.1 x.2) hV ℓ m hs z'
  have hdiff : ∀ z' : Plane, DifferentiableAt ℝ g z' := fun z' =>
    (hgC z').differentiableAt (by exact_mod_cast Nat.succ_ne_zero m)
  have hfd : ∀ z' : Plane, fderiv ℝ g z' = streamVecMap (V z') := by
    intro z'
    refine ContinuousLinearMap.ext (fun h => ?_)
    have hq : HasDerivAt (fun q : ℝ => g (q, z'.2)) (fderiv ℝ g z' ((1 : ℝ), (0 : ℝ))) z'.1 := by
      have hl : HasDerivAt (fun q : ℝ => (q, z'.2)) ((1 : ℝ), (0 : ℝ)) z'.1 :=
        (hasDerivAt_id' z'.1).prodMk (hasDerivAt_const z'.1 z'.2)
      exact (hdiff z').hasFDerivAt.comp_hasDerivAt z'.1 hl
    have ht : HasDerivAt (fun t : ℝ => g (z'.1, t)) (fderiv ℝ g z' ((0 : ℝ), (1 : ℝ))) z'.2 := by
      have hl : HasDerivAt (fun t : ℝ => (z'.1, t)) ((0 : ℝ), (1 : ℝ)) z'.2 :=
        (hasDerivAt_const z'.2 z'.1).prodMk (hasDerivAt_id' z'.2)
      exact (hdiff z').hasFDerivAt.comp_hasDerivAt z'.2 hl
    have hq' := psiQSwap_proof ψ v hsp ℓ s hs z'.1 z'.2
    have ht' := psiEtaSwap_proof ψ v hsp ℓ s hs z'.1 z'.2
    have e1 : fderiv ℝ g z' ((1 : ℝ), (0 : ℝ)) = V z' 1 := hq.unique hq'
    have e2 : fderiv ℝ g z' ((0 : ℝ), (1 : ℝ)) = -(V z' 0) := ht.unique ht'
    have step : fderiv ℝ g z' h =
        h.1 * fderiv ℝ g z' ((1 : ℝ), (0 : ℝ)) + h.2 * fderiv ℝ g z' ((0 : ℝ), (1 : ℝ)) := by
      have hdec : h = h.1 • ((1 : ℝ), (0 : ℝ)) + h.2 • ((0 : ℝ), (1 : ℝ)) := by
        ext <;> simp
      conv_lhs => rw [hdec]
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    rw [step, e1, e2, streamVecMap_apply]
    ring
  have hfun : fderiv ℝ g = fun z' => streamVecMap (V z') := funext hfd
  show ‖iteratedFDeriv ℝ (m + 1) g z‖ ≤ 2 * ‖iteratedFDeriv ℝ m V z‖
  calc ‖iteratedFDeriv ℝ (m + 1) g z‖ = ‖iteratedFDeriv ℝ m (fun z' => streamVecMap (V z')) z‖ := by
        rw [← norm_iteratedFDeriv_fderiv, hfun]
    _ = ‖streamVecMap.compContinuousMultilinearMap (iteratedFDeriv ℝ m V z)‖ := by
        rw [show (fun z' => streamVecMap (V z')) = streamVecMap ∘ V from rfl,
          ContinuousLinearMap.iteratedFDeriv_comp_left streamVecMap (hVC z) (le_refl _)]
    _ ≤ ‖streamVecMap‖ * ‖iteratedFDeriv ℝ m V z‖ :=
        ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ 2 * ‖iteratedFDeriv ℝ m V z‖ := mul_le_mul_of_nonneg_right streamVecMap_le_two (norm_nonneg _)

end UnforcedLeray.Short.PartIIIb.Concrete
