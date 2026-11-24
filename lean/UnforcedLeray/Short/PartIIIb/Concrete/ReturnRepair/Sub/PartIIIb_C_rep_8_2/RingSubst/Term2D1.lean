import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_6_2

/-!
# `PartIII-b:C/rep/8/2/6/2/1`: the first flat train derivatives are bounded by the weight

Source `the November 2 reference manuscript` lines 5462, 5464-5465.
Here `flatD1 L s x j = emb (fderiv (trainV L s) x (flatDir j))`, and the flat velocity
`(s, x) ↦ trainV L s x` is the dilation-variable function `trainFv L (log s, x)` restricted to the
two velocity components.  The operator norm of its `x`-derivative is at most the first-order
term of `trainWeight`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The train flat velocity in the dilation variable is `C^∞` at every point. -/
theorem trainFv_contDiffAt_ring (L : ReturnLevel) (z : ℝ × (ℝ × ℝ)) :
    ContDiffAt ℝ ∞ (trainFv L) z := by
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hmem : (Ici (0 : ℝ)) ×ˢ (univ : Set (ℝ × ℝ)) ∈ 𝓝 (Real.exp z.1, z.2) :=
    Filter.mem_of_superset
      (hopen.mem_nhds (show (Real.exp z.1, z.2) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) from
        ⟨Real.exp_pos _, mem_univ _⟩))
      (prod_mono Ioi_subset_Ici_self (subset_refl _))
  have hc := L.train.isTrain.smooth_v.contDiffAt hmem
  have hφ : ContDiffAt ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => (Real.exp z.1, z.2)) z :=
    ((Real.contDiff_exp.comp contDiff_fst).contDiffAt).prodMk contDiff_snd.contDiffAt
  exact hc.comp z hφ

/-- The projection of a `UnforcedLeray.Cyl.Vec2` onto its two components, as a continuous linear map. -/
def vecPairRing : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ × ℝ :=
  (EuclideanSpace.proj (0 : Fin 2)).prod (EuclideanSpace.proj (1 : Fin 2))

theorem vecPairRing_apply (u : UnforcedLeray.Cyl.Vec2) : vecPairRing u = (u 0, u 1) := rfl

theorem norm_vecPairRing_le (u : UnforcedLeray.Cyl.Vec2) : ‖vecPairRing u‖ ≤ ‖u‖ := by
  rw [vecPairRing_apply]
  refine norm_prod_le_iff.2 ⟨?_, ?_⟩
  · exact PiLp.norm_apply_le _ _
  · exact PiLp.norm_apply_le _ _

theorem trainV_eq_comp_ring (L : ReturnLevel) {s : ℝ} (hs : 0 < s) :
    trainV L s = vecPairRing ∘ (fun y => trainFv L (Real.log s, y)) := by
  funext y
  have h : trainFv L (Real.log s, y) = L.train.v s y := by
    unfold trainFv
    rw [Real.exp_log hs]
  simp only [Function.comp_apply, h, vecPairRing_apply, trainV]

/-- The derivative of the flat velocity in a direction is controlled by the first derivative of
the dilation-variable velocity. -/
theorem norm_fderiv_trainV_le_ring (L : ReturnLevel) {s : ℝ} (hs : 0 < s) (x w : ℝ × ℝ) :
    ‖fderiv ℝ (trainV L s) x w‖ ≤ ‖fderiv ℝ (trainFv L) (Real.log s, x)‖ * ‖w‖ := by
  have hι : HasFDerivAt (fun y : ℝ × ℝ => (Real.log s, y))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) x :=
    hasFDerivAt_prodMk_right (Real.log s) x
  have hF : HasFDerivAt (trainFv L) (fderiv ℝ (trainFv L) (Real.log s, x)) (Real.log s, x) :=
    ((trainFv_contDiffAt_ring L (Real.log s, x)).differentiableAt (by simp)).hasFDerivAt
  have hcomp := hF.comp x hι
  have hpair : HasFDerivAt (vecPairRing ∘ fun y => trainFv L (Real.log s, y))
      (vecPairRing.comp ((fderiv ℝ (trainFv L) (Real.log s, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)))) x :=
    (vecPairRing.hasFDerivAt).comp x hcomp
  rw [trainV_eq_comp_ring L hs, hpair.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  have hinr : ‖(ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) w‖ ≤ ‖w‖ := by
    simp only [ContinuousLinearMap.inr_apply]
    exact norm_prod_le_iff.2 ⟨by simp, le_rfl⟩
  calc ‖vecPairRing (fderiv ℝ (trainFv L) (Real.log s, x) ((ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) w))‖
      ≤ ‖fderiv ℝ (trainFv L) (Real.log s, x) ((ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) w)‖ :=
        norm_vecPairRing_le _
    _ ≤ ‖fderiv ℝ (trainFv L) (Real.log s, x)‖ *
        ‖(ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) w‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderiv ℝ (trainFv L) (Real.log s, x)‖ * ‖w‖ :=
        mul_le_mul_of_nonneg_left hinr (norm_nonneg _)

/-- **`TrainFlatD1Bound`** (source 5462, 5464-5465): `‖D_flat v‖ ≤ 𝔴₃`. -/
theorem trainFlatD1Bound (L : ReturnLevel) : TrainFlatD1Bound L := by
  intro p hp j
  have hw : ‖flatDir j‖ ≤ 1 := by
    fin_cases j <;> simp [flatDir]
  have hstep1 : ‖flatD1 L p.1 p.2 j‖ ≤ ‖fderiv ℝ (trainV L p.1) p.2 (flatDir j)‖ := by
    unfold flatD1
    exact norm_emb_le _
  have hstep2 : ‖fderiv ℝ (trainV L p.1) p.2 (flatDir j)‖ ≤
      ‖fderiv ℝ (trainFv L) (Real.log p.1, p.2)‖ := by
    refine (norm_fderiv_trainV_le_ring L hp p.2 (flatDir j)).trans ?_
    exact mul_le_of_le_one_right (norm_nonneg _) hw
  have hstep3 : ‖fderiv ℝ (trainFv L) (Real.log p.1, p.2)‖ ≤
      ∑ k ∈ Finset.range 5,
        (‖iteratedFDeriv ℝ k (trainFv L) (Real.log p.1, p.2)‖ +
          ‖iteratedFDeriv ℝ k (trainFp L) (Real.log p.1, p.2)‖ +
          ‖iteratedFDeriv ℝ k (trainFpsi L) (Real.log p.1, p.2)‖) := by
    rw [← norm_iteratedFDeriv_one (trainFv L)]
    have hsingle := Finset.single_le_sum
      (f := fun k : ℕ => ‖iteratedFDeriv ℝ k (trainFv L) (Real.log p.1, p.2)‖ +
        ‖iteratedFDeriv ℝ k (trainFp L) (Real.log p.1, p.2)‖ +
        ‖iteratedFDeriv ℝ k (trainFpsi L) (Real.log p.1, p.2)‖)
      (fun k _ => by positivity) (Finset.mem_range.2 (by norm_num : (1 : ℕ) < 5))
    have hB := norm_nonneg (iteratedFDeriv ℝ 1 (trainFp L) (Real.log p.1, p.2))
    have hC := norm_nonneg (iteratedFDeriv ℝ 1 (trainFpsi L) (Real.log p.1, p.2))
    linarith
  have hpow : (1 : ℝ) ≤ (1 + |p.2.2|) ^ 3 :=
    one_le_pow₀ (by linarith [abs_nonneg p.2.2])
  have hnn : 0 ≤ ∑ k ∈ Finset.range 5,
      (‖iteratedFDeriv ℝ k (trainFv L) (Real.log p.1, p.2)‖ +
        ‖iteratedFDeriv ℝ k (trainFp L) (Real.log p.1, p.2)‖ +
        ‖iteratedFDeriv ℝ k (trainFpsi L) (Real.log p.1, p.2)‖) :=
    Finset.sum_nonneg (fun k _ => by positivity)
  unfold trainWeight
  calc ‖flatD1 L p.1 p.2 j‖ ≤ _ := hstep1.trans (hstep2.trans hstep3)
    _ ≤ (1 + |p.2.2|) ^ 3 * ∑ k ∈ Finset.range 5,
        (‖iteratedFDeriv ℝ k (trainFv L) (Real.log p.1, p.2)‖ +
          ‖iteratedFDeriv ℝ k (trainFp L) (Real.log p.1, p.2)‖ +
          ‖iteratedFDeriv ℝ k (trainFpsi L) (Real.log p.1, p.2)‖) :=
      le_mul_of_one_le_left hnn hpow

end UnforcedLeray.Short.PartIIIb.Concrete
