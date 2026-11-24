import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_6_2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.RingSubst.Term2D1

/-!
# `PartIII-b:C/rep/8/2/6/2/2`: the second flat train derivatives are bounded by the weight

Source `the November 2 reference manuscript` lines 5463, 5464-5465.
`flatD2 L s x j l = emb (fderiv (fun x' => fderiv (trainV L s) x' (flatDir l)) x (flatDir j))`.
The second derivative of the flat velocity is the second derivative of the dilation-variable
velocity `trainFv L` at `(log s, x)` (with the `vecPairRing` projection of norm at most one),
which is the `j = 2` term of `trainWeight 3`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem norm_inr_le_ring (w : ℝ × ℝ) :
    ‖(ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) w‖ ≤ ‖w‖ := by
  simp only [ContinuousLinearMap.inr_apply]
  exact norm_prod_le_iff.2 ⟨by simp, le_rfl⟩

theorem fderiv_trainV_eq_ring (L : ReturnLevel) {s : ℝ} (hs : 0 < s) (y : ℝ × ℝ) :
    fderiv ℝ (trainV L s) y = vecPairRing.comp
      ((fderiv ℝ (trainFv L) (Real.log s, y)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) := by
  have hι : HasFDerivAt (fun y' : ℝ × ℝ => (Real.log s, y'))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) y :=
    hasFDerivAt_prodMk_right (Real.log s) y
  have hF : HasFDerivAt (trainFv L) (fderiv ℝ (trainFv L) (Real.log s, y)) (Real.log s, y) :=
    ((trainFv_contDiffAt_ring L (Real.log s, y)).differentiableAt (by simp)).hasFDerivAt
  have hcomp := hF.comp y hι
  have hpair : HasFDerivAt (vecPairRing ∘ fun y' => trainFv L (Real.log s, y'))
      (vecPairRing.comp ((fderiv ℝ (trainFv L) (Real.log s, y)).comp
        (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)))) y :=
    vecPairRing.hasFDerivAt.comp y hcomp
  rw [trainV_eq_comp_ring L hs, hpair.fderiv]

theorem fderiv_trainV_apply_eq_ring (L : ReturnLevel) {s : ℝ} (hs : 0 < s) (w : ℝ × ℝ) :
    (fun x' => fderiv ℝ (trainV L s) x' w) = fun x' =>
      vecPairRing (fderiv ℝ (trainFv L) (Real.log s, x') (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) w)) := by
  funext x'
  rw [fderiv_trainV_eq_ring L hs x']
  rfl

/-- The second flat derivative in the directions `v, w`, in terms of the second derivative of the
dilation-variable velocity. -/
theorem fderiv_fderiv_trainV_ring (L : ReturnLevel) {s : ℝ} (hs : 0 < s) (x v w : ℝ × ℝ) :
    fderiv ℝ (fun x' => fderiv ℝ (trainV L s) x' w) x v =
      vecPairRing (fderiv ℝ (fderiv ℝ (trainFv L)) (Real.log s, x)
        (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) v) (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) w)) := by
  rw [fderiv_trainV_apply_eq_ring L hs w]
  have hι : HasFDerivAt (fun y' : ℝ × ℝ => (Real.log s, y'))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) x :=
    hasFDerivAt_prodMk_right (Real.log s) x
  have hc : DifferentiableAt ℝ (fderiv ℝ (trainFv L)) (Real.log s, x) :=
    ((trainFv_contDiffAt_ring L (Real.log s, x)).fderiv_right (m := 1) (by simp)).differentiableAt
      (by simp)
  have hK : HasFDerivAt (fun z' => fderiv ℝ (trainFv L) z'
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) w))
      ((fderiv ℝ (fderiv ℝ (trainFv L)) (Real.log s, x)).flip
        (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) w)) (Real.log s, x) := by
    have h := hc.hasFDerivAt.clm_apply (hasFDerivAt_const (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) w)
      (Real.log s, x))
    simpa using h
  have hd : HasFDerivAt (fun x' => vecPairRing (fderiv ℝ (trainFv L) (Real.log s, x')
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) w)))
      (vecPairRing.comp (((fderiv ℝ (fderiv ℝ (trainFv L)) (Real.log s, x)).flip
        (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) w)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)))) x :=
    vecPairRing.hasFDerivAt.comp x (hK.comp x hι)
  rw [hd.fderiv]
  simp [ContinuousLinearMap.flip_apply]

theorem norm_fderiv_fderiv_trainFv_le_ring (L : ReturnLevel) (z : ℝ × (ℝ × ℝ)) :
    ‖fderiv ℝ (fderiv ℝ (trainFv L)) z‖ = ‖iteratedFDeriv ℝ 2 (trainFv L) z‖ := by
  rw [← norm_iteratedFDeriv_one (fderiv ℝ (trainFv L)) (x := z)]
  rw [norm_iteratedFDeriv_fderiv (n := 1)]

/-- **`TrainFlatD2Bound`** (source 5463, 5464-5465): `‖D²_flat v‖ ≤ 𝔴₃`. -/
theorem trainFlatD2Bound (L : ReturnLevel) : TrainFlatD2Bound L := by
  intro p hp j l
  have hj : ‖flatDir j‖ ≤ 1 := by
    fin_cases j <;> simp [flatDir]
  have hl : ‖flatDir l‖ ≤ 1 := by
    fin_cases l <;> simp [flatDir]
  have hstep1 : ‖flatD2 L p.1 p.2 j l‖ ≤
      ‖fderiv ℝ (fun x' => fderiv ℝ (trainV L p.1) x' (flatDir l)) p.2 (flatDir j)‖ := by
    unfold flatD2
    exact norm_emb_le _
  rw [fderiv_fderiv_trainV_ring L hp] at hstep1
  have hstep2 : ‖vecPairRing (fderiv ℝ (fderiv ℝ (trainFv L)) (Real.log p.1, p.2)
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) (flatDir j))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) (flatDir l)))‖ ≤
      ‖fderiv ℝ (fderiv ℝ (trainFv L)) (Real.log p.1, p.2)‖ := by
    refine (norm_vecPairRing_le _).trans ?_
    set A := fderiv ℝ (fderiv ℝ (trainFv L)) (Real.log p.1, p.2) with hA
    have ha : ‖ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) (flatDir j)‖ ≤ 1 :=
      (norm_inr_le_ring _).trans hj
    have hb : ‖ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) (flatDir l)‖ ≤ 1 :=
      (norm_inr_le_ring _).trans hl
    calc ‖A (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) (flatDir j))
          (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) (flatDir l))‖
        ≤ ‖A (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) (flatDir j))‖ *
          ‖ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) (flatDir l)‖ :=
          (A _).le_opNorm _
      _ ≤ (‖A‖ * ‖ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) (flatDir j)‖) *
          ‖ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) (flatDir l)‖ := by
          gcongr
          exact A.le_opNorm _
      _ ≤ (‖A‖ * 1) * 1 := by gcongr
      _ = ‖A‖ := by ring
  have hsum0 := le_trans hstep1 hstep2
  have hA2 := norm_fderiv_fderiv_trainFv_le_ring L (Real.log p.1, p.2)
  have hsingle := Finset.single_le_sum
    (f := fun k : ℕ => ‖iteratedFDeriv ℝ k (trainFv L) (Real.log p.1, p.2)‖ +
      ‖iteratedFDeriv ℝ k (trainFp L) (Real.log p.1, p.2)‖ +
      ‖iteratedFDeriv ℝ k (trainFpsi L) (Real.log p.1, p.2)‖)
    (fun k _ => by positivity) (Finset.mem_range.2 (by norm_num : (2 : ℕ) < 5))
  have hB := norm_nonneg (iteratedFDeriv ℝ 2 (trainFp L) (Real.log p.1, p.2))
  have hC := norm_nonneg (iteratedFDeriv ℝ 2 (trainFpsi L) (Real.log p.1, p.2))
  have hsumfin : ‖fderiv ℝ (fderiv ℝ (trainFv L)) (Real.log p.1, p.2)‖ ≤
      ∑ k ∈ Finset.range 5,
        (‖iteratedFDeriv ℝ k (trainFv L) (Real.log p.1, p.2)‖ +
          ‖iteratedFDeriv ℝ k (trainFp L) (Real.log p.1, p.2)‖ +
          ‖iteratedFDeriv ℝ k (trainFpsi L) (Real.log p.1, p.2)‖) := by
    rw [hA2]
    linarith
  have hpow : (1 : ℝ) ≤ (1 + |p.2.2|) ^ 3 :=
    one_le_pow₀ (by linarith [abs_nonneg p.2.2])
  have hnn : 0 ≤ ∑ k ∈ Finset.range 5,
      (‖iteratedFDeriv ℝ k (trainFv L) (Real.log p.1, p.2)‖ +
        ‖iteratedFDeriv ℝ k (trainFp L) (Real.log p.1, p.2)‖ +
        ‖iteratedFDeriv ℝ k (trainFpsi L) (Real.log p.1, p.2)‖) :=
    Finset.sum_nonneg (fun k _ => by positivity)
  unfold trainWeight
  calc ‖flatD2 L p.1 p.2 j l‖ ≤ _ := hsum0.trans hsumfin
    _ ≤ (1 + |p.2.2|) ^ 3 * ∑ k ∈ Finset.range 5,
        (‖iteratedFDeriv ℝ k (trainFv L) (Real.log p.1, p.2)‖ +
          ‖iteratedFDeriv ℝ k (trainFp L) (Real.log p.1, p.2)‖ +
          ‖iteratedFDeriv ℝ k (trainFpsi L) (Real.log p.1, p.2)‖) :=
      le_mul_of_one_le_left hnn hpow

end UnforcedLeray.Short.PartIIIb.Concrete
