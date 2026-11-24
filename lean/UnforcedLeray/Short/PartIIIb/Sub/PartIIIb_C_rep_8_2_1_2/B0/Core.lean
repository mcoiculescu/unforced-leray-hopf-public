import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_1.Raised
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_1.Smooth
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.RingSubst.Term2D2

/-!
# Shared core for the raw ring derivative bounds `RawD1Bound0`, `RawD1Bound2`
(`PartIII-b:C/rep/8/2/1/2/7`, `/9`)

Source `the November 2 reference manuscript` lines 2073-2077 (`b_raw = v + εH e_z`,
`H = (1-K)ψ`) and 5462-5476.  In dilation variables `z = (σ,(q,η))`, `σ = log s`:
`bRaw L (s,x) = rawPhi L (log s, x)` with `rawPhi = trainFv + ε·rawH·e₁`, where `rawH` is the
raised stream.  The derivatives of `bRaw` in the chart directions are then the derivatives of
`rawPhi` (chain rule `s∂_s = ∂_σ`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Axi

/-- The unit vector `e₁` of the profile space `Merid` (the `e_z` slot, index `1`). -/
def rawE1 : Merid := EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

theorem rawE1_norm : ‖rawE1‖ = 1 := by
  unfold rawE1
  simp

/-- The raised stream `H = ψ - η∂_ηψ - 2∂_σψ` in dilation variables `z = (σ,(q,η))`. -/
def rawH (L : ReturnLevel) (z : ℝ × (ℝ × ℝ)) : ℝ :=
  trainFpsi L z - (z.2.2 * fderiv ℝ (trainFpsi L) z (0, (0, 1)) +
    2 * fderiv ℝ (trainFpsi L) z (1, (0, 0)))

/-- The raw profile `v + ε H e₁` in dilation variables. -/
def rawPhi (L : ReturnLevel) (z : ℝ × (ℝ × ℝ)) : Merid :=
  trainFv L z + (L.ε * rawH L z) • rawE1

theorem trainFv_log (L : ReturnLevel) {p : Chart} (hp : 0 < p.1) :
    trainFv L (Real.log p.1, p.2) = L.train.v p.1 p.2 := by
  unfold trainFv
  rw [Real.exp_log hp]

theorem trainFpsi_contDiff (L : ReturnLevel) : ContDiff ℝ ∞ (trainFpsi L) :=
  trainStreamSmooth L

theorem rawH_eq_stream (L : ReturnLevel) {p : Chart} (hp : 0 < p.1) :
    rawH L (Real.log p.1, p.2) = UnforcedLeray.Cons.C03.raisedStream L.train.ψ p.1 p.2.1 p.2.2 := by
  have hF : Differentiable ℝ (trainFpsi L) := (trainFpsi_contDiff L).differentiable (by simp)
  rw [ringRaised_stream_eq L hF hp p.2.1 p.2.2]
  rfl

theorem bRaw_eq_phi (L : ReturnLevel) {p : Chart} (hp : 0 < p.1) :
    bRaw L p = rawPhi L (Real.log p.1, p.2) := by
  unfold rawPhi
  rw [trainFv_log L hp, rawH_eq_stream L hp]
  unfold bRaw UnforcedLeray.Cons.C03.rawProfile rawE1
  rfl

theorem rawH_hasFDerivAt (L : ReturnLevel) (z : ℝ × (ℝ × ℝ)) :
    ∃ D : (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ, HasFDerivAt (rawH L) D z ∧ ∀ w : ℝ × (ℝ × ℝ),
      D w = fderiv ℝ (trainFpsi L) z w
        - (w.2.2 * fderiv ℝ (trainFpsi L) z (0, (0, 1)) +
            z.2.2 * fderiv ℝ (fderiv ℝ (trainFpsi L)) z w (0, (0, 1)))
        - 2 * fderiv ℝ (fderiv ℝ (trainFpsi L)) z w (1, (0, 0)) := by
  have hFc : ContDiff ℝ ∞ (trainFpsi L) := trainFpsi_contDiff L
  have hF1 : ContDiff ℝ 1 (fderiv ℝ (trainFpsi L)) := hFc.fderiv_right (m := 1) (by simp)
  have hFd : ∀ e : ℝ × (ℝ × ℝ), HasFDerivAt (fun y => fderiv ℝ (trainFpsi L) y e)
      ((fderiv ℝ (fderiv ℝ (trainFpsi L)) z).flip e) z := by
    intro e
    have hc : DifferentiableAt ℝ (fderiv ℝ (trainFpsi L)) z := (hF1.differentiable (by simp)) z
    have h := hc.hasFDerivAt.clm_apply (hasFDerivAt_const e z)
    simpa using h
  have hFF : HasFDerivAt (trainFpsi L) (fderiv ℝ (trainFpsi L) z) z :=
    ((hFc.differentiable (by simp)) z).hasFDerivAt
  have hc1 : HasFDerivAt (fun y : ℝ × (ℝ × ℝ) => y.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) z :=
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasFDerivAt
  have hM := hc1.mul (hFd (0, (0, 1)))
  have hB := (hFd (1, (0, 0))).const_mul (2 : ℝ)
  have hR := hFF.sub (hM.add hB)
  refine ⟨_, hR, fun w => ?_⟩
  simp [ContinuousLinearMap.flip_apply] <;> ring

theorem rawPhi_differentiableAt (L : ReturnLevel) (z : ℝ × (ℝ × ℝ)) :
    DifferentiableAt ℝ (rawPhi L) z := by
  obtain ⟨D, hD, _⟩ := rawH_hasFDerivAt L z
  have hG : DifferentiableAt ℝ (trainFv L) z :=
    (trainFv_contDiffAt_ring L z).differentiableAt (by simp)
  have hP : DifferentiableAt ℝ (fun y => (L.ε * rawH L y) • rawE1) z :=
    (hD.differentiableAt.const_mul L.ε).smul_const rawE1
  exact hG.add hP

theorem rawPhi_fderiv_apply (L : ReturnLevel) (z w : ℝ × (ℝ × ℝ)) :
    fderiv ℝ (rawPhi L) z w =
      fderiv ℝ (trainFv L) z w + (L.ε * fderiv ℝ (rawH L) z w) • rawE1 := by
  obtain ⟨D, hD, hDw⟩ := rawH_hasFDerivAt L z
  have hG : HasFDerivAt (trainFv L) (fderiv ℝ (trainFv L) z) z :=
    ((trainFv_contDiffAt_ring L z).differentiableAt (by simp)).hasFDerivAt
  have hP := (hD.const_mul L.ε).smul_const rawE1
  have key : HasFDerivAt (rawPhi L) (fderiv ℝ (trainFv L) z + ((L.ε) • D).smulRight rawE1) z :=
    hG.add hP
  rw [key.fderiv, hD.fderiv]
  simp

theorem bRaw_fderiv_apply (L : ReturnLevel) {p : Chart} (hp : 0 < p.1) (w : Chart) :
    fderiv ℝ (bRaw L) p w =
      fderiv ℝ (rawPhi L) (Real.log p.1, p.2) ((p.1)⁻¹ * w.1, w.2) := by
  have hlog : HasFDerivAt (fun q : Chart => Real.log q.1)
      ((p.1)⁻¹ • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    (Real.hasDerivAt_log hp.ne').comp_hasFDerivAt p hasFDerivAt_fst
  have hT : HasFDerivAt (fun q : Chart => (Real.log q.1, q.2))
      (((p.1)⁻¹ • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    hlog.prodMk hasFDerivAt_snd
  have hPhi : HasFDerivAt (rawPhi L) (fderiv ℝ (rawPhi L) (Real.log p.1, p.2))
      (Real.log p.1, p.2) :=
    (rawPhi_differentiableAt L _).hasFDerivAt
  have hcomp := hPhi.comp p hT
  have hev : bRaw L =ᶠ[𝓝 p] (rawPhi L ∘ fun q : Chart => (Real.log q.1, q.2)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hp] with q hq
    exact bRaw_eq_phi L hq
  rw [(hcomp.congr_of_eventuallyEq hev).fderiv]
  simp

theorem vecSp_flatD1 (L : ReturnLevel) {p : Chart} (hp : 0 < p.1) (j : Fin 3) :
    vecSp (flatD1 L p.1 p.2 j) =
      merSp (fderiv ℝ (trainFv L) (Real.log p.1, p.2) (0, flatDir j)) := by
  have h : fderiv ℝ (trainV L p.1) p.2 (flatDir j) =
      vecPairRing (fderiv ℝ (trainFv L) (Real.log p.1, p.2)
        (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) (flatDir j))) :=
    congrFun (fderiv_trainV_apply_eq_ring L hp (flatDir j)) p.2
  have hinr : ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) (flatDir j) = ((0 : ℝ), flatDir j) := by
    simp
  unfold flatD1
  rw [h, hinr, vecPairRing_apply]
  rfl

/-- Merid-level linearity of the embedding `merSp`. -/
theorem merSp_sub' (a b : Merid) : merSp (a - b) = merSp a - merSp b := by
  unfold merSp vecSp
  ext i
  fin_cases i <;> simp

theorem merSp_norm (m : Merid) : ‖merSp m‖ = ‖m‖ := by
  unfold merSp vecSp
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_three, Fin.sum_univ_two]

/-! ### Weight and bounds in dilation variables -/

/-- The weight sum at a dilation point `z`. -/
def ringS (L : ReturnLevel) (z : ℝ × (ℝ × ℝ)) : ℝ := ∑ j ∈ Finset.range 5, ringFj L z j

theorem ringFj_nonneg' (L : ReturnLevel) (z : ℝ × (ℝ × ℝ)) (j : ℕ) : 0 ≤ ringFj L z j := by
  unfold ringFj
  positivity

theorem ringS_nonneg (L : ReturnLevel) (z : ℝ × (ℝ × ℝ)) : 0 ≤ ringS L z :=
  Finset.sum_nonneg fun j _ => ringFj_nonneg' L z j

theorem ringFj_le_S (L : ReturnLevel) (z : ℝ × (ℝ × ℝ)) {j : ℕ} (hj : j < 5) :
    ringFj L z j ≤ ringS L z :=
  Finset.single_le_sum (f := ringFj L z) (fun k _ => ringFj_nonneg' L z k)
    (Finset.mem_range.2 hj)

theorem norm_fv_le_S (L : ReturnLevel) (z : ℝ × (ℝ × ℝ)) {j : ℕ} (hj : j < 5) :
    ‖iteratedFDeriv ℝ j (trainFv L) z‖ ≤ ringS L z := by
  have h := ringFj_le_S L z hj
  unfold ringFj at h
  have := norm_nonneg (iteratedFDeriv ℝ j (trainFp L) z)
  have := norm_nonneg (iteratedFDeriv ℝ j (trainFpsi L) z)
  linarith

theorem norm_fpsi_le_S (L : ReturnLevel) (z : ℝ × (ℝ × ℝ)) {j : ℕ} (hj : j < 5) :
    ‖iteratedFDeriv ℝ j (trainFpsi L) z‖ ≤ ringS L z := by
  have h := ringFj_le_S L z hj
  unfold ringFj at h
  have := norm_nonneg (iteratedFDeriv ℝ j (trainFp L) z)
  have := norm_nonneg (iteratedFDeriv ℝ j (trainFv L) z)
  linarith

theorem trainFv_val_le (L : ReturnLevel) (z : ℝ × (ℝ × ℝ)) : ‖trainFv L z‖ ≤ ringS L z := by
  have h := norm_fv_le_S L z (j := 0) (by norm_num)
  rwa [norm_iteratedFDeriv_zero] at h

theorem trainFv_deriv_le (L : ReturnLevel) (z : ℝ × (ℝ × ℝ)) {w : ℝ × (ℝ × ℝ)} (hw : ‖w‖ ≤ 1) :
    ‖fderiv ℝ (trainFv L) z w‖ ≤ ringS L z := by
  have h2 : ‖fderiv ℝ (trainFv L) z‖ ≤ ringS L z := by
    have h := norm_fv_le_S L z (j := 1) (by norm_num)
    rwa [norm_iteratedFDeriv_one] at h
  exact ((fderiv ℝ (trainFv L) z).le_opNorm w).trans
    ((mul_le_of_le_one_right (norm_nonneg _) hw).trans h2)

theorem fpsi_deriv_le (L : ReturnLevel) (z : ℝ × (ℝ × ℝ)) :
    ‖fderiv ℝ (trainFpsi L) z‖ ≤ ringS L z := by
  have h := norm_fpsi_le_S L z (j := 1) (by norm_num)
  rwa [norm_iteratedFDeriv_one] at h

theorem fpsi_deriv2_le (L : ReturnLevel) (z : ℝ × (ℝ × ℝ)) :
    ‖fderiv ℝ (fderiv ℝ (trainFpsi L)) z‖ ≤ ringS L z := by
  have e : ‖fderiv ℝ (fderiv ℝ (trainFpsi L)) z‖ = ‖iteratedFDeriv ℝ 2 (trainFpsi L) z‖ := by
    rw [← norm_iteratedFDeriv_one (fderiv ℝ (trainFpsi L)) (x := z)]
    rw [norm_iteratedFDeriv_fderiv (n := 1)]
  rw [e]
  exact norm_fpsi_le_S L z (j := 2) (by norm_num)

theorem abs_clm2_le (M : (ℝ × (ℝ × ℝ)) →L[ℝ] (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ) {w e : ℝ × (ℝ × ℝ)}
    (hw : ‖w‖ ≤ 1) (he : ‖e‖ ≤ 1) : |M w e| ≤ ‖M‖ := by
  rw [← Real.norm_eq_abs]
  have h := M.le_opNorm₂ w e
  have hM := norm_nonneg M
  have h1 : ‖M‖ * ‖w‖ ≤ ‖M‖ := mul_le_of_le_one_right hM hw
  have h2 : ‖M‖ * ‖w‖ * ‖e‖ ≤ ‖M‖ * ‖w‖ :=
    mul_le_of_le_one_right (mul_nonneg hM (norm_nonneg _)) he
  linarith

theorem rawH_deriv_le (L : ReturnLevel) (z : ℝ × (ℝ × ℝ)) {w : ℝ × (ℝ × ℝ)} (hw : ‖w‖ ≤ 1) :
    |fderiv ℝ (rawH L) z w| ≤ 4 * ringS L z + |z.2.2| * ringS L z := by
  obtain ⟨D, hD, hDw⟩ := rawH_hasFDerivAt L z
  rw [hD.fderiv, hDw]
  have hF1 := fpsi_deriv_le L z
  have hF2 := fpsi_deriv2_le L z
  have he1 : ‖((0 : ℝ), ((0 : ℝ), (1 : ℝ)))‖ ≤ 1 := by simp [Prod.norm_def]
  have he2 : ‖((1 : ℝ), ((0 : ℝ), (0 : ℝ)))‖ ≤ 1 := by simp [Prod.norm_def]
  have hw2 : |w.2.2| ≤ 1 := by
    have h1 : ‖w.2.2‖ ≤ ‖w.2‖ := norm_snd_le w.2
    have h2 : ‖w.2‖ ≤ ‖w‖ := norm_snd_le w
    rw [Real.norm_eq_abs] at h1
    linarith
  have t1 : |fderiv ℝ (trainFpsi L) z w| ≤ ringS L z :=
    (ringRaised_apply_le _ _ hw).trans hF1
  have t2 : |fderiv ℝ (trainFpsi L) z (0, (0, 1))| ≤ ringS L z :=
    (ringRaised_apply_le _ _ he1).trans hF1
  have t3 : |fderiv ℝ (fderiv ℝ (trainFpsi L)) z w (0, (0, 1))| ≤ ringS L z :=
    (abs_clm2_le _ hw he1).trans hF2
  have t4 : |fderiv ℝ (fderiv ℝ (trainFpsi L)) z w (1, (0, 0))| ≤ ringS L z :=
    (abs_clm2_le _ hw he2).trans hF2
  have hA2 : |w.2.2 * fderiv ℝ (trainFpsi L) z (0, (0, 1))| ≤ ringS L z := by
    rw [abs_mul]
    calc |w.2.2| * |fderiv ℝ (trainFpsi L) z (0, (0, 1))|
        ≤ 1 * ringS L z := mul_le_mul hw2 t2 (abs_nonneg _) zero_le_one
      _ = ringS L z := one_mul _
  have hA3 : |z.2.2 * fderiv ℝ (fderiv ℝ (trainFpsi L)) z w (0, (0, 1))|
      ≤ |z.2.2| * ringS L z := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left t3 (abs_nonneg _)
  have hA4 : |2 * fderiv ℝ (fderiv ℝ (trainFpsi L)) z w (1, (0, 0))| ≤ 2 * ringS L z := by
    rw [abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left t4 (by norm_num)
  have ha := abs_le.mp t1
  have hb := abs_le.mp hA2
  have hc := abs_le.mp hA3
  have hd := abs_le.mp hA4
  rw [abs_le]
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2, hc.1, hc.2, hd.1, hd.2]

theorem rawH_val_le (L : ReturnLevel) {p : Chart} (hp : 0 < p.1) :
    |rawH L (Real.log p.1, p.2)| ≤ 3 * ((1 + |p.2.2|) ^ 3 * ringS L (Real.log p.1, p.2)) := by
  have h := raisedStreamBound L (trainFpsi_contDiff L) p hp
  rw [rawH_eq_stream L hp]
  exact h

end UnforcedLeray.Short.PartIIIb.Concrete
