import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Equation.A_Diff
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.HigherReg.Scale

/-!
# `PartIII-a:T21/2/2/3/2/2`: `MvChiC1` (leaf B of `movAdjEquation_of`)

`mvChi = adjGen β V Φ - ∂_ζΦ` is `C¹` in `y`. The first term is smooth in `y` (the moving adjoint
`movingPhi ν φ r` is `C^∞`, the moving velocity `movingTrainV` is `C^∞` on `r > 0`). The second term
is `y ↦ fderiv (ζ', y ↦ mvPhi ζ' y) (ζ, y) (1, 0)`, which is `C^∞` because the joint map
`(ζ', y) ↦ mvPhi ζ' y` is `C^∞` near every `(ζ, y)` (chain rule through `revAge`, `√a`, `φ`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

theorem contDiffAt_revAge_B (ν s ζ : ℝ) (hd : 0 < 1 - ν * (movingZ ν s - ζ)) :
    ContDiffAt ℝ ∞ (fun ζ' => revAge ν s ζ') ζ := by
  have hc : ContDiffAt ℝ ∞ (fun ζ' : ℝ => movingZ ν s - ζ') ζ := by fun_prop
  have hd' : ContDiffAt ℝ ∞ (fun ζ' : ℝ => 1 - ν * (movingZ ν s - ζ')) ζ := by fun_prop
  have e : (fun ζ' => revAge ν s ζ') =
      fun ζ' => (movingZ ν s - ζ') / (1 - ν * (movingZ ν s - ζ')) := rfl
  rw [e]
  exact hc.div hd' hd.ne'

/-- The joint smoothness of `(ζ', y) ↦ mvPhi ν φ s ζ' y` at `(ζ, y0)`. -/
theorem contDiffAt_mvPhi_joint_B {t s ν ζ : ℝ} {φ : ℝ → ℝ × ℝ → ℂ} (hν : 0 < ν) (ht0 : 0 ≤ t)
    (hts : t < s) (hζ : ζ ∈ Ioo 0 (deltaZ ν t s))
    (hJ : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ)) (y0 : ℝ × ℝ) :
    ContDiffAt ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => mvPhi ν φ s p.1 p.2) (ζ, y0) := by
  have hr : revAge ν s ζ ∈ Ioo t s := revAge_mem_Ioo_A hν ht0 hts hζ
  have hζ0 : 0 < ζ := hζ.1
  have hd : 0 < 1 - ν * (movingZ ν s - ζ) :=
    revAge_denom_pos_A hν hζ0 (movingZ_mul_lt_one_A hν (ht0.trans hts.le))
  have hR : ContDiffAt ℝ ∞ (fun ζ' => revAge ν s ζ') ζ := contDiffAt_revAge_B ν s ζ hd
  have hA : ContDiffAt ℝ ∞ (fun ζ' => clockA ν (revAge ν s ζ')) ζ := by
    unfold clockA
    exact contDiffAt_const.add (contDiffAt_const.mul hR)
  have hApos : 0 < clockA ν (revAge ν s ζ) := by
    have h0 : 0 ≤ ν * revAge ν s ζ := mul_nonneg hν.le (by linarith [hr.1, ht0])
    unfold clockA
    linarith
  have hS : ContDiffAt ℝ ∞ (fun ζ' => Real.sqrt (clockA ν (revAge ν s ζ'))) ζ :=
    hA.sqrt hApos.ne'
  have hI : ContDiffAt ℝ ∞ (fun ζ' => (clockA ν (revAge ν s ζ'))⁻¹) ζ := hA.inv hApos.ne'
  have hR' : ContDiffAt ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => revAge ν s p.1) (ζ, y0) :=
    ContDiffAt.comp (f := fun p : ℝ × (ℝ × ℝ) => p.1) (g := fun ζ' : ℝ => revAge ν s ζ')
      (ζ, y0) hR contDiffAt_fst
  have hS' : ContDiffAt ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => Real.sqrt (clockA ν (revAge ν s p.1)))
      (ζ, y0) :=
    ContDiffAt.comp (f := fun p : ℝ × (ℝ × ℝ) => p.1)
      (g := fun ζ' : ℝ => Real.sqrt (clockA ν (revAge ν s ζ'))) (ζ, y0) hS contDiffAt_fst
  have hy1 : ContDiffAt ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => p.2.1) (ζ, y0) :=
    (contDiff_fst.comp contDiff_snd).contDiffAt
  have hy2 : ContDiffAt ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => p.2.2) (ζ, y0) :=
    (contDiff_snd.comp contDiff_snd).contDiffAt
  have hQ : ContDiffAt ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (revAge ν s p.1,
      (Real.sqrt (clockA ν (revAge ν s p.1)) * p.2.1, Real.sqrt (clockA ν (revAge ν s p.1)) * p.2.2)))
      (ζ, y0) :=
    hR'.prodMk ((hS'.mul hy1).prodMk (hS'.mul hy2))
  have hP : ContDiffAt ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => φ q.1 q.2) (revAge ν s ζ,
      (Real.sqrt (clockA ν (revAge ν s ζ)) * y0.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y0.2)) :=
    joint_contDiffAt_A hJ hr _
  have hPQ := hP.comp (ζ, y0) hQ
  have hI' : ContDiffAt ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (clockA ν (revAge ν s p.1))⁻¹) (ζ, y0) :=
    ContDiffAt.comp (f := fun p : ℝ × (ℝ × ℝ) => p.1)
      (g := fun ζ' : ℝ => (clockA ν (revAge ν s ζ'))⁻¹) (ζ, y0) hI contDiffAt_fst
  have hCf : ContDiffAt ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (((clockA ν (revAge ν s p.1))⁻¹ : ℝ) : ℂ))
      (ζ, y0) :=
    ContDiffAt.comp (f := fun p : ℝ × (ℝ × ℝ) => (clockA ν (revAge ν s p.1))⁻¹)
      (g := fun t : ℝ => (t : ℂ)) (ζ, y0) Complex.ofRealCLM.contDiff.contDiffAt hI'
  exact hCf.mul hPQ

theorem deriv_mvPhi_eq_B {t s ν ζ : ℝ} {φ : ℝ → ℝ × ℝ → ℂ} (hν : 0 < ν) (ht0 : 0 ≤ t)
    (hts : t < s) (hζ : ζ ∈ Ioo 0 (deltaZ ν t s))
    (hJ : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ)) (y : ℝ × ℝ) :
    deriv (fun ζ' => mvPhi ν φ s ζ' y) ζ =
      fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => mvPhi ν φ s p.1 p.2) (ζ, y) (1, 0) := by
  have hH := ((contDiffAt_mvPhi_joint_B hν ht0 hts hζ hJ y).differentiableAt (by simp))
  have hl : HasDerivAt (fun ζ' : ℝ => (ζ', y)) ((1 : ℝ), (0 : ℝ × ℝ)) ζ :=
    (hasDerivAt_id' ζ).prodMk (hasDerivAt_const ζ y)
  exact (hH.hasFDerivAt.comp_hasDerivAt ζ hl).deriv

theorem contDiff_slice_deriv_B {t s ν ζ : ℝ} {φ : ℝ → ℝ × ℝ → ℂ} (hν : 0 < ν) (ht0 : 0 ≤ t)
    (hts : t < s) (hζ : ζ ∈ Ioo 0 (deltaZ ν t s))
    (hJ : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ)) :
    ContDiff ℝ ∞ (fun y : ℝ × ℝ =>
      fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => mvPhi ν φ s p.1 p.2) (ζ, y) (1, 0)) := by
  rw [contDiff_iff_contDiffAt]
  intro y0
  have hHd : ContDiffAt ℝ ∞ (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => mvPhi ν φ s p.1 p.2)) (ζ, y0) :=
    (contDiffAt_mvPhi_joint_B hν ht0 hts hζ hJ y0).fderiv_right (by simp)
  have hc : ContDiffAt ℝ ∞ (fun y : ℝ × ℝ => (ζ, y)) y0 := contDiffAt_const.prodMk contDiffAt_id
  exact (hHd.comp y0 hc).clm_apply contDiffAt_const

/-- Joint smoothness of the train velocity along `r > 0`. -/
theorem contDiffAt_trainV_B {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 < r)
    (z : ℝ × ℝ) :
    ContDiffAt ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) (r, z) := by
  have hmem : (r, z) ∈ Ioi 0 ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hr, mem_univ z⟩
  have hopen : Ioi 0 ×ˢ (univ : Set (ℝ × ℝ)) ∈ 𝓝 (r, z) :=
    IsOpen.mem_nhds (isOpen_Ioi.prod isOpen_univ) hmem
  exact tr.isTrain.smooth_v.contDiffAt (Filter.mem_of_superset hopen
    (Set.prod_mono (Set.Ioi_subset_Ici le_rfl) (Set.Subset.refl _)))

theorem mvChiC1 (m : ℝ) : UnforcedLeray.Short.IIIa.AdjE1.MvChiC1 m := by
  intro ν tr t s φ ζ hflow
  obtain ⟨hν, ht0, hts, ⟨G, _, hF⟩, hζ⟩ := hflow
  have hr : revAge ν s ζ ∈ Ioo t s := revAge_mem_Ioo_A hν ht0 hts hζ
  have hrI : revAge ν s ζ ∈ Ico t s := Ioo_subset_Ico_self hr
  have hrpos : 0 < revAge ν s ζ := lt_of_le_of_lt ht0 hr.1
  have hJ : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ) := hF.jointSmooth
  -- smoothness of the moving adjoint in `y`
  have hΦ : ContDiff ℝ ∞ (mvPhi ν φ s ζ) := by
    show ContDiff ℝ ∞ (movingPhi ν φ (revAge ν s ζ))
    rw [movingPhi_eq_comp]
    exact contDiff_const.mul ((hF.smooth _ hrI).comp (contDiff_const_smul _))
  have hL0 : ContDiff ℝ ∞ (pdCx 0 (mvPhi ν φ s ζ)) := contDiff_pdCx 0 hΦ
  have hL1 : ContDiff ℝ ∞ (pdCx 1 (mvPhi ν φ s ζ)) := contDiff_pdCx 1 hΦ
  have hL00 : ContDiff ℝ ∞ (pdCx 0 (pdCx 0 (mvPhi ν φ s ζ))) := contDiff_pdCx 0 hL0
  have hL11 : ContDiff ℝ ∞ (pdCx 1 (pdCx 1 (mvPhi ν φ s ζ))) := contDiff_pdCx 1 hL1
  -- smoothness of the rescaled train velocity in `y`
  have hQy : ContDiff ℝ ∞ (fun y : ℝ × ℝ =>
      (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)) :=
    (contDiff_const.mul contDiff_fst).prodMk (contDiff_const.mul contDiff_snd)
  have hVv : ContDiff ℝ ∞ (fun y : ℝ × ℝ => tr.v (revAge ν s ζ)
      (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)) := by
    rw [contDiff_iff_contDiffAt]
    intro y0
    have hjoint := contDiffAt_trainV_B tr hrpos (Real.sqrt (clockA ν (revAge ν s ζ)) * y0.1,
      Real.sqrt (clockA ν (revAge ν s ζ)) * y0.2)
    have hpair : ContDiffAt ℝ ∞ (fun y : ℝ × ℝ => (revAge ν s ζ,
        (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)))
        y0 :=
      contDiffAt_const.prodMk hQy.contDiffAt
    exact ContDiffAt.comp (f := fun y : ℝ × ℝ => (revAge ν s ζ,
        (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)))
      (g := fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) y0 hjoint hpair
  have hV0 : ContDiff ℝ ∞ (fun y : ℝ × ℝ => movingTrainV tr (revAge ν s ζ) y 0) := by
    have hproj := (EuclideanSpace.proj (0 : Fin 2)).contDiff.comp hVv
    exact contDiff_const.mul hproj
  have hV1 : ContDiff ℝ ∞ (fun y : ℝ × ℝ => movingTrainV tr (revAge ν s ζ) y 1) := by
    have hproj := (EuclideanSpace.proj (1 : Fin 2)).contDiff.comp hVv
    exact contDiff_const.mul hproj
  have hofR : ContDiff ℝ ∞ (Complex.ofReal) := Complex.ofRealCLM.contDiff
  have hadj : ContDiff ℝ ∞ (fun y : ℝ × ℝ => adjGen (mvBeta ν s ζ)
      (movingTrainV tr (revAge ν s ζ)) (mvPhi ν φ s ζ) y) := by
    unfold adjGen lapC radC transC
    fun_prop
  have hadj1 : ContDiff ℝ 1 (fun y : ℝ × ℝ => adjGen (mvBeta ν s ζ)
      (movingTrainV tr (revAge ν s ζ)) (mvPhi ν φ s ζ) y) := hadj.of_le (by simp)
  have hder : ContDiff ℝ 1 (fun y : ℝ × ℝ => deriv (fun ζ' => mvPhi ν φ s ζ' y) ζ) := by
    have e : (fun y : ℝ × ℝ => deriv (fun ζ' => mvPhi ν φ s ζ' y) ζ) =
        fun y : ℝ × ℝ => fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => mvPhi ν φ s p.1 p.2) (ζ, y) (1, 0) :=
      funext fun y => deriv_mvPhi_eq_B hν ht0 hts hζ hJ y
    rw [e]
    exact (contDiff_slice_deriv_B hν ht0 hts hζ hJ).of_le (by simp)
  exact hadj1.sub hder

end UnforcedLeray.Short.IIIa.AdjE1
