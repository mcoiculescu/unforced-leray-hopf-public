import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org_1_a.JointMeas

/-!
# Helper for `PartIII-a:T21/c3/2/1/1/org/1/a`: joint measurability of `movDampedComplInt`

Assembly of the joint measurability in `(r, y)` of the damped complement interaction
`movDampedComplInt κ P tr (rho t₁ t₂ r) W y` (SP 2920-2925, 2974-2978) from its ingredients, and of
its cell zero-extension.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit.RelIntA

open UnforcedLeray.Short.IIIa.CompactDuhamelGapSub UnforcedLeray.Short.IIIa.ComplCouplingSub
  UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf4Aux

theorem measurable_movH0_rho {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {ν t₁ t₂ : ℝ} (hν : 0 < ν) (ht : 0 ≤ t₁) (hts : t₁ ≤ t₂)
    (hd1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (hdet : ∀ r ∈ Icc t₁ t₂, (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))).det ≠ 0)
    (hform : ∀ r ∈ Icc t₁ t₂, HeatFormula κ ν r)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) {W : ℝ × ℝ → ℂ} (hW : Measurable W)
    (i : Fin 2) :
    Measurable (fun r : ℝ => movH0 κ tr (rho t₁ t₂ r) i W) := by
  have heq : (fun r : ℝ => movH0 κ tr (rho t₁ t₂ r) i W) = fun r =>
      ∫ y in B0579.cell (dRho ν t₁ t₂ r), movLamDual κ tr (rho t₁ t₂ r) i y * W y := by
    funext r
    exact movH0_eq_integral_movLamDual κ tr _ i W
  rw [heq]
  have hH : Measurable (fun q : ℝ × (ℝ × ℝ) => movLamDual κ tr (rho t₁ t₂ q.1) i q.2 * W q.2) :=
    (measurable_movLamDual_joint hκ hν ht hts hd1 hdet hform tr i).mul (hW.comp measurable_snd)
  exact measurable_setIntegral_cell (dRho ν t₁ t₂) (continuous_dRho hν ht).measurable
    (fun q : ℝ × (ℝ × ℝ) => movLamDual κ tr (rho t₁ t₂ q.1) i q.2 * W q.2) hH

theorem measurable_movLamPair_rho {κ : PlanarFrameKernels}
    {ν t₁ t₂ : ℝ} (hν : 0 < ν) (ht : 0 ≤ t₁) (hts : t₁ ≤ t₂)
    (hd1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (hdet : ∀ r ∈ Icc t₁ t₂, (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))).det ≠ 0)
    {W : ℝ × ℝ → ℂ} (hW : Measurable W) (j : Fin 2) :
    Measurable (fun r : ℝ => movLamPair κ ν (rho t₁ t₂ r) j W) := by
  have hH : Measurable (fun q : ℝ × (ℝ × ℝ) => perLam κ (dRho ν t₁ t₂ q.1) j q.2 * W q.2) :=
    (measurable_perLam_joint hν ht hts hd1 hdet j).mul (hW.comp measurable_snd)
  exact measurable_setIntegral_cell (dRho ν t₁ t₂) (continuous_dRho hν ht).measurable
    (fun q : ℝ × (ℝ × ℝ) => perLam κ (dRho ν t₁ t₂ q.1) j q.2 * W q.2) hH

theorem measurable_movK0_joint {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) (P : PlanarData)
    {ν t₁ t₂ : ℝ} (hν : 0 < ν) (ht : 0 ≤ t₁) (hts : t₁ ≤ t₂)
    (hd1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (j : Fin 2) :
    Measurable (fun p : ℝ × (ℝ × ℝ) => movK0 κ P tr (rho t₁ t₂ p.1) j p.2) := by
  have h1 := measurable_movOscRes_joint hκ hν ht hts hd1 j
  have h2 := measurable_movEulerRes_joint hκ hν ht hts hd1 P tr j
  have h3 := measurable_perE_joint hκ hν ht hts hd1 j
  exact (h1.add h2).add (measurable_const.mul h3)

theorem measurable_movM0_rho {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) (P : PlanarData)
    {ν t₁ t₂ : ℝ} (hν : 0 < ν) (ht : 0 ≤ t₁) (hts : t₁ ≤ t₂)
    (hd1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (hdet : ∀ r ∈ Icc t₁ t₂, (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))).det ≠ 0)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (i j : Fin 2) :
    Measurable (fun r : ℝ => movM0 κ P tr (rho t₁ t₂ r) i j) := by
  have hH : Measurable (fun q : ℝ × (ℝ × ℝ) =>
      perLam κ (dRho ν t₁ t₂ q.1) i q.2 * movK0 κ P tr (rho t₁ t₂ q.1) j q.2) :=
    (measurable_perLam_joint hν ht hts hd1 hdet i).mul
      (measurable_movK0_joint hκ P hν ht hts hd1 tr j)
  exact measurable_setIntegral_cell (dRho ν t₁ t₂) (continuous_dRho hν ht).measurable
    (fun q : ℝ × (ℝ × ℝ) =>
      perLam κ (dRho ν t₁ t₂ q.1) i q.2 * movK0 κ P tr (rho t₁ t₂ q.1) j q.2) hH

theorem measurable_movBeta0_rho (P : PlanarData) (ν t₁ t₂ : ℝ) :
    Measurable (fun r : ℝ => movBeta0 P ν (rho t₁ t₂ r)) := by
  have hr : Measurable (rho t₁ t₂) := (continuous_rho t₁ t₂).measurable
  have hθ : Measurable (fun r : ℝ => clockTheta ν (rho t₁ t₂ r)) := by
    unfold clockTheta clockA
    exact (measurable_const.mul (measurable_const.add (measurable_const.mul hr))).inv
  unfold movBeta0
  exact measurable_const.add (measurable_const.div hθ)

theorem measurable_movDampedComplInt_joint {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    (P : PlanarData) {ν t₁ t₂ : ℝ} (hν : 0 < ν) (ht : 0 ≤ t₁) (hts : t₁ ≤ t₂)
    (hd1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (hdet : ∀ r ∈ Icc t₁ t₂, (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))).det ≠ 0)
    (hform : ∀ r ∈ Icc t₁ t₂, HeatFormula κ ν r)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) {W : ℝ × ℝ → ℂ} (hW : Measurable W) :
    Measurable (fun p : ℝ × (ℝ × ℝ) => movDampedComplInt κ P tr (rho t₁ t₂ p.1) W p.2) := by
  have hL := measurable_movLInt_joint (t₂ := t₂) hν ht tr hW
  have hE : ∀ i, Measurable (fun p : ℝ × (ℝ × ℝ) => perE κ (dRho ν t₁ t₂ p.1) i p.2) :=
    fun i => measurable_perE_joint hκ hν ht hts hd1 i
  have hHE : Measurable (fun p : ℝ × (ℝ × ℝ) =>
      ∑ i : Fin 2, movH0 κ tr (rho t₁ t₂ p.1) i W * perE κ (dRho ν t₁ t₂ p.1) i p.2) :=
    Finset.measurable_sum _ fun i _ =>
      ((measurable_movH0_rho hκ hν ht hts hd1 hdet hform tr hW i).comp measurable_fst).mul (hE i)
  have hb : Measurable (fun p : ℝ × (ℝ × ℝ) =>
      (((movBeta0 P ν (rho t₁ t₂ p.1) - 1 : ℝ)) : ℂ)) :=
    Complex.measurable_ofReal.comp
      (((measurable_movBeta0_rho P ν t₁ t₂).sub measurable_const).comp measurable_fst)
  have hΨ : ∀ j : Fin 2, Measurable (fun p : ℝ × (ℝ × ℝ) =>
      -movK0 κ P tr (rho t₁ t₂ p.1) j p.2 +
        (((movBeta0 P ν (rho t₁ t₂ p.1) - 1 : ℝ)) : ℂ) * perE κ (dRho ν t₁ t₂ p.1) j p.2 +
        ∑ i : Fin 2, movM0 κ P tr (rho t₁ t₂ p.1) i j * perE κ (dRho ν t₁ t₂ p.1) i p.2) := by
    intro j
    have hM : Measurable (fun p : ℝ × (ℝ × ℝ) =>
        ∑ i : Fin 2, movM0 κ P tr (rho t₁ t₂ p.1) i j * perE κ (dRho ν t₁ t₂ p.1) i p.2) :=
      Finset.measurable_sum _ fun i _ =>
        ((measurable_movM0_rho hκ P hν ht hts hd1 hdet tr i j).comp measurable_fst).mul (hE i)
    exact (((measurable_movK0_joint hκ P hν ht hts hd1 tr j).neg).add (hb.mul (hE j))).add hM
  have hΛ : ∀ j : Fin 2, Measurable (fun p : ℝ × (ℝ × ℝ) => movLamPair κ ν (rho t₁ t₂ p.1) j W) :=
    fun j => (measurable_movLamPair_rho hν ht hts hd1 hdet hW j).comp measurable_fst
  have hR : Measurable (fun p : ℝ × (ℝ × ℝ) =>
      (-∑ i : Fin 2, movH0 κ tr (rho t₁ t₂ p.1) i W * perE κ (dRho ν t₁ t₂ p.1) i p.2) +
        ∑ j : Fin 2, (-movK0 κ P tr (rho t₁ t₂ p.1) j p.2 +
          (((movBeta0 P ν (rho t₁ t₂ p.1) - 1 : ℝ)) : ℂ) * perE κ (dRho ν t₁ t₂ p.1) j p.2 +
          ∑ i : Fin 2, movM0 κ P tr (rho t₁ t₂ p.1) i j * perE κ (dRho ν t₁ t₂ p.1) i p.2) *
            movLamPair κ ν (rho t₁ t₂ p.1) j W) :=
    hHE.neg.add (Finset.measurable_sum _ fun j _ => (hΨ j).mul (hΛ j))
  exact hL.add hR

/-- Joint measurability of a cell zero-extension with a parameter-dependent cell. -/
theorem measurable_cellZeroExt_joint {α : Type*} [MeasurableSpace α] (D : α → ℝ)
    (hD : Measurable D) (V : α → ℝ × ℝ → ℂ)
    (hV : Measurable (fun q : α × (ℝ × ℝ) => V q.1 q.2)) :
    Measurable (fun q : α × (ℝ × ℝ) => cellZeroExt (D q.1) (V q.1) q.2) := by
  have hset : MeasurableSet {q : α × (ℝ × ℝ) | q.2 ∈ B0579.cell (D q.1)} := by
    have : {q : α × (ℝ × ℝ) | q.2 ∈ B0579.cell (D q.1)} =
        {q | -(D q.1 / 2) ≤ q.2.1} ∩ {q | q.2.1 < D q.1 / 2} := by
      ext q; simp [B0579.cell, Set.mem_prod]
    rw [this]
    exact (measurableSet_le (by fun_prop) (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) (by fun_prop))
  have heq : (fun q : α × (ℝ × ℝ) => cellZeroExt (D q.1) (V q.1) q.2) =
      {q : α × (ℝ × ℝ) | q.2 ∈ B0579.cell (D q.1)}.indicator (fun q => V q.1 q.2) := by
    funext q
    by_cases h : q.2 ∈ B0579.cell (D q.1)
    · rw [Set.indicator_of_mem (show q ∈ {q : α × (ℝ × ℝ) | q.2 ∈ B0579.cell (D q.1)} from h)]
      exact Set.indicator_of_mem h _
    · rw [Set.indicator_of_notMem (show q ∉ {q : α × (ℝ × ℝ) | q.2 ∈ B0579.cell (D q.1)} from h)]
      exact Set.indicator_of_notMem h _
  rw [heq]
  exact hV.indicator hset

end UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit.RelIntA
