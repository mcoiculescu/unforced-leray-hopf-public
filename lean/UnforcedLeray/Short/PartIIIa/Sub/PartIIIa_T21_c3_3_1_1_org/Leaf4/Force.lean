import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf4.Frame

/-!
# Leaf (d) of `PartIII-a:T21/c3/3/1/1`, part 5: joint measurability of the mode forcings
and measurability of their norm profile (SP 2916-2925, 2991-2997)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIIa

namespace ComplFreeRateSub

namespace Leaf4Aux

section

variable {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) {ν t₁ t₂ : ℝ} (hν : 0 < ν)
  (ht : 0 ≤ t₁) (hts : t₁ ≤ t₂)
  (hd1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))

include hκ hν ht hts hd1 in
lemma measurable_kerVel_joint (j : Fin 2) (k : Fin 2) :
    Measurable (fun p : ℝ × (ℝ × ℝ) =>
      kerVelCx (dRho ν t₁ t₂ p.1) (perE κ (dRho ν t₁ t₂ p.1) j) p.2 k) := by
  have hD : Measurable (fun a : ℝ × (ℝ × ℝ) => dRho ν t₁ t₂ a.1) :=
    ((continuous_dRho hν ht).comp continuous_fst).measurable
  have hE := measurable_perE_joint hκ hν ht hts hd1 j
  have hK := measurable_kerD_joint k
  have hm0 : Measurable (fun q : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) => (q.1.1, q.2)) := by fun_prop
  have hm1 : Measurable (fun q : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) =>
      (dRho ν t₁ t₂ q.1.1, q.1.2 - q.2)) := by
    have h1 : Measurable (fun q : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) => dRho ν t₁ t₂ q.1.1) :=
      hD.comp measurable_fst
    have h2 : Measurable (fun q : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) => q.1.2 - q.2) := by fun_prop
    exact h1.prodMk h2
  have hH : Measurable (fun q : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) =>
      perE κ (dRho ν t₁ t₂ q.1.1) j q.2 *
        ((kerD (dRho ν t₁ t₂ q.1.1) (q.1.2 - q.2) k : ℝ) : ℂ)) := by
    have h3 : Measurable (fun q : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) =>
        kerD (dRho ν t₁ t₂ q.1.1) (q.1.2 - q.2) k) := by
      have := hK.comp hm1
      exact this
    have h4 : Measurable (fun q : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) =>
        perE κ (dRho ν t₁ t₂ q.1.1) j q.2) := by
      have := hE.comp hm0
      exact this
    exact h4.mul (Complex.measurable_ofReal.comp h3)
  exact measurable_setIntegral_cell _ hD _ hH

include hκ hν ht hts hd1 in
lemma measurable_movOscRes_joint (j : Fin 2) :
    Measurable (fun p : ℝ × (ℝ × ℝ) => movOscRes κ ν (rho t₁ t₂ p.1) j p.2) := by
  obtain ⟨hcont, C, hC0, hC⟩ := OscillatorForceSub.movD_seed_decay hκ j
  have hps := measurable_perSum_joint hcont (C := 16 * C) (by positivity)
    (fun z => (hC z).trans (by
      have := FrameCont.exp_le_translate_weight z.1 z.2
      calc C * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)
          ≤ C * (16 * (1 + |z.1|) ^ (-(2 : ℝ))) := mul_le_mul_of_nonneg_left this hC0
        _ = (16 * C) * (1 + |z.1|) ^ (-(2 : ℝ)) := by ring)) hν ht hts hd1
  have hθ : Measurable (fun p : ℝ × (ℝ × ℝ) => ((clockTheta ν (rho t₁ t₂ p.1) : ℝ) : ℂ)⁻¹) := by
    have hA : Continuous (fun r : ℝ => clockA ν (rho t₁ t₂ r)) := by
      unfold clockA; have := continuous_rho t₁ t₂; fun_prop
    have : Measurable (fun p : ℝ × (ℝ × ℝ) => clockTheta ν (rho t₁ t₂ p.1)) := by
      unfold clockTheta
      exact ((measurable_const.mul (hA.comp continuous_fst).measurable)).inv
    exact (Complex.measurable_ofReal.comp this).inv
  have heq : (fun p : ℝ × (ℝ × ℝ) => movOscRes κ ν (rho t₁ t₂ p.1) j p.2) =
      fun p => ((clockTheta ν (rho t₁ t₂ p.1) : ℝ) : ℂ)⁻¹ *
        perSum (dRho ν t₁ t₂ p.1) (movD (κ.e j)) p.2 := by
    funext p
    exact OscillatorForceSub.movOscRes_eq_perSum_movD hκ hν (ht.trans (le_max_left _ _)) j p.2
  rw [heq]
  exact hθ.mul hps

include hκ hν ht hts hd1 in
lemma measurable_movEulerRes_joint (P : PlanarData)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (j : Fin 2) :
    Measurable (fun p : ℝ × (ℝ × ℝ) => movEulerRes κ P tr (rho t₁ t₂ p.1) j p.2) := by
  have hE := measurable_perE_joint hκ hν ht hts hd1 j
  have hp0 := measurable_pdCx_perE_joint hκ hν ht hts hd1 j 0
  have hp1 := measurable_pdCx_perE_joint hκ hν ht hts hd1 j 1
  have hk0 := measurable_kerVel_joint hκ hν ht hts hd1 j 0
  have hk1 := measurable_kerVel_joint hκ hν ht hts hd1 j 1
  have hV0 := Complex.measurable_ofReal.comp (measurable_movingTrainV (t₂ := t₂) tr ht 0)
  have hV1 := Complex.measurable_ofReal.comp (measurable_movingTrainV (t₂ := t₂) tr ht 1)
  have hG0 := Complex.measurable_ofReal.comp (measurable_movingTrainGradE (t₂ := t₂) tr ht 0)
  have hG1 := Complex.measurable_ofReal.comp (measurable_movingTrainGradE (t₂ := t₂) tr ht 1)
  unfold movEulerRes movL
  exact (((hV0.mul hp0).add (hV1.mul hp1)).neg.sub ((hk0.mul hG0).add (hk1.mul hG1))).sub
    (measurable_const.mul hE)

include hκ hν ht hts hd1 in
lemma measurable_force_joint {m b K : ℝ} (P : PlanarData)
    (hF : PerFrameFacts κ ν m b K)
    (hdet : ∀ r ∈ Icc t₁ t₂, (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))).det ≠ 0)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (j : Fin 2) :
    Measurable (fun p : ℝ × (ℝ × ℝ) =>
      complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr (rho t₁ t₂ p.1) j p.2) := by
  have hΨ : Measurable (fun p : ℝ × (ℝ × ℝ) =>
      movOscRes κ ν (rho t₁ t₂ p.1) j p.2 + movEulerRes κ P tr (rho t₁ t₂ p.1) j p.2) :=
    (measurable_movOscRes_joint hκ hν ht hts hd1 j).add
      (measurable_movEulerRes_joint hκ hν ht hts hd1 P tr j)
  have hD : Measurable (dRho ν t₁ t₂) := (continuous_dRho hν ht).measurable
  have hcoef : ∀ i : Fin 2, Measurable (fun r : ℝ =>
      ∫ x in movingCell ν (ν ^ (-2 : ℝ)) (rho t₁ t₂ r),
        (periodizedFrame κ ν m b K hν hF).lam (rho t₁ t₂ r) i x *
          (movOscRes κ ν (rho t₁ t₂ r) j x + movEulerRes κ P tr (rho t₁ t₂ r) j x)) := by
    intro i
    have hH : Measurable (fun q : ℝ × (ℝ × ℝ) =>
        perLam κ (dRho ν t₁ t₂ q.1) i q.2 *
          (movOscRes κ ν (rho t₁ t₂ q.1) j q.2 + movEulerRes κ P tr (rho t₁ t₂ q.1) j q.2)) :=
      (measurable_perLam_joint hν ht hts hd1 hdet i).mul hΨ
    exact measurable_setIntegral_cell (dRho ν t₁ t₂) hD _ hH
  unfold complModeForce frameProj
  refine hΨ.sub (Finset.measurable_sum _ (fun i _ => ?_))
  have hEi := measurable_perE_joint hκ hν ht hts hd1 i
  exact ((hcoef i).comp measurable_fst).mul hEi

/-- Measurability of the norm profile of a jointly measurable family on the moving cells. -/
lemma measurable_xNorm_family {t₁ t₂ ν : ℝ} (hν : 0 < ν) (ht : 0 ≤ t₁) (m : ℝ)
    (f : ℝ → ℝ × ℝ → ℂ) (hf : Measurable (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2)) :
    Measurable (fun r : ℝ => xNorm (dRho ν t₁ t₂ r) m (f r)) := by
  have hD : Measurable (dRho ν t₁ t₂) := (continuous_dRho hν ht).measurable
  have hset : MeasurableSet {q : ℝ × (ℝ × ℝ) | q.2 ∈ B0579.cell (dRho ν t₁ t₂ q.1)} := by
    have : {q : ℝ × (ℝ × ℝ) | q.2 ∈ B0579.cell (dRho ν t₁ t₂ q.1)} =
        {q | -(dRho ν t₁ t₂ q.1 / 2) ≤ q.2.1} ∩ {q | q.2.1 < dRho ν t₁ t₂ q.1 / 2} := by
      ext q; simp [B0579.cell, Set.mem_prod]
    rw [this]
    have hD1 : Measurable (fun q : ℝ × (ℝ × ℝ) => dRho ν t₁ t₂ q.1) := hD.comp measurable_fst
    exact (measurableSet_le (by fun_prop) (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) (by fun_prop))
  have hG : Measurable (fun q : ℝ × (ℝ × ℝ) =>
      {q : ℝ × (ℝ × ℝ) | q.2 ∈ B0579.cell (dRho ν t₁ t₂ q.1)}.indicator
        (fun q => ((B0579.density m q.2 : ℝ≥0) : ℝ≥0∞) * ‖f q.1 q.2‖ₑ ^ 2) q) := by
    refine Measurable.indicator ?_ hset
    exact (((B0579.measurable_density m).coe_nnreal_ennreal).comp measurable_snd).mul
      (hf.enorm.pow_const 2)
  have hL := hG.lintegral_prod_right' (ν := (volume : Measure (ℝ × ℝ)))
  have heq : (fun r : ℝ => xNorm (dRho ν t₁ t₂ r) m (f r)) = fun r =>
      (∫⁻ x, {q : ℝ × (ℝ × ℝ) | q.2 ∈ B0579.cell (dRho ν t₁ t₂ q.1)}.indicator
        (fun q => ((B0579.density m q.2 : ℝ≥0) : ℝ≥0∞) * ‖f q.1 q.2‖ₑ ^ 2) (r, x)) ^ (1 / 2 : ℝ) := by
    funext r
    unfold xNorm
    rw [T07.eLpNorm_two_eq_lintegral, T07.lintegral_cellMeasure_eq]
    congr 2
  rw [heq]
  exact hL.pow_const _

end

end Leaf4Aux

end ComplFreeRateSub

end UnforcedLeray.Short.IIIa
