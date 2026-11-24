import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf4.Train
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf4.Ampl

/-!
# Leaf (d) of `PartIII-a:T21/c3/3/1/1`, part 4: joint measurability of the frame and the kernel
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIIa

namespace ComplFreeRateSub

namespace Leaf4Aux

/-- Joint measurability of the cylinder Biot-Savart kernel in its period. -/
lemma measurable_kerD_joint (k : Fin 2) :
    Measurable (fun q : ℝ × (ℝ × ℝ) => kerD q.1 q.2 k) := by
  have hcot : Measurable Complex.cot := by
    have e : Complex.cot = fun z => Complex.cos z / Complex.sin z :=
      funext Complex.cot_eq_cos_div_sin
    rw [e]
    exact Complex.measurable_cos.div Complex.measurable_sin
  have h1 : Measurable (fun q : ℝ × (ℝ × ℝ) => UnforcedLeray.Cyl.bsC q.1 q.2) := by
    unfold UnforcedLeray.Cyl.bsC UnforcedLeray.Kernels.cylinderBS
    refine measurable_const.mul (Measurable.mul ?_ (hcot.comp ?_))
    · exact measurable_const.div (Complex.measurable_ofReal.comp measurable_fst)
    · fun_prop
  unfold kerD UnforcedLeray.Cyl.bsKernel
  fin_cases k
  · simp only [Fin.zero_eta]
    exact Complex.measurable_re.comp h1
  · simp only [Fin.mk_one]
    simpa [Function.comp_def] using (Complex.measurable_im.comp h1)

/-- Parametric cell integrals are measurable. -/
lemma measurable_setIntegral_cell {α : Type*} [MeasurableSpace α] (D : α → ℝ) (hD : Measurable D)
    (H : α × (ℝ × ℝ) → ℂ) (hH : Measurable H) :
    Measurable (fun a => ∫ z in B0579.cell (D a), H (a, z)) := by
  have hset : MeasurableSet {q : α × (ℝ × ℝ) | q.2 ∈ B0579.cell (D q.1)} := by
    have : {q : α × (ℝ × ℝ) | q.2 ∈ B0579.cell (D q.1)} =
        {q | -(D q.1 / 2) ≤ q.2.1} ∩ {q | q.2.1 < D q.1 / 2} := by
      ext q; simp [B0579.cell, Set.mem_prod]
    rw [this]
    exact (measurableSet_le (by fun_prop) (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) (by fun_prop))
  have hI : StronglyMeasurable (fun q : α × (ℝ × ℝ) =>
      {q : α × (ℝ × ℝ) | q.2 ∈ B0579.cell (D q.1)}.indicator H q) :=
    (hH.indicator hset).stronglyMeasurable
  have := hI.integral_prod_right' (ν := (volume : Measure (ℝ × ℝ)))
  have heq : (fun a => ∫ z in B0579.cell (D a), H (a, z)) = fun a => ∫ z,
      {q : α × (ℝ × ℝ) | q.2 ∈ B0579.cell (D q.1)}.indicator H (a, z) := by
    funext a
    rw [← integral_indicator (B0579.measurableSet_cell _)]
    try congr 1
    try (funext z; simp only [Set.indicator_apply, Set.mem_setOf_eq])
  rw [heq]
  exact this.measurable

/-- Cell length at the clamped age. -/
abbrev dRho (ν t₁ t₂ r : ℝ) : ℝ := cellLen (ν ^ (-2 : ℝ)) (clockA ν (rho t₁ t₂ r))

lemma continuous_dRho {ν : ℝ} (hν : 0 < ν) {t₁ t₂ : ℝ} (ht : 0 ≤ t₁) :
    Continuous (dRho ν t₁ t₂) := by
  have hr : ∀ r, 1 ≤ clockA ν (rho t₁ t₂ r) := fun r =>
    one_le_clockA hν.le (ht.trans (le_max_left _ _))
  unfold dRho cellLen
  have hA : Continuous (fun r : ℝ => clockA ν (rho t₁ t₂ r)) := by
    unfold clockA; have := continuous_rho t₁ t₂; fun_prop
  refine continuous_const.div (Real.continuous_sqrt.comp hA) (fun r => ?_)
  exact (Real.sqrt_pos.2 (by linarith [hr r])).ne'

section

variable {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) {ν t₁ t₂ : ℝ} (hν : 0 < ν)
  (ht : 0 ≤ t₁) (hts : t₁ ≤ t₂)
  (hd1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))

include hd1 hts in
lemma one_le_dRho (r : ℝ) : 1 ≤ dRho ν t₁ t₂ r := hd1 _ (rho_mem hts r)

include hκ hν ht hts hd1 in
lemma measurable_perE_joint (j : Fin 2) :
    Measurable (fun p : ℝ × (ℝ × ℝ) => perE κ (dRho ν t₁ t₂ p.1) j p.2) := by
  obtain ⟨C, hC0, h0, -, -⟩ := OscillatorForceSub.seed_e_translate_bounds hκ j
  exact measurable_perSum_joint (κ.e_cont j) hC0 h0 hν ht hts hd1

include hκ hν ht hts hd1 in
lemma measurable_pdCx_perE_joint (j k : Fin 2) :
    Measurable (fun p : ℝ × (ℝ × ℝ) => pdCx k (perE κ (dRho ν t₁ t₂ p.1) j) p.2) := by
  have := measurable_fderiv_apply_param (fun r (w : ℝ × ℝ) => perE κ (dRho ν t₁ t₂ r) j w)
    (measurable_perE_joint hκ hν ht hts hd1 j) (fun r y => by
      have hpos : 0 < dRho ν t₁ t₂ r := lt_of_lt_of_le zero_lt_one (one_le_dRho hts hd1 r)
      exact ((EulerErrorSub.contDiff_two_perE hκ hpos j).differentiable (by norm_num)) y)
    (B0579.dir k)
  exact this

include hν ht hts hd1 in
lemma measurable_perLam0_joint (i : Fin 2) :
    Measurable (fun p : ℝ × (ℝ × ℝ) => perLam0 κ (dRho ν t₁ t₂ p.1) i p.2) := by
  obtain ⟨C, hC0, hC⟩ := Lam0B.lamP_translate_bound κ
  exact measurable_perSum_joint (κ.lamP_cont i) hC0 (hC i) hν ht hts hd1

include hν ht hts hd1 in
lemma measurable_Ginv (hdet : ∀ r ∈ Icc t₁ t₂,
      (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))).det ≠ 0) (i k : Fin 2) :
    Measurable (fun r : ℝ => (perGram κ (dRho ν t₁ t₂ r))⁻¹ i k) := by
  have hd_cont : ContinuousOn (fun r => cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (Icc t₁ t₂) :=
    FlowMeas.continuousOn_cellLen_clockA hν ht _ fun _ hr => hr.1
  have hmaps : MapsTo (fun r => cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (Icc t₁ t₂)
      {d : ℝ | 1 ≤ d ∧ (perGram κ d).det ≠ 0} := fun r hr => ⟨hd1 r hr, hdet r hr⟩
  have hG := (FlowMeas.continuousOn_perGram_inv' κ (S := {d : ℝ | 1 ≤ d ∧ (perGram κ d).det ≠ 0})
      (fun d hd => hd.1) (fun d hd => hd.2) i k).comp hd_cont hmaps
  exact (hG.comp_continuous (continuous_rho t₁ t₂) (rho_mem hts)).measurable

include hν ht hts hd1 in
lemma measurable_perLam_joint (hdet : ∀ r ∈ Icc t₁ t₂,
      (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))).det ≠ 0) (i : Fin 2) :
    Measurable (fun p : ℝ × (ℝ × ℝ) => perLam κ (dRho ν t₁ t₂ p.1) i p.2) := by
  unfold perLam
  refine Finset.measurable_sum _ (fun k _ => Measurable.mul ?_ ?_)
  · exact (measurable_Ginv hν ht hts hd1 hdet i k).comp measurable_fst
  · exact measurable_perLam0_joint hν ht hts hd1 k

end

end Leaf4Aux

end ComplFreeRateSub

end UnforcedLeray.Short.IIIa
