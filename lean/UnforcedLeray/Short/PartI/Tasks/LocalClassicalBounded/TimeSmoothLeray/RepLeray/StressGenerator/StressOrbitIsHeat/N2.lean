import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.StressGenerator.StressOrbitIsHeat.N1

/-!
# N2: heat of the row divergence (`NeedRowDivHeat`)

Proof of `NeedRowDivHeat` from `Needed.lean`, using `needSmoothRowIBP` (N1) for the two
output coordinates. For `θ > 0` the heat semigroup applied to the row divergence is the
convolution of the planar heat kernel with `rowDivergence T`; the first component of
`heatDiv θ T` is `∫ (∂_q K_θ T¹¹ + ∂_η K_θ T²¹)`, which N1 turns into the first component of
`∫ K_θ (∂_q T¹¹ + ∂_η T²¹)`, and similarly for the second component.

The Bochner integrals are split componentwise (`fst_integral`, `snd_integral`), so the proof
also needs the integrability of both integrands. These come from the integrability of the
one-dimensional kernels and their derivatives, and from the boundedness and continuity of `T`
and of `rowDivergence T`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- A directional derivative of a smooth real function is continuous in the base point. -/
theorem continuous_fderiv_apply_plane {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (v : Plane) :
    Continuous (fun z => fderiv ℝ f z v) :=
  (hf.continuous_fderiv (by simp)).clm_apply continuous_const

/-- Bound on a directional derivative from a bound on the derivative. -/
theorem norm_fderiv_apply_le' {f : Plane → ℝ} {K : ℝ} (hK : ∀ x, ‖fderiv ℝ f x‖ ≤ K)
    (x v : Plane) : ‖fderiv ℝ f x v‖ ≤ K * ‖v‖ :=
  (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hK x) (norm_nonneg _))

/-- The derivative of `y ↦ L (T y)` for a continuous linear functional `L` is bounded by
`‖L‖` times a bound of the derivative of `T`. -/
theorem norm_fderiv_comp_clm_le {T : Plane → Plane × Plane} (hT : ContDiff ℝ ∞ T)
    (L : (Plane × Plane) →L[ℝ] ℝ) {N : ℝ} (hN : ∀ x, ‖fderiv ℝ T x‖ ≤ N) (x : Plane) :
    ‖fderiv ℝ (fun y => L (T y)) x‖ ≤ ‖L‖ * N := by
  have hd : DifferentiableAt ℝ T x := (hT.differentiable (by simp)) x
  have h : fderiv ℝ (fun y => L (T y)) x = L.comp (fderiv ℝ T x) :=
    (L.hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  rw [h]
  exact (ContinuousLinearMap.opNorm_comp_le L (fderiv ℝ T x)).trans
    (mul_le_mul_of_nonneg_left (hN x) (norm_nonneg _))

theorem exists_fderiv_bound_comp {T : Plane → Plane × Plane} (hT : ContDiff ℝ ∞ T) {N : ℝ}
    (hN0 : 0 ≤ N) (hN : ∀ x, ‖fderiv ℝ T x‖ ≤ N) (L : (Plane × Plane) →L[ℝ] ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x, ‖fderiv ℝ (fun y => L (T y)) x‖ ≤ K :=
  ⟨‖L‖ * N, mul_nonneg (norm_nonneg _) hN0, norm_fderiv_comp_clm_le hT L hN⟩

/-- **N2** (heat of the divergence, for a smooth bounded two-row tensor), from N1. -/
theorem needRowDivHeat_of (h1 : NeedSmoothRowIBP) : NeedRowDivHeat := by
  unfold NeedSmoothRowIBP at h1
  intro θ hθ T hT hTB hDB z
  obtain ⟨M, hM0, hM⟩ := hTB
  obtain ⟨N, hN0, hN⟩ := hDB
  have cT : Continuous T := hT.continuous
  have cz : Continuous (fun w : Plane => z - w) := continuous_const.sub continuous_id
  have ha : ContDiff ℝ ∞ (fun x => (T x).1.1) := hT.fst.fst
  have hb : ContDiff ℝ ∞ (fun x => (T x).2.1) := hT.snd.fst
  have hc : ContDiff ℝ ∞ (fun x => (T x).1.2) := hT.fst.snd
  have hd : ContDiff ℝ ∞ (fun x => (T x).2.2) := hT.snd.snd
  have vA : ∀ x, ‖(T x).1.1‖ ≤ M := fun x =>
    (norm_fst_le (T x).1).trans ((norm_fst_le (T x)).trans (hM x))
  have vB : ∀ x, ‖(T x).2.1‖ ≤ M := fun x =>
    (norm_fst_le (T x).2).trans ((norm_snd_le (T x)).trans (hM x))
  have vC : ∀ x, ‖(T x).1.2‖ ≤ M := fun x =>
    (norm_snd_le (T x).1).trans ((norm_fst_le (T x)).trans (hM x))
  have vD : ∀ x, ‖(T x).2.2‖ ≤ M := fun x =>
    (norm_snd_le (T x).2).trans ((norm_snd_le (T x)).trans (hM x))
  obtain ⟨Ka, hKa0, hKa⟩ := exists_fderiv_bound_comp hT hN0 hN
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ Plane Plane))
  obtain ⟨Kb, hKb0, hKb⟩ := exists_fderiv_bound_comp hT hN0 hN
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ Plane Plane))
  obtain ⟨Kc, hKc0, hKc⟩ := exists_fderiv_bound_comp hT hN0 hN
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ Plane Plane))
  obtain ⟨Kd, hKd0, hKd⟩ := exists_fderiv_bound_comp hT hN0 hN
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ Plane Plane))
  -- N1 for each output coordinate
  have hS1 := h1 hθ ha hb ⟨M, hM0, vA⟩ ⟨M, hM0, vB⟩ ⟨Ka, hKa0, hKa⟩ ⟨Kb, hKb0, hKb⟩ z
  have hS2 := h1 hθ hc hd ⟨M, hM0, vC⟩ ⟨M, hM0, vD⟩ ⟨Kc, hKc0, hKc⟩ ⟨Kd, hKd0, hKd⟩ z
  -- integrability of the kernel and its gradient
  have hK : Integrable (B0284.heatKernel2 θ) := B0284.integrable_heatKernel2 hθ
  have hg1 : Integrable (fun w : Plane => (B0296.gradHeatKernel2 θ w).1) :=
    (B0296.integrable_dHeatKernel hθ).mul_prod (B0296.integrable_heatKernel1 hθ)
  have hg2 : Integrable (fun w : Plane => (B0296.gradHeatKernel2 θ w).2) :=
    (B0296.integrable_heatKernel1 hθ).mul_prod (B0296.integrable_dHeatKernel hθ)
  -- integrability of the integrand of the heat of the divergence
  have mA : AEStronglyMeasurable (fun w : Plane => (T (z - w)).1.1) volume :=
    ((cT.comp cz).fst.fst).aestronglyMeasurable
  have mB : AEStronglyMeasurable (fun w : Plane => (T (z - w)).2.1) volume :=
    ((cT.comp cz).snd.fst).aestronglyMeasurable
  have mC : AEStronglyMeasurable (fun w : Plane => (T (z - w)).1.2) volume :=
    ((cT.comp cz).fst.snd).aestronglyMeasurable
  have mD : AEStronglyMeasurable (fun w : Plane => (T (z - w)).2.2) volume :=
    ((cT.comp cz).snd.snd).aestronglyMeasurable
  have bA : ∀ᵐ w ∂(volume : Measure Plane), ‖(T (z - w)).1.1‖ ≤ M :=
    ae_of_all _ (fun w => vA (z - w))
  have bB : ∀ᵐ w ∂(volume : Measure Plane), ‖(T (z - w)).2.1‖ ≤ M :=
    ae_of_all _ (fun w => vB (z - w))
  have bC : ∀ᵐ w ∂(volume : Measure Plane), ‖(T (z - w)).1.2‖ ≤ M :=
    ae_of_all _ (fun w => vC (z - w))
  have bD : ∀ᵐ w ∂(volume : Measure Plane), ‖(T (z - w)).2.2‖ ≤ M :=
    ae_of_all _ (fun w => vD (z - w))
  have hF1 : Integrable (fun w : Plane =>
      (B0296.gradHeatKernel2 θ w).1 * (T (z - w)).1.1 +
        (B0296.gradHeatKernel2 θ w).2 * (T (z - w)).2.1) :=
    (hg1.mul_bdd mA bA).add (hg2.mul_bdd mB bB)
  have hF2 : Integrable (fun w : Plane =>
      (B0296.gradHeatKernel2 θ w).1 * (T (z - w)).1.2 +
        (B0296.gradHeatKernel2 θ w).2 * (T (z - w)).2.2) :=
    (hg1.mul_bdd mC bC).add (hg2.mul_bdd mD bD)
  have hF : Integrable (fun w : Plane => B0296.divKernel θ w (T (z - w))) :=
    hF1.prodMk hF2
  -- integrability of the integrand of the heat of the row divergence
  have hr1 : Continuous (fun x : Plane => (rowDivergence T x).1) :=
    (continuous_fderiv_apply_plane ha (1, 0)).add (continuous_fderiv_apply_plane hb (0, 1))
  have hr2 : Continuous (fun x : Plane => (rowDivergence T x).2) :=
    (continuous_fderiv_apply_plane hc (1, 0)).add (continuous_fderiv_apply_plane hd (0, 1))
  have br1 : ∀ x : Plane, ‖(rowDivergence T x).1‖ ≤
      Ka * ‖((1, 0) : Plane)‖ + Kb * ‖((0, 1) : Plane)‖ := fun x =>
    (norm_add_le _ _).trans
      (add_le_add (norm_fderiv_apply_le' hKa x _) (norm_fderiv_apply_le' hKb x _))
  have br2 : ∀ x : Plane, ‖(rowDivergence T x).2‖ ≤
      Kc * ‖((1, 0) : Plane)‖ + Kd * ‖((0, 1) : Plane)‖ := fun x =>
    (norm_add_le _ _).trans
      (add_le_add (norm_fderiv_apply_le' hKc x _) (norm_fderiv_apply_le' hKd x _))
  have mr1 : AEStronglyMeasurable (fun w : Plane => (rowDivergence T (z - w)).1) volume :=
    (hr1.comp cz).aestronglyMeasurable
  have mr2 : AEStronglyMeasurable (fun w : Plane => (rowDivergence T (z - w)).2) volume :=
    (hr2.comp cz).aestronglyMeasurable
  have br1' : ∀ᵐ w ∂(volume : Measure Plane), ‖(rowDivergence T (z - w)).1‖ ≤
      Ka * ‖((1, 0) : Plane)‖ + Kb * ‖((0, 1) : Plane)‖ :=
    ae_of_all _ (fun w => br1 (z - w))
  have br2' : ∀ᵐ w ∂(volume : Measure Plane), ‖(rowDivergence T (z - w)).2‖ ≤
      Kc * ‖((1, 0) : Plane)‖ + Kd * ‖((0, 1) : Plane)‖ :=
    ae_of_all _ (fun w => br2 (z - w))
  have hG1 : Integrable (fun w : Plane => B0284.heatKernel2 θ w * (rowDivergence T (z - w)).1) :=
    hK.mul_bdd mr1 br1'
  have hG2 : Integrable (fun w : Plane => B0284.heatKernel2 θ w * (rowDivergence T (z - w)).2) :=
    hK.mul_bdd mr2 br2'
  have hG : Integrable (fun w : Plane => B0284.heatKernel2 θ w • rowDivergence T (z - w)) :=
    hG1.prodMk hG2
  -- assemble componentwise
  rw [B0296.heatDiv_apply_of_pos hθ, B0284.heat_apply_of_pos hθ]
  refine Prod.ext ?_ ?_
  · rw [fst_integral hF, fst_integral hG]
    exact hS1
  · rw [snd_integral hF, snd_integral hG]
    exact hS2

/-- **N2** (heat of the divergence, for a smooth bounded two-row tensor). -/
theorem needRowDivHeat : NeedRowDivHeat := needRowDivHeat_of needSmoothRowIBP

end UnforcedLeray.Short.PartI
