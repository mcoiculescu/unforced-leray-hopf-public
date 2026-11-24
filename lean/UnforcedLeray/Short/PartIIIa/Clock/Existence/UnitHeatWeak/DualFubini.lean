import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_2_Smooth.DualSplit
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.WeightedHeat
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.FluxHeatCLM

/-!
# Part III-a, `PartIII-a:T21/3/2/2/2/2`: the Gaussian heat-divergence duality

Source of record: `the November 2 reference manuscript`, lines 2819-2836.
Proves `HeatDivFluxDual` (`DualSplit.lean`): Fubini on `cell × ℝ²`, periodic translation of the
cell, and one Gaussian integration by parts in each coordinate.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
open UnforcedLeray.B0284 (heatKernel2)

theorem dualFub_cell_eq (c : ℝ) :
    UnforcedLeray.B0579.cell c = UnforcedLeray.Cyl.cell c := by
  simp only [UnforcedLeray.B0579.cell, UnforcedLeray.Cyl.cell, neg_div]

theorem dualFub_differentiable_kernel (θ : ℝ) : Differentiable ℝ (heatKernel2 θ) := by
  show Differentiable ℝ (fun w : ℝ × ℝ =>
    UnforcedLeray.B0191.heatKernel 1 θ w.1 * UnforcedLeray.B0191.heatKernel 1 θ w.2)
  exact ((differentiable_heatKernel1 θ).comp differentiable_fst).mul
    ((differentiable_heatKernel1 θ).comp differentiable_snd)

theorem dualFub_fderiv_fst {θ : ℝ} (hθ : 0 < θ) (w : ℝ × ℝ) :
    fderiv ℝ (heatKernel2 θ) w ((1 : ℝ), (0 : ℝ)) =
      (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 :=
  fderiv_apply_q_of_hasDerivAt (dualFub_differentiable_kernel θ) w
    (UnforcedLeray.B0296.hasDerivAt_heatKernel2_fst hθ.ne' w)

theorem dualFub_fderiv_snd {θ : ℝ} (hθ : 0 < θ) (w : ℝ × ℝ) :
    fderiv ℝ (heatKernel2 θ) w ((0 : ℝ), (1 : ℝ)) =
      (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 :=
  fderiv_apply_eta_of_hasDerivAt (dualFub_differentiable_kernel θ) w
    (UnforcedLeray.B0296.hasDerivAt_heatKernel2_snd hθ.ne' w)

theorem dualFub_integrable_fst {θ : ℝ} (hθ : 0 < θ) :
    Integrable (fun w : ℝ × ℝ => (UnforcedLeray.B0296.gradHeatKernel2 θ w).1) := by
  rw [show (fun w : ℝ × ℝ => (UnforcedLeray.B0296.gradHeatKernel2 θ w).1) =
      fun w => UnforcedLeray.B0296.dHeatKernel θ w.1 *
        UnforcedLeray.B0191.heatKernel 1 θ w.2 by rfl]
  exact (UnforcedLeray.B0296.integrable_dHeatKernel hθ).mul_prod
    (UnforcedLeray.B0296.integrable_heatKernel1 hθ)

theorem dualFub_integrable_snd {θ : ℝ} (hθ : 0 < θ) :
    Integrable (fun w : ℝ × ℝ => (UnforcedLeray.B0296.gradHeatKernel2 θ w).2) := by
  rw [show (fun w : ℝ × ℝ => (UnforcedLeray.B0296.gradHeatKernel2 θ w).2) =
      fun w => UnforcedLeray.B0191.heatKernel 1 θ w.1 *
        UnforcedLeray.B0296.dHeatKernel θ w.2 by rfl]
  exact (UnforcedLeray.B0296.integrable_heatKernel1 hθ).mul_prod
    (UnforcedLeray.B0296.integrable_dHeatKernel hθ)

theorem dualFub_dHeat_neg (θ x : ℝ) :
    UnforcedLeray.B0296.dHeatKernel θ (-x) = -UnforcedLeray.B0296.dHeatKernel θ x := by
  simp only [UnforcedLeray.B0296.dHeatKernel, UnforcedLeray.B0191.heatKernel, neg_sq]
  ring

theorem dualFub_heat_neg (θ x : ℝ) :
    UnforcedLeray.B0191.heatKernel 1 θ (-x) = UnforcedLeray.B0191.heatKernel 1 θ x := by
  simp only [UnforcedLeray.B0191.heatKernel, neg_sq]

theorem dualFub_grad_fst_neg (θ : ℝ) (w : ℝ × ℝ) :
    (UnforcedLeray.B0296.gradHeatKernel2 θ (-w)).1 =
      -(UnforcedLeray.B0296.gradHeatKernel2 θ w).1 := by
  simp only [UnforcedLeray.B0296.gradHeatKernel2, Prod.fst_neg, Prod.snd_neg,
    dualFub_dHeat_neg, dualFub_heat_neg, neg_mul]

theorem dualFub_grad_snd_neg (θ : ℝ) (w : ℝ × ℝ) :
    (UnforcedLeray.B0296.gradHeatKernel2 θ (-w)).2 =
      -(UnforcedLeray.B0296.gradHeatKernel2 θ w).2 := by
  simp only [UnforcedLeray.B0296.gradHeatKernel2, Prod.fst_neg, Prod.snd_neg,
    dualFub_dHeat_neg, dualFub_heat_neg, mul_neg]

/-- Gaussian integration by parts in `q`, after reflection: `∫ ∂_qG(w) ψ(y+w) = -P_θ(∂_qψ)(y)`. -/
theorem dualFub_gauss_q {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {ψ : ℝ × ℝ → ℝ} (hψ : UnforcedLeray.B0579.IsCylTest c ψ) (y : ℝ × ℝ) :
    ∫ w : ℝ × ℝ, (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 * ψ (y + w) =
      -cylHeatSmooth c θ (UnforcedLeray.B0579.pd 0 ψ) y := by
  obtain ⟨M, -, hM⟩ := cylTest_exists_bound hc hψ
  obtain ⟨N, -, hN⟩ := cylTest_exists_fderiv_bound hc hψ
  have hC1 : ContDiff ℝ 1 ψ := hψ.smooth.of_le (by simp)
  have hKe : Integrable (fun w : ℝ × ℝ => fderiv ℝ (heatKernel2 θ) w ((1 : ℝ), (0 : ℝ))) :=
    (dualFub_integrable_fst hθ).congr
      (Eventually.of_forall fun w => (dualFub_fderiv_fst hθ w).symm)
  have hpd0 : ∀ x : ℝ × ℝ, fderiv ℝ ψ x ((1 : ℝ), (0 : ℝ)) = UnforcedLeray.B0579.pd 0 ψ x :=
    fun x => by simp only [UnforcedLeray.B0579.pd, dir_zero']
  have hIBP : ∫ w : ℝ × ℝ, (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 * ψ (y - w) =
      ∫ w : ℝ × ℝ, heatKernel2 θ w * UnforcedLeray.B0579.pd 0 ψ (y - w) := by
    have h := integral_kernel_fderiv_mul_comp_sub (dualFub_differentiable_kernel θ)
      (UnforcedLeray.B0284.integrable_heatKernel2 hθ) ((1 : ℝ), (0 : ℝ)) hKe hC1 hM hN y
    simp only [dualFub_fderiv_fst hθ, hpd0] at h
    exact h
  have hodd : ∀ w : ℝ × ℝ, (UnforcedLeray.B0296.gradHeatKernel2 θ (-w)).1 * ψ (y + -w) =
      -((UnforcedLeray.B0296.gradHeatKernel2 θ w).1 * ψ (y - w)) := by
    intro w
    rw [dualFub_grad_fst_neg, neg_mul, sub_eq_add_neg]
  have hrefl : ∫ w : ℝ × ℝ, (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 * ψ (y + w) =
      ∫ w : ℝ × ℝ, (UnforcedLeray.B0296.gradHeatKernel2 θ (-w)).1 * ψ (y + -w) :=
    (integral_neg_eq_self
      (fun w : ℝ × ℝ => (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 * ψ (y + w)) volume).symm
  have hstep : ∫ w : ℝ × ℝ, (UnforcedLeray.B0296.gradHeatKernel2 θ (-w)).1 * ψ (y + -w) =
      -∫ w : ℝ × ℝ, (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 * ψ (y - w) := by
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall hodd)
  rw [hrefl, hstep, hIBP, cylHeatSmooth_apply_of_pos hθ]

/-- Gaussian integration by parts in `η`, after reflection. -/
theorem dualFub_gauss_eta {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {ψ : ℝ × ℝ → ℝ} (hψ : UnforcedLeray.B0579.IsCylTest c ψ) (y : ℝ × ℝ) :
    ∫ w : ℝ × ℝ, (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 * ψ (y + w) =
      -cylHeatSmooth c θ (UnforcedLeray.B0579.pd 1 ψ) y := by
  obtain ⟨M, -, hM⟩ := cylTest_exists_bound hc hψ
  obtain ⟨N, -, hN⟩ := cylTest_exists_fderiv_bound hc hψ
  have hC1 : ContDiff ℝ 1 ψ := hψ.smooth.of_le (by simp)
  have hKe : Integrable (fun w : ℝ × ℝ => fderiv ℝ (heatKernel2 θ) w ((0 : ℝ), (1 : ℝ))) :=
    (dualFub_integrable_snd hθ).congr
      (Eventually.of_forall fun w => (dualFub_fderiv_snd hθ w).symm)
  have hpd1 : ∀ x : ℝ × ℝ, fderiv ℝ ψ x ((0 : ℝ), (1 : ℝ)) = UnforcedLeray.B0579.pd 1 ψ x :=
    fun x => by simp only [UnforcedLeray.B0579.pd, dir_one']
  have hIBP : ∫ w : ℝ × ℝ, (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 * ψ (y - w) =
      ∫ w : ℝ × ℝ, heatKernel2 θ w * UnforcedLeray.B0579.pd 1 ψ (y - w) := by
    have h := integral_kernel_fderiv_mul_comp_sub (dualFub_differentiable_kernel θ)
      (UnforcedLeray.B0284.integrable_heatKernel2 hθ) ((0 : ℝ), (1 : ℝ)) hKe hC1 hM hN y
    simp only [dualFub_fderiv_snd hθ, hpd1] at h
    exact h
  have hodd : ∀ w : ℝ × ℝ, (UnforcedLeray.B0296.gradHeatKernel2 θ (-w)).2 * ψ (y + -w) =
      -((UnforcedLeray.B0296.gradHeatKernel2 θ w).2 * ψ (y - w)) := by
    intro w
    rw [dualFub_grad_snd_neg, neg_mul, sub_eq_add_neg]
  have hrefl : ∫ w : ℝ × ℝ, (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 * ψ (y + w) =
      ∫ w : ℝ × ℝ, (UnforcedLeray.B0296.gradHeatKernel2 θ (-w)).2 * ψ (y + -w) :=
    (integral_neg_eq_self
      (fun w : ℝ × ℝ => (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 * ψ (y + w)) volume).symm
  have hstep : ∫ w : ℝ × ℝ, (UnforcedLeray.B0296.gradHeatKernel2 θ (-w)).2 * ψ (y + -w) =
      -∫ w : ℝ × ℝ, (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 * ψ (y - w) := by
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall hodd)
  rw [hrefl, hstep, hIBP, cylHeatSmooth_apply_of_pos hθ]

/-- Periodic translation of the cell: `∫_cell f(x - w) ψ(x) = ∫_cell f(y) ψ(y + w)`. -/
theorem dualFub_cell_shift {c : ℝ} (hc : 0 < c) {f ψ : ℝ × ℝ → ℝ}
    (hf : UnforcedLeray.Cyl.IsPeriodic c f) (hψ : UnforcedLeray.B0579.IsCylTest c ψ)
    (w : ℝ × ℝ) :
    ∫ x in UnforcedLeray.Cyl.cell c, f (x - w) * ψ x =
      ∫ y in UnforcedLeray.Cyl.cell c, f y * ψ (y + w) := by
  have hG : UnforcedLeray.Cyl.IsPeriodic c (fun y => f y * ψ (y + w)) := by
    intro z
    have hψz : ψ ((z.1 + c, z.2) + w) = ψ (z + w) := by
      have hx : (z.1 + c, z.2) + w = ((z + w).1 + c, (z + w).2) := by
        ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
      rw [hx]
      exact hψ.periodic (z + w)
    show f (z.1 + c, z.2) * ψ ((z.1 + c, z.2) + w) = f z * ψ (z + w)
    rw [hf z, hψz]
  have h := UnforcedLeray.Cyl.integral_cell_comp_add hc hG (-w)
  calc ∫ x in UnforcedLeray.Cyl.cell c, f (x - w) * ψ x
      = ∫ x in UnforcedLeray.Cyl.cell c, (fun y => f y * ψ (y + w)) (x + -w) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [sub_eq_add_neg, neg_add_cancel_right]
    _ = ∫ y in UnforcedLeray.Cyl.cell c, f y * ψ (y + w) := h

/-- Integrability of `g · ψ` for a bounded continuous `ψ`. -/
theorem dualFub_integrable_mul_bdd {μ : Measure (ℝ × ℝ)} {g ψ : ℝ × ℝ → ℝ}
    (hg : Integrable g μ) (hψc : Continuous ψ) {M : ℝ} (hM : ∀ x, |ψ x| ≤ M) :
    Integrable (fun x => g x * ψ x) μ := by
  refine (hg.norm.const_mul M).mono' ?_ ?_
  · exact hg.aestronglyMeasurable.mul hψc.aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    rw [norm_mul]
    have hb : ‖ψ x‖ ≤ M := by rw [Real.norm_eq_abs]; exact hM x
    calc ‖g x‖ * ‖ψ x‖ ≤ ‖g x‖ * M := by gcongr
      _ = M * ‖g x‖ := by ring

/-- Integrability of `k(w) · (F(y) ψ(y + w))` on `ℝ² × cell`. -/
theorem dualFub_integrable_shift_prod {c : ℝ} {k Fq ψ : ℝ × ℝ → ℝ}
    (hk : Integrable k) (hkm : StronglyMeasurable k)
    (hFq : Integrable Fq (volume.restrict (UnforcedLeray.Cyl.cell c)))
    (hFqm : StronglyMeasurable Fq) (hψc : Continuous ψ) {M : ℝ} (hM : ∀ x, |ψ x| ≤ M) :
    Integrable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => k q.1 * (Fq q.2 * ψ (q.2 + q.1)))
      (volume.prod (volume.restrict (UnforcedLeray.Cyl.cell c))) := by
  have hI : Integrable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => k q.1 * Fq q.2)
      (volume.prod (volume.restrict (UnforcedLeray.Cyl.cell c))) :=
    hk.mul_prod hFq
  refine (hI.norm.const_mul M).mono' ?_ ?_
  · have h1 : StronglyMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => k q.1) :=
      hkm.comp_measurable measurable_fst
    have h2 : StronglyMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => Fq q.2) :=
      hFqm.comp_measurable measurable_snd
    have h3 : StronglyMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => ψ (q.2 + q.1)) :=
      (hψc.comp (continuous_snd.add continuous_fst)).stronglyMeasurable
    exact (h1.mul (h2.mul h3)).aestronglyMeasurable
  · refine Eventually.of_forall fun q => ?_
    have hψn : ‖ψ (q.2 + q.1)‖ ≤ M := by rw [Real.norm_eq_abs]; exact hM _
    calc ‖k q.1 * (Fq q.2 * ψ (q.2 + q.1))‖
        = ‖k q.1‖ * (‖Fq q.2‖ * ‖ψ (q.2 + q.1)‖) := by rw [norm_mul, norm_mul]
      _ ≤ ‖k q.1‖ * (‖Fq q.2‖ * M) := by gcongr
      _ = M * (‖k q.1‖ * ‖Fq q.2‖) := by ring
      _ = M * ‖k q.1 * Fq q.2‖ := by rw [norm_mul]

/-- The product integrability of the scalar flux kernel on `cell × ℝ²`. -/
theorem dualFub_integrable_phi {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) {Fq Fη : ℝ × ℝ → ℝ}
    (hFqm : StronglyMeasurable Fq) (hFem : StronglyMeasurable Fη)
    (hQper : UnforcedLeray.Cyl.IsPeriodic c Fq) (hEper : UnforcedLeray.Cyl.IsPeriodic c Fη)
    (hQint : Integrable Fq (volume.restrict (UnforcedLeray.Cyl.cell c)))
    (hEint : Integrable Fη (volume.restrict (UnforcedLeray.Cyl.cell c))) :
    Integrable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => scalarFluxKernelIntegrand θ Fq Fη q.1 q.2)
      ((volume.restrict (UnforcedLeray.Cyl.cell c)).prod volume) := by
  have hQi : ∀ w : ℝ × ℝ,
      Integrable (fun z => Fq (z - w)) (volume.restrict (UnforcedLeray.Cyl.cell c)) := fun w => by
    simpa only [sub_eq_add_neg] using
      integrable_translate_cell_of_periodic hc hFqm hQper hQint (-w)
  have hEi : ∀ w : ℝ × ℝ,
      Integrable (fun z => Fη (z - w)) (volume.restrict (UnforcedLeray.Cyl.cell c)) := fun w => by
    simpa only [sub_eq_add_neg] using
      integrable_translate_cell_of_periodic hc hFem hEper hEint (-w)
  have hFqc : StronglyMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => Fq (q.1 - q.2)) :=
    hFqm.comp_measurable (by fun_prop)
  have hFec : StronglyMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => Fη (q.1 - q.2)) :=
    hFem.comp_measurable (by fun_prop)
  have hkq : StronglyMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      (UnforcedLeray.B0296.gradHeatKernel2 θ q.2).1) :=
    ((UnforcedLeray.B0296.measurable_gradHeatKernel2_fst θ).comp measurable_snd).stronglyMeasurable
  have hke : StronglyMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      (UnforcedLeray.B0296.gradHeatKernel2 θ q.2).2) :=
    ((UnforcedLeray.B0296.measurable_gradHeatKernel2_snd θ).comp measurable_snd).stronglyMeasurable
  have hmeas : StronglyMeasurable
      (fun q : (ℝ × ℝ) × (ℝ × ℝ) => scalarFluxKernelIntegrand θ Fq Fη q.1 q.2) := by
    show StronglyMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      (UnforcedLeray.B0296.gradHeatKernel2 θ q.2).1 * Fq (q.1 - q.2) +
        (UnforcedLeray.B0296.gradHeatKernel2 θ q.2).2 * Fη (q.1 - q.2))
    exact (hkq.mul hFqc).add (hke.mul hFec)
  exact integrable_scalarFluxKernelIntegrand hc hθ hQper hEper hQi hEi hmeas

/-- Core duality for arbitrary periodic column representatives `Fq`, `Fη`. -/
theorem dualFub_core {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) {Fq Fη : ℝ × ℝ → ℝ}
    (hFqm : StronglyMeasurable Fq) (hFem : StronglyMeasurable Fη)
    (hQper : UnforcedLeray.Cyl.IsPeriodic c Fq) (hEper : UnforcedLeray.Cyl.IsPeriodic c Fη)
    (hQint : Integrable Fq (volume.restrict (UnforcedLeray.Cyl.cell c)))
    (hEint : Integrable Fη (volume.restrict (UnforcedLeray.Cyl.cell c)))
    {ψ : ℝ × ℝ → ℝ} (hψ : UnforcedLeray.B0579.IsCylTest c ψ) :
    ∫ x in UnforcedLeray.Cyl.cell c, (negativeHeatDiv θ (scalarFluxTensor Fq Fη) x).1 * ψ x =
      ∫ x in UnforcedLeray.Cyl.cell c,
        (Fq x * UnforcedLeray.B0579.pd 0 (cylHeatSmooth c θ ψ) x +
          Fη x * UnforcedLeray.B0579.pd 1 (cylHeatSmooth c θ ψ) x) := by
  rw [pd_cylHeatSmooth hc hψ 0, pd_cylHeatSmooth hc hψ 1]
  obtain ⟨M, -, hM⟩ := cylTest_exists_bound hc hψ
  have hψc : Continuous ψ := hψ.continuous
  have hProd := dualFub_integrable_phi hc hθ hFqm hFem hQper hEper hQint hEint
  have hQi : ∀ w : ℝ × ℝ,
      Integrable (fun z => Fq (z - w)) (volume.restrict (UnforcedLeray.Cyl.cell c)) := fun w => by
    simpa only [sub_eq_add_neg] using
      integrable_translate_cell_of_periodic hc hFqm hQper hQint (-w)
  have hEi : ∀ w : ℝ × ℝ,
      Integrable (fun z => Fη (z - w)) (volume.restrict (UnforcedLeray.Cyl.cell c)) := fun w => by
    simpa only [sub_eq_add_neg] using
      integrable_translate_cell_of_periodic hc hFem hEper hEint (-w)
  -- pointwise formula for the response on the cell
  have hae : ∀ᵐ x ∂(volume.restrict (UnforcedLeray.Cyl.cell c)),
      (negativeHeatDiv θ (scalarFluxTensor Fq Fη) x).1 =
        -∫ w : ℝ × ℝ, scalarFluxKernelIntegrand θ Fq Fη x w := by
    filter_upwards [hProd.prod_right_ae] with x hx
    have hvecEq : (fun w : ℝ × ℝ => UnforcedLeray.B0296.divKernel θ w (scalarFluxTensor Fq Fη (x - w))) =
        fun w => (scalarFluxKernelIntegrand θ Fq Fη x w, 0) :=
      funext fun w => divKernel_scalarFluxTensor θ Fq Fη x w
    have hvec : Integrable
        (fun w : ℝ × ℝ => UnforcedLeray.B0296.divKernel θ w (scalarFluxTensor Fq Fη (x - w))) volume :=
      (hx.prodMk (integrable_zero (α := ℝ × ℝ) (ε' := ℝ) volume)).congr
        (Eventually.of_forall fun w => (congrFun hvecEq w).symm)
    simp only [negativeHeatDiv, Prod.fst_neg]
    rw [UnforcedLeray.B0296.heatDiv_apply_of_pos hθ, fst_integral hvec]
    congr 1
  have hLHS : ∫ x in UnforcedLeray.Cyl.cell c, (negativeHeatDiv θ (scalarFluxTensor Fq Fη) x).1 * ψ x =
      -∫ x in UnforcedLeray.Cyl.cell c, ∫ w : ℝ × ℝ,
        ψ x * scalarFluxKernelIntegrand θ Fq Fη x w := by
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx, integral_const_mul]
    ring
  -- Fubini on `cell × ℝ²`
  have hsw1 : ∫ x in UnforcedLeray.Cyl.cell c, ∫ w : ℝ × ℝ,
        ψ x * scalarFluxKernelIntegrand θ Fq Fη x w =
      ∫ w : ℝ × ℝ, ∫ x in UnforcedLeray.Cyl.cell c,
        ψ x * scalarFluxKernelIntegrand θ Fq Fη x w := by
    refine integral_integral_swap
      (f := fun x w => ψ x * scalarFluxKernelIntegrand θ Fq Fη x w) ?_
    refine hProd.bdd_mul (f := fun q : (ℝ × ℝ) × (ℝ × ℝ) => ψ q.1) (c := M) ?_ ?_
    · exact (hψc.comp continuous_fst).aestronglyMeasurable
    · refine Eventually.of_forall fun q => ?_
      rw [Real.norm_eq_abs]
      exact hM _
  -- pointwise in `w`: translate the cell and split the two components
  have hpt : ∀ w : ℝ × ℝ, ∫ x in UnforcedLeray.Cyl.cell c,
      ψ x * scalarFluxKernelIntegrand θ Fq Fη x w =
        (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 *
            (∫ y in UnforcedLeray.Cyl.cell c, Fq y * ψ (y + w)) +
          (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 *
            (∫ y in UnforcedLeray.Cyl.cell c, Fη y * ψ (y + w)) := by
    intro w
    have hI1 : Integrable (fun x => Fq (x - w) * ψ x)
        (volume.restrict (UnforcedLeray.Cyl.cell c)) :=
      dualFub_integrable_mul_bdd (hQi w) hψc hM
    have hI2 : Integrable (fun x => Fη (x - w) * ψ x)
        (volume.restrict (UnforcedLeray.Cyl.cell c)) :=
      dualFub_integrable_mul_bdd (hEi w) hψc hM
    calc ∫ x in UnforcedLeray.Cyl.cell c, ψ x * scalarFluxKernelIntegrand θ Fq Fη x w
        = ∫ x in UnforcedLeray.Cyl.cell c,
            ((UnforcedLeray.B0296.gradHeatKernel2 θ w).1 * (Fq (x - w) * ψ x) +
              (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 * (Fη (x - w) * ψ x)) := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          unfold scalarFluxKernelIntegrand
          ring
      _ = (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 *
            (∫ x in UnforcedLeray.Cyl.cell c, Fq (x - w) * ψ x) +
          (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 *
            (∫ x in UnforcedLeray.Cyl.cell c, Fη (x - w) * ψ x) := by
          rw [integral_add (hI1.const_mul _) (hI2.const_mul _), integral_const_mul,
            integral_const_mul]
      _ = _ := by
          rw [dualFub_cell_shift hc hQper hψ w, dualFub_cell_shift hc hEper hψ w]
  -- the two Fubini integrals over `ℝ² × cell`
  have hAq := dualFub_integrable_shift_prod (c := c)
    (k := fun w => (UnforcedLeray.B0296.gradHeatKernel2 θ w).1)
    (dualFub_integrable_fst hθ)
    (UnforcedLeray.B0296.measurable_gradHeatKernel2_fst θ).stronglyMeasurable
    hQint hFqm hψc hM
  have hAe := dualFub_integrable_shift_prod (c := c)
    (k := fun w => (UnforcedLeray.B0296.gradHeatKernel2 θ w).2)
    (dualFub_integrable_snd hθ)
    (UnforcedLeray.B0296.measurable_gradHeatKernel2_snd θ).stronglyMeasurable
    hEint hFem hψc hM
  have hQy : ∀ y : ℝ × ℝ, ∫ w : ℝ × ℝ,
      (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 * (Fq y * ψ (y + w)) =
        Fq y * (-cylHeatSmooth c θ (UnforcedLeray.B0579.pd 0 ψ) y) := by
    intro y
    have h : ∫ w : ℝ × ℝ, (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 * (Fq y * ψ (y + w)) =
        Fq y * ∫ w : ℝ × ℝ, (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 * ψ (y + w) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun w => by ring)
    rw [h, dualFub_gauss_q hc hθ hψ y]
  have hEy : ∀ y : ℝ × ℝ, ∫ w : ℝ × ℝ,
      (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 * (Fη y * ψ (y + w)) =
        Fη y * (-cylHeatSmooth c θ (UnforcedLeray.B0579.pd 1 ψ) y) := by
    intro y
    have h : ∫ w : ℝ × ℝ, (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 * (Fη y * ψ (y + w)) =
        Fη y * ∫ w : ℝ × ℝ, (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 * ψ (y + w) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun w => by ring)
    rw [h, dualFub_gauss_eta hc hθ hψ y]
  have hQ : ∫ w : ℝ × ℝ, (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 *
      (∫ y in UnforcedLeray.Cyl.cell c, Fq y * ψ (y + w)) =
        ∫ y in UnforcedLeray.Cyl.cell c,
          Fq y * (-cylHeatSmooth c θ (UnforcedLeray.B0579.pd 0 ψ) y) := by
    calc ∫ w : ℝ × ℝ, (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 *
          (∫ y in UnforcedLeray.Cyl.cell c, Fq y * ψ (y + w))
        = ∫ w : ℝ × ℝ, ∫ y in UnforcedLeray.Cyl.cell c,
            (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 * (Fq y * ψ (y + w)) := by
          refine integral_congr_ae (Eventually.of_forall fun w => ?_)
          simp only [integral_const_mul]
      _ = ∫ y in UnforcedLeray.Cyl.cell c, ∫ w : ℝ × ℝ,
            (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 * (Fq y * ψ (y + w)) :=
          integral_integral_swap
            (f := fun w y => (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 * (Fq y * ψ (y + w))) hAq
      _ = _ := integral_congr_ae (Eventually.of_forall fun y => hQy y)
  have hE : ∫ w : ℝ × ℝ, (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 *
      (∫ y in UnforcedLeray.Cyl.cell c, Fη y * ψ (y + w)) =
        ∫ y in UnforcedLeray.Cyl.cell c,
          Fη y * (-cylHeatSmooth c θ (UnforcedLeray.B0579.pd 1 ψ) y) := by
    calc ∫ w : ℝ × ℝ, (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 *
          (∫ y in UnforcedLeray.Cyl.cell c, Fη y * ψ (y + w))
        = ∫ w : ℝ × ℝ, ∫ y in UnforcedLeray.Cyl.cell c,
            (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 * (Fη y * ψ (y + w)) := by
          refine integral_congr_ae (Eventually.of_forall fun w => ?_)
          simp only [integral_const_mul]
      _ = ∫ y in UnforcedLeray.Cyl.cell c, ∫ w : ℝ × ℝ,
            (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 * (Fη y * ψ (y + w)) :=
          integral_integral_swap
            (f := fun w y => (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 * (Fη y * ψ (y + w))) hAe
      _ = _ := integral_congr_ae (Eventually.of_forall fun y => hEy y)
  have hIq : Integrable (fun w : ℝ × ℝ => (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 *
      (∫ y in UnforcedLeray.Cyl.cell c, Fq y * ψ (y + w))) := by
    refine hAq.integral_prod_left.congr (Eventually.of_forall fun w => ?_)
    simp only [integral_const_mul]
  have hIe : Integrable (fun w : ℝ × ℝ => (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 *
      (∫ y in UnforcedLeray.Cyl.cell c, Fη y * ψ (y + w))) := by
    refine hAe.integral_prod_left.congr (Eventually.of_forall fun w => ?_)
    simp only [integral_const_mul]
  have hYq : Integrable (fun y : ℝ × ℝ =>
      Fq y * (-cylHeatSmooth c θ (UnforcedLeray.B0579.pd 0 ψ) y))
      (volume.restrict (UnforcedLeray.Cyl.cell c)) :=
    hAq.integral_prod_right.congr (Eventually.of_forall fun y => hQy y)
  have hYe : Integrable (fun y : ℝ × ℝ =>
      Fη y * (-cylHeatSmooth c θ (UnforcedLeray.B0579.pd 1 ψ) y))
      (volume.restrict (UnforcedLeray.Cyl.cell c)) :=
    hAe.integral_prod_right.congr (Eventually.of_forall fun y => hEy y)
  have hQC : Integrable (fun y : ℝ × ℝ => Fq y * cylHeatSmooth c θ (UnforcedLeray.B0579.pd 0 ψ) y)
      (volume.restrict (UnforcedLeray.Cyl.cell c)) :=
    (hYq.const_mul (-1)).congr (Eventually.of_forall fun y => by ring)
  have hEC : Integrable (fun y : ℝ × ℝ => Fη y * cylHeatSmooth c θ (UnforcedLeray.B0579.pd 1 ψ) y)
      (volume.restrict (UnforcedLeray.Cyl.cell c)) :=
    (hYe.const_mul (-1)).congr (Eventually.of_forall fun y => by ring)
  calc ∫ x in UnforcedLeray.Cyl.cell c, (negativeHeatDiv θ (scalarFluxTensor Fq Fη) x).1 * ψ x
      = -∫ x in UnforcedLeray.Cyl.cell c, ∫ w : ℝ × ℝ,
          ψ x * scalarFluxKernelIntegrand θ Fq Fη x w := hLHS
    _ = -∫ w : ℝ × ℝ, ∫ x in UnforcedLeray.Cyl.cell c,
          ψ x * scalarFluxKernelIntegrand θ Fq Fη x w := by rw [hsw1]
    _ = -∫ w : ℝ × ℝ, ((UnforcedLeray.B0296.gradHeatKernel2 θ w).1 *
            (∫ y in UnforcedLeray.Cyl.cell c, Fq y * ψ (y + w)) +
          (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 *
            (∫ y in UnforcedLeray.Cyl.cell c, Fη y * ψ (y + w))) := by
        congr 1
        exact integral_congr_ae (Eventually.of_forall hpt)
    _ = -((∫ w : ℝ × ℝ, (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 *
            (∫ y in UnforcedLeray.Cyl.cell c, Fq y * ψ (y + w))) +
          (∫ w : ℝ × ℝ, (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 *
            (∫ y in UnforcedLeray.Cyl.cell c, Fη y * ψ (y + w)))) := by
        rw [integral_add hIq hIe]
    _ = -((∫ y in UnforcedLeray.Cyl.cell c,
            Fq y * (-cylHeatSmooth c θ (UnforcedLeray.B0579.pd 0 ψ) y)) +
          (∫ y in UnforcedLeray.Cyl.cell c,
            Fη y * (-cylHeatSmooth c θ (UnforcedLeray.B0579.pd 1 ψ) y))) := by
        rw [hQ, hE]
    _ = ∫ x in UnforcedLeray.Cyl.cell c,
          (Fq x * cylHeatSmooth c θ (UnforcedLeray.B0579.pd 0 ψ) x +
            Fη x * cylHeatSmooth c θ (UnforcedLeray.B0579.pd 1 ψ) x) := by
        rw [integral_add hQC hEC]
        simp only [mul_neg, integral_neg]
        ring

/-- `PartIII-a:T21/3/2/2/2/2`: the Gaussian heat-divergence duality for the periodic columns. -/
theorem heatDivFluxDual : UnforcedLeray.Short.IIIa.Exist.HeatDivFluxDual := by
  intro c m _ hm F ψ hψ θ hθ
  have hc : 0 < c := Fact.out
  rw [dualFub_cell_eq c]
  exact dualFub_core hc hθ.1
    (stronglyMeasurable_xColumnPeriodicRep hc (F 0))
    (stronglyMeasurable_xColumnPeriodicRep hc (F 1))
    (periodic_xColumnPeriodicRep hc (F 0)) (periodic_xColumnPeriodicRep hc (F 1))
    (integrable_xColumnPeriodicRep hc hm (F 0)) (integrable_xColumnPeriodicRep hc hm (F 1)) hψ

end UnforcedLeray.Short.IIIa.Exist
