import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_2_2

/-!
# `PartIII-b:C/ward/13/8/2/2/3`: scaling step for the annular Poincare inequality

Proof of `annularScaling` (source 117-118, 2641-2642). Given the unit-annulus inequality with
constant `C` and a `C^1` function `p`, apply it to `q(z) = p(R z)`:

* `grad q(z) = R grad p(R z)`, so `|grad q(z)|^2 = R^2 |grad p(R z)|^2`;
* `A_R = R • A_1` and the set change of variables `z |-> R z` (Jacobian `R^3`) give
  `int_{A_1} (q - m)^2 = (R^3)⁻¹ int_{A_R} (p - m)^2` and
  `int_{A_1} |grad p (R z)|^2 = (R^3)⁻¹ int_{A_R} |grad p|^2`.

Multiplying the unit inequality through by `R^3` gives the scale-invariant bound with constant `C`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Short.PartIIIb.Concrete
open scoped Pointwise

theorem annularScaling : UnforcedLeray.Short.PartIIIb.Concrete.AnnPoinSub.AnnularScaling := by
  intro hu
  obtain ⟨C, hC⟩ := hu
  refine ⟨C, fun p hp R hR => ?_⟩
  have hdiff : Differentiable ℝ p := hp.differentiable one_ne_zero
  have hscale : ContDiff ℝ 1 (fun z : UnforcedLeray.Space => R • z) :=
    contDiff_id.const_smul R
  have hqC : ContDiff ℝ 1 (fun z : UnforcedLeray.Space => p (R • z)) := hp.comp hscale
  -- gradient of the rescaled function
  have hgrad : ∀ z : UnforcedLeray.Space,
      physGrad (fun z : UnforcedLeray.Space => p (R • z)) z = R • physGrad p (R • z) := by
    intro z
    have hd : HasFDerivAt (fun z : UnforcedLeray.Space => p (R • z))
        ((fderiv ℝ p (R • z)).comp (R • ContinuousLinearMap.id ℝ UnforcedLeray.Space)) z :=
      (hdiff (R • z)).hasFDerivAt.comp z ((hasFDerivAt_id z).const_smul R)
    ext j
    simp only [physGrad, hd.fderiv, ContinuousLinearMap.comp_apply,
      smul_apply, ContinuousLinearMap.id_apply, map_smul, smul_eq_mul,
      PiLp.smul_apply, PiLp.toLp_apply]
  have hnorm : ∀ z : UnforcedLeray.Space,
      ‖physGrad (fun z : UnforcedLeray.Space => p (R • z)) z‖ ^ 2 =
        R ^ 2 * ‖physGrad p (R • z)‖ ^ 2 := by
    intro z
    rw [hgrad z, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    ring
  -- the scaled annulus
  have hset : R • {z : UnforcedLeray.Space | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 4} =
      {y : UnforcedLeray.Space | R ≤ ‖y‖ ∧ ‖y‖ ≤ 4 * R} := by
    ext y
    rw [mem_smul_set_iff_inv_smul_mem₀ hR.ne']
    simp only [Set.mem_setOf_eq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
    constructor
    · rintro ⟨h1, h2⟩
      have e1 := (le_inv_mul_iff₀ hR).1 h1
      have e2 := (inv_mul_le_iff₀ hR).1 h2
      constructor <;> linarith
    · rintro ⟨h1, h2⟩
      exact ⟨(le_inv_mul_iff₀ hR).2 (by linarith), (inv_mul_le_iff₀ hR).2 (by linarith)⟩
  obtain ⟨m, hm⟩ := hC (fun z : UnforcedLeray.Space => p (R • z)) hqC
  refine ⟨m, ?_⟩
  have hm' := hm
  simp only [hnorm, integral_const_mul] at hm'
  -- change of variables for the two integrals
  have hcov1 : ∫ z in {z : UnforcedLeray.Space | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 4},
      (p (R • z) - m) ^ 2 =
        (R ^ 3)⁻¹ * ∫ y in {y : UnforcedLeray.Space | R ≤ ‖y‖ ∧ ‖y‖ ≤ 4 * R}, (p y - m) ^ 2 := by
    have h := MeasureTheory.Measure.setIntegral_comp_smul_of_pos volume
      (fun y : UnforcedLeray.Space => (p y - m) ^ 2)
      {z : UnforcedLeray.Space | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 4} hR
    rw [finrank_euclideanSpace_fin, hset, smul_eq_mul] at h
    exact h
  have hcov2 : ∫ z in {z : UnforcedLeray.Space | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 4},
      ‖physGrad p (R • z)‖ ^ 2 =
        (R ^ 3)⁻¹ * ∫ y in {y : UnforcedLeray.Space | R ≤ ‖y‖ ∧ ‖y‖ ≤ 4 * R},
          ‖physGrad p y‖ ^ 2 := by
    have h := MeasureTheory.Measure.setIntegral_comp_smul_of_pos volume
      (fun y : UnforcedLeray.Space => ‖physGrad p y‖ ^ 2)
      {z : UnforcedLeray.Space | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 4} hR
    rw [finrank_euclideanSpace_fin, hset, smul_eq_mul] at h
    exact h
  rw [hcov1, hcov2] at hm'
  have hp3 : 0 < R ^ 3 := pow_pos hR 3
  have hinv : R ^ 3 * (R ^ 3)⁻¹ = 1 := mul_inv_cancel₀ hp3.ne'
  calc ∫ y in {y : UnforcedLeray.Space | R ≤ ‖y‖ ∧ ‖y‖ ≤ 4 * R}, (p y - m) ^ 2
      = R ^ 3 * ((R ^ 3)⁻¹ * ∫ y in {y : UnforcedLeray.Space | R ≤ ‖y‖ ∧ ‖y‖ ≤ 4 * R},
          (p y - m) ^ 2) := by
        linear_combination (-(∫ y in {y : UnforcedLeray.Space | R ≤ ‖y‖ ∧ ‖y‖ ≤ 4 * R},
          (p y - m) ^ 2)) * hinv
    _ ≤ R ^ 3 * (C * (R ^ 2 * ((R ^ 3)⁻¹ * ∫ y in {y : UnforcedLeray.Space | R ≤ ‖y‖ ∧ ‖y‖ ≤ 4 * R},
          ‖physGrad p y‖ ^ 2))) := mul_le_mul_of_nonneg_left hm' hp3.le
    _ = C * R ^ 2 * ∫ y in {y : UnforcedLeray.Space | R ≤ ‖y‖ ∧ ‖y‖ ≤ 4 * R},
          ‖physGrad p y‖ ^ 2 := by
        linear_combination (C * R ^ 2 * ∫ y in {y : UnforcedLeray.Space | R ≤ ‖y‖ ∧ ‖y‖ ≤ 4 * R},
          ‖physGrad p y‖ ^ 2) * hinv
