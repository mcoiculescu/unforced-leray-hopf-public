import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_1_3

/-!
# `PartIII-b:C/ward/12/3/1/2/8/2/1/1/3`: order-zero Newton decay of `projPot`

Source `the November 2 reference manuscript`
lines 1393-1400, 1409-1412.  First component of `PiDecay`: `π = projPot Ψ = O((1+|y|)^{-2})`
uniformly in the phase `τ ∈ ℝ`.  Far field from the uniform Newton bounds on `[0,P]`
(`exists_uniform_projectedPotential{Re,Im}Path_far_bound`), periodicity in `τ`, and compactness
of `[0,P] × closedBall 0 T` for the near field.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set Metric
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.PiDecayOrder0Aux

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

/-- `τ ↦ projPot Ψ (τ, y)` is `P`-periodic. -/
theorem projPot_periodic_time {P : ℝ} {Ψ : ℝ × UnforcedLeray.Space → CVec3}
    (hΨ : IsPhaseTest P Ψ) (y : UnforcedLeray.Space) :
    Function.Periodic (fun τ : ℝ => projPot Ψ (τ, y)) P := by
  intro τ
  show projPot Ψ (τ + P, y) = projPot Ψ (τ, y)
  unfold projPot
  rw [projectedPotentialRePath_periodic hΨ τ y, projectedPotentialImPath_periodic hΨ τ y]

/-- Uniform order-zero Newton decay of `projPot`. -/
theorem projPot_decay0_aux {P : ℝ} [Fact (0 < P)] {Ψ : ℝ × UnforcedLeray.Space → CVec3}
    (hΨ : IsPhaseTest P Ψ) :
    ∃ C : ℝ, ∀ τ y, ‖projPot Ψ (τ, y)‖ ≤ C * (1 + ‖y‖) ^ (-2 : ℝ) := by
  obtain ⟨ρ, C0, hρ, hC0, hfar⟩ := exists_uniform_projectedPotentialRePath_far_bound hΨ
  obtain ⟨ρ', C1, hρ', hC1, hfarI⟩ := exists_uniform_projectedPotentialImPath_far_bound hΨ
  set T : ℝ := max (max (2 * ρ) (2 * ρ')) 1 with hT
  have hT1 : 1 ≤ T := le_max_right _ _
  have hT2 : 2 * ρ ≤ T := le_trans (le_max_left _ _) (le_max_left _ _)
  have hT3 : 2 * ρ' ≤ T := le_trans (le_max_right _ _) (le_max_left _ _)
  have hcont : Continuous (fun q : ℝ × UnforcedLeray.Space => ‖projPot Ψ q‖) :=
    (contDiff_projPot hΨ).continuous.norm
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : UnforcedLeray.Space) T)).exists_bound_of_continuousOn
    hcont.continuousOn
  -- reduce a phase to `[0, P)`
  have hred : ∀ τ y, ∃ τ' ∈ Ico (0 : ℝ) P, projPot Ψ (τ', y) = projPot Ψ (τ, y) := by
    intro τ y
    obtain ⟨τ', hτ', h⟩ := (projPot_periodic_time hΨ y).exists_mem_Ico₀ (Fact.out) τ
    exact ⟨τ', hτ', h.symm⟩
  have hnear : ∀ τ y, ‖y‖ ≤ T → ‖projPot Ψ (τ, y)‖ ≤ M := by
    intro τ y hy
    obtain ⟨τ', hτ', hEq⟩ := hred τ y
    have hm := hM (τ', y) ⟨⟨hτ'.1, hτ'.2.le⟩, mem_closedBall_zero_iff.mpr hy⟩
    rw [hEq] at hm
    simpa using hm
  have hfar' : ∀ τ y, T < ‖y‖ → ‖projPot Ψ (τ, y)‖ ≤ (C0 + C1) * (‖y‖ ^ 2)⁻¹ := by
    intro τ y hy
    obtain ⟨τ', hτ', hEq⟩ := hred τ y
    have hy0 : y ≠ 0 := by
      intro h
      rw [h, norm_zero] at hy
      linarith
    have hyR : 2 * ρ ≤ ‖y‖ := le_trans hT2 hy.le
    have hyR' : 2 * ρ' ≤ ‖y‖ := le_trans hT3 hy.le
    have h1 := hfar τ' ⟨hτ'.1, hτ'.2.le⟩ y hyR hy0
    have h2 := hfarI τ' ⟨hτ'.1, hτ'.2.le⟩ y hyR' hy0
    rw [← hEq]
    unfold projPot
    have hnorm : ‖(↑(projectedPotentialRePath Ψ (τ', y)) : ℂ) +
        Complex.I * ↑(projectedPotentialImPath Ψ (τ', y))‖ ≤
        |projectedPotentialRePath Ψ (τ', y)| + |projectedPotentialImPath Ψ (τ', y)| := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
    calc _ ≤ |projectedPotentialRePath Ψ (τ', y)| + |projectedPotentialImPath Ψ (τ', y)| := hnorm
      _ ≤ C0 * (‖y‖ ^ 2)⁻¹ + C1 * (‖y‖ ^ 2)⁻¹ := add_le_add h1 h2
      _ = (C0 + C1) * (‖y‖ ^ 2)⁻¹ := by ring
  refine ⟨max M 0 * (1 + T) ^ 2 + 4 * (C0 + C1), fun τ y => ?_⟩
  have hQ : (1 + ‖y‖) ^ (-2 : ℝ) = ((1 + ‖y‖) ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
  have hQnn : 0 ≤ (1 + ‖y‖) ^ (-2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hC01 : 0 ≤ C0 + C1 := add_nonneg hC0 hC1
  have hmax0 : 0 ≤ max M 0 := le_max_right _ _
  have hmaxM : M ≤ max M 0 := le_max_left _ _
  rcases le_or_gt ‖y‖ T with hy | hy
  · have h := hnear τ y hy
    have hpos : 0 < (1 + ‖y‖) ^ 2 := by positivity
    have hyT : (1 + ‖y‖) ^ 2 ≤ (1 + T) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have hmul := mul_le_mul_of_nonneg_right hyT (inv_nonneg.mpr hpos.le)
    have hone : 1 ≤ (1 + T) ^ 2 * (1 + ‖y‖) ^ (-2 : ℝ) := by
      rw [hQ]
      linarith [mul_inv_cancel₀ hpos.ne']
    calc ‖projPot Ψ (τ, y)‖ ≤ M := h
      _ ≤ max M 0 * ((1 + T) ^ 2 * (1 + ‖y‖) ^ (-2 : ℝ)) := by
          nlinarith [mul_le_mul_of_nonneg_left hone hmax0]
      _ ≤ (max M 0 * (1 + T) ^ 2 + 4 * (C0 + C1)) * (1 + ‖y‖) ^ (-2 : ℝ) := by
          nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 4 * (C0 + C1)) hQnn]
  · have h := hfar' τ y hy
    have hy1 : 1 ≤ ‖y‖ := by linarith [hT1]
    have hinv : (‖y‖ ^ 2)⁻¹ ≤ 4 * ((1 + ‖y‖) ^ 2)⁻¹ := by
      have hA : 0 < ‖y‖ ^ 2 := by positivity
      have hB : 0 < (1 + ‖y‖) ^ 2 := by positivity
      rw [inv_eq_one_div, inv_eq_one_div, ← sub_nonneg]
      have hid : 4 * (1 / (1 + ‖y‖) ^ 2) - 1 / ‖y‖ ^ 2 =
          (4 * ‖y‖ ^ 2 - (1 + ‖y‖) ^ 2) / ((1 + ‖y‖) ^ 2 * ‖y‖ ^ 2) := by
        field_simp
      rw [hid]
      apply div_nonneg
      · nlinarith
      · positivity
    calc ‖projPot Ψ (τ, y)‖ ≤ (C0 + C1) * (‖y‖ ^ 2)⁻¹ := h
      _ ≤ (C0 + C1) * (4 * (1 + ‖y‖) ^ (-2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (by rw [hQ]; exact hinv) hC01
      _ ≤ (max M 0 * (1 + T) ^ 2 + 4 * (C0 + C1)) * (1 + ‖y‖) ^ (-2 : ℝ) := by
          nlinarith [mul_nonneg (mul_nonneg hmax0 (by positivity : (0:ℝ) ≤ (1 + T) ^ 2)) hQnn]

end UnforcedLeray.Short.PartIIIb.Concrete.PiDecayOrder0Aux
