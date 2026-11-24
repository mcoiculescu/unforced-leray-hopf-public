import UnforcedLeray.Lib.HeatR3.SimContinuity
import UnforcedLeray.Lib.HeatR3.Smoothing

/-!
# Solenoidality of the similarity heat profile (INF04 T10, `simHeat_solenoidal`)


item `simHeat_solenoidal`. Unit B0697 (tex 5923–5934, "`H_a` is solenoidal") and the profile of
`loc:eq:dss` (tex 150–163, "`u_dss` solenoidal").

For `u ∈ 𝒦₁(C)` (`C¹` off `0`, `|u| ≤ C|x|^{-1}`, `|Du| ≤ C|x|^{-2}`) with `div u = 0` off `0`,
the heat flow `e^{tΔ}u` is divergence free (`spaceDiv_average_eq_zero`). The singularity
carries no flux (`|u| ≤ C|x|^{-1}` against the area `|x|²`), and the proof makes this
quantitative with the cutoff `φ_ε = cut(·/ε)` of `HeatDecay` (`1` on `B_ε`, `0` off `B_{2ε}`):
* near part `φ_ε u`: `|div e^{tΔ}(φ_ε u)(x)| ≤ 3‖DG_t‖_∞ C ∫_{B_{2ε}} |y|^{-1} dy → 0`;
* far part `(1 - φ_ε)u ∈ C¹_b`: `div e^{tΔ}((1-φ_ε)u) = e^{tΔ}(-∇φ_ε · u)` (`spaceDiv_average`),
  and `|∇φ_ε · u| ≤ 3Bε^{-1}·Cε^{-1}` on `B_{2ε}`, so its heat flow is
  `≤ ‖G_t‖_∞ 3BCε^{-2}|B_{2ε}| = O(ε)`.
Letting `ε → 0` gives `div e^{tΔ}u = 0`; the profile `H_h[u](τ) = e^{τ/2}e^{he^τΔ}u(e^{τ/2}·)`
inherits it (`simHeat_solenoidal`).
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology Metric
open scoped ENNReal ContDiff

/-! ### Divergence: additivity and rescaling -/

theorem spaceDiv_add {F G : SpatialField} {x : Space} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) : spaceDiv (F + G) x = spaceDiv F x + spaceDiv G x := by
  have e : fderiv ℝ (F + G) x = fderiv ℝ F x + fderiv ℝ G x :=
    (hF.hasFDerivAt.add hG.hasFDerivAt).fderiv
  simp only [spaceDiv, e, ContinuousLinearMap.add_apply, PiLp.add_apply, Finset.sum_add_distrib]

theorem spaceDiv_rescale {F : SpatialField} {a : ℝ} {y : Space}
    (hF : DifferentiableAt ℝ F (a • y)) :
    spaceDiv (fun z => a • F (a • z)) y = (a * a) * spaceDiv F (a • y) := by
  simp only [spaceDiv, fderiv_rescale_apply hF, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]

/-! ### The cutoff at scale `ε` -/

theorem cut_scale_eq_one {ε : ℝ} (hε : 0 < ε) {y : Space} (hy : ‖y‖ ≤ ε) :
    cut (ε⁻¹ • y) = 1 := by
  apply cut_eq_one
  rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hε).le, inv_mul_le_iff₀ hε, mul_one]
  exact hy

theorem cut_scale_eq_zero {ε : ℝ} (hε : 0 < ε) {y : Space} (hy : 2 * ε ≤ ‖y‖) :
    cut (ε⁻¹ • y) = 0 := by
  apply cut_eq_zero
  rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hε).le, le_inv_mul_iff₀ hε]
  linarith

theorem contDiff_cut_scale (ε : ℝ) : ContDiff ℝ ∞ (fun y : Space => cut (ε⁻¹ • y)) :=
  contDiff_cut.comp (contDiff_const_smul _)

theorem norm_fderiv_cut_scale_le {ε : ℝ} (hε : 0 < ε) {B : ℝ}
    (hB : ∀ y, ‖iteratedFDeriv ℝ 1 cut y‖ ≤ B) (y : Space) :
    ‖fderiv ℝ (fun z : Space => cut (ε⁻¹ • z)) y‖ ≤ B * ε⁻¹ := by
  have hd : DifferentiableAt ℝ cut (ε⁻¹ • y) :=
    (contDiff_cut.differentiable (by simp)) _
  have h : HasFDerivAt (fun z : Space => cut (ε⁻¹ • z))
      ((fderiv ℝ cut (ε⁻¹ • y)).comp (ε⁻¹ • ContinuousLinearMap.id ℝ Space)) y :=
    hd.hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul ε⁻¹)
  rw [h.fderiv]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h1 : ‖fderiv ℝ cut (ε⁻¹ • y)‖ ≤ B := by
    rw [← norm_iteratedFDeriv_one]; exact hB _
  have h2 : ‖ε⁻¹ • ContinuousLinearMap.id ℝ Space‖ ≤ ε⁻¹ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hε).le]
    exact mul_le_of_le_one_right (inv_pos.mpr hε).le ContinuousLinearMap.norm_id_le
  exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)

theorem fderiv_cut_scale_eq_zero {ε : ℝ} (hε : 0 < ε) {y : Space}
    (hy : ‖y‖ < ε ∨ 2 * ε < ‖y‖) : fderiv ℝ (fun z : Space => cut (ε⁻¹ • z)) y = 0 := by
  rcases hy with hy | hy
  · have h : (fun z : Space => cut (ε⁻¹ • z)) =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hy] with z hz
      exact cut_scale_eq_one hε (le_of_lt hz)
    rw [h.fderiv_eq, fderiv_const_apply]
  · have h : (fun z : Space => cut (ε⁻¹ • z)) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with z hz
      exact cut_scale_eq_zero hε (le_of_lt hz)
    rw [h.fderiv_eq, fderiv_const_apply]

/-! ### The far part `(1 - φ_ε) u` -/

section Far

variable {C : ℝ} {u : SpatialField} (hu : InvDistClass 1 C u) {ε : ℝ} (hε : 0 < ε)
include hu hε

theorem scaleFar_eq_zero_of_lt {y : Space} (hy : ‖y‖ < ε) :
    (1 - cut (ε⁻¹ • y)) • u y = 0 := by
  rw [cut_scale_eq_one hε hy.le, sub_self, zero_smul]

theorem scaleFar_eventually_zero {y : Space} (hy : ‖y‖ < ε) :
    (fun z => (1 - cut (ε⁻¹ • z)) • u z) =ᶠ[𝓝 y] fun _ => (0 : Space) := by
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hy] with z hz
  exact scaleFar_eq_zero_of_lt hu hε hz

theorem hasFDerivAt_scaleFar {y : Space} (hy : y ≠ 0) :
    HasFDerivAt (fun z => (1 - cut (ε⁻¹ • z)) • u z)
      ((1 - cut (ε⁻¹ • y)) • fderiv ℝ u y +
        (-fderiv ℝ (fun z : Space => cut (ε⁻¹ • z)) y).smulRight (u y)) y := by
  have hφ : HasFDerivAt (fun z : Space => 1 - cut (ε⁻¹ • z))
      (-fderiv ℝ (fun z : Space => cut (ε⁻¹ • z)) y) y :=
    (((contDiff_cut_scale ε).differentiable (by simp)) y).hasFDerivAt.const_sub 1
  have hud : DifferentiableAt ℝ u y :=
    (hu.contDiffAt hy).differentiableAt (by simp)
  exact hφ.fun_smul hud.hasFDerivAt

theorem contDiff_scaleFar : ContDiff ℝ 1 (fun z => (1 - cut (ε⁻¹ • z)) • u z) := by
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  by_cases hy : ‖y‖ < ε
  · exact contDiffAt_const.congr_of_eventuallyEq (scaleFar_eventually_zero hu hε hy)
  · have hy0 : y ≠ 0 := fun h => hy (by rw [h, norm_zero]; exact hε)
    have h1 : ContDiffAt ℝ 1 (fun z : Space => 1 - cut (ε⁻¹ • z)) y :=
      (contDiff_const.sub ((contDiff_cut_scale ε).of_le (by simp))).contDiffAt
    have h2 : ContDiffAt ℝ 1 u y := by exact_mod_cast hu.contDiffAt hy0
    exact h1.smul h2

theorem abs_one_sub_cut_scale_le (y : Space) : |1 - cut (ε⁻¹ • y)| ≤ 1 := by
  have h0 := cut_nonneg (ε⁻¹ • y)
  have h1 := cut_le_one (ε⁻¹ • y)
  rw [abs_le]; constructor <;> linarith

end Far

/-! ### Divergence of the heat flow -/

/-- **Solenoidality is preserved by the heat flow of singular data.** For `u ∈ 𝒦₁(C)` with
`div u = 0` off the origin and `t > 0`: `div e^{tΔ}u = 0` everywhere (B0697). -/
theorem spaceDiv_average_eq_zero {C : ℝ} {u : SpatialField} (hu : InvDistClass 1 C u)
    (hdiv : ∀ x : Space, x ≠ 0 → spaceDiv u x = 0) {t : ℝ} (ht : 0 < t) (x : Space) :
    spaceDiv (average t u) x = 0 := by
  have hC : 0 ≤ C := hu.const_nonneg'
  -- constants: `‖DG_t‖ ≤ M1`, `G_t ≤ K0`, `‖Dcut‖ ≤ B`
  obtain ⟨M1, hM1pos, hM1⟩ := norm_iteratedFDeriv_gaussKernel_le_weight 3 1 ht (m := 0) le_rfl
  have hM1' : ∀ z : Space, ‖fderiv ℝ (kernel t) z‖ ≤ M1 := fun z => by
    have := hM1 z
    rwa [neg_zero, Real.rpow_zero, mul_one, norm_iteratedFDeriv_one,
      Gaussian.gaussKernel_three_eq] at this
  set K0 := (4 * Real.pi * t) ^ (-((3 : ℕ) : ℝ) / 2)
  have hK0 : ∀ z, kernel t z ≤ K0 := fun z => by
    have := Gaussian.gaussKernel_le (d := 3) ht z
    rwa [Gaussian.gaussKernel_three_eq] at this
  have hK00 : 0 ≤ K0 := (kernel_nonneg ht 0).trans (hK0 0)
  obtain ⟨B, hB0, hB⟩ := cut_deriv_bound 1
  -- the volume of balls
  set V1 := (volume (ball (0 : Space) 1)).toReal
  have hvol : ∀ r : ℝ, 0 ≤ r → (volume (closedBall (0 : Space) r)).toReal = r ^ 3 * V1 := by
    intro r hr
    rw [Measure.addHaar_closedBall volume (0 : Space) hr, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), show Module.finrank ℝ Space = 3 by simp [Space]]
  set I : ℝ → ℝ := fun r => ∫ y in closedBall (0 : Space) r, ‖y‖ ^ (-(1 : ℝ))
  -- the estimate at scale `ε`
  have key : ∀ ε : ℝ, 0 < ε → 2 * ε ≤ 1 →
      |spaceDiv (average t u) x| ≤ 3 * (M1 * (C * I (2 * ε))) +
        K0 * (3 * B * C * ε⁻¹ ^ 2 * (8 * ε ^ 3 * V1)) := by
    intro ε hε hε1
    set φ : Space → ℝ := fun y => cut (ε⁻¹ • y)
    set nr : SpatialField := fun y => φ y • u y
    set fr : SpatialField := fun y => (1 - φ y) • u y
    have hum : AEStronglyMeasurable u volume := hu.heatAdmissible.1
    have hφc : Continuous φ := (contDiff_cut_scale ε).continuous
    have hnr : HeatAdmissible nr := by
      refine HeatAdmissible.of_inv_bound (hφc.aestronglyMeasurable.smul hum) (C := C)
        fun y hy => ?_
      rw [norm_smul, Real.norm_of_nonneg (cut_nonneg _)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (cut_le_one _)).trans (hu.norm_le' hy)
    have hfr : HeatAdmissible fr := by
      refine HeatAdmissible.of_inv_bound
        ((continuous_const.sub hφc).aestronglyMeasurable.smul hum) (C := C) fun y hy => ?_
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_of_le_one_left (norm_nonneg _) (abs_one_sub_cut_scale_le hu hε y)).trans
        (hu.norm_le' hy)
    have hsplit : average t u = average t nr + average t fr := by
      rw [← average_add' hnr hfr ht]
      congr 1
      funext y
      simp only [nr, fr, Pi.add_apply, ← add_smul, add_sub_cancel, one_smul]
    have hdnr : DifferentiableAt ℝ (average t nr) x :=
      ((contDiff_average hnr ht).differentiable (by simp)) x
    have hdfr : DifferentiableAt ℝ (average t fr) x :=
      ((contDiff_average hfr ht).differentiable (by simp)) x
    rw [hsplit, spaceDiv_add hdnr hdfr]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · -- near part
      set g : Space → ℝ := (closedBall (0 : Space) (2 * ε)).indicator
        (fun y => C * ‖y‖ ^ (-(1 : ℝ)))
      have hgi : Integrable g := by
        refine IntegrableOn.integrable_indicator ?_ measurableSet_closedBall
        exact (integrableOn_inv_norm_closedBall.mono_set
          (closedBall_subset_closedBall hε1)).const_mul C
      have hgint : ∫ y, g y = C * I (2 * ε) := by
        rw [integral_indicator measurableSet_closedBall, integral_const_mul]
      have hnrb : ∀ y : Space, y ≠ 0 → ‖nr y‖ ≤ g y := by
        intro y hy
        simp only [g]
        by_cases hyb : y ∈ closedBall (0 : Space) (2 * ε)
        · rw [indicator_of_mem hyb, norm_smul, Real.norm_of_nonneg (cut_nonneg _),
            Real.rpow_neg_one]
          exact (mul_le_of_le_one_left (norm_nonneg _) (cut_le_one _)).trans (hu.norm_le' hy)
        · rw [indicator_of_notMem hyb]
          have : 2 * ε ≤ ‖y‖ := by
            rw [mem_closedBall, dist_zero_right, not_le] at hyb; exact hyb.le
          simp only [nr, φ, cut_scale_eq_zero hε this, zero_smul, norm_zero, le_refl]
      have hcomp : ∀ i : Fin 3, |(fderiv ℝ (average t nr) x (coordinateVector i)) i| ≤
          M1 * (C * I (2 * ε)) := by
        intro i
        rw [fderiv_average_apply hnr ht x, ← Real.norm_eq_abs]
        refine (PiLp.norm_apply_le _ i).trans ?_
        rw [← hgint, ← integral_const_mul]
        refine norm_integral_le_of_norm_le (hgi.const_mul M1) ?_
        filter_upwards [Measure.ae_ne volume (0 : Space)] with y hy
        rw [norm_smul]
        refine mul_le_mul ?_ (hnrb y hy) (norm_nonneg _) (by positivity)
        refine ((fderiv ℝ (kernel t) (x - y)).le_opNorm _).trans ?_
        rw [norm_coordinateVector, mul_one]
        exact hM1' _
      calc |spaceDiv (average t nr) x|
          ≤ ∑ i : Fin 3, |(fderiv ℝ (average t nr) x (coordinateVector i)) i| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin 3, M1 * (C * I (2 * ε)) := Finset.sum_le_sum fun i _ => hcomp i
        _ = 3 * (M1 * (C * I (2 * ε))) := by simp
    · -- far part
      have hfc := contDiff_scaleFar hu hε
      have hfr0 : ∀ y, ‖fr y‖ ≤ C * ε⁻¹ := by
        intro y
        by_cases hy : ‖y‖ < ε
        · rw [show fr y = 0 from scaleFar_eq_zero_of_lt hu hε hy, norm_zero]; positivity
        · have hy0 : y ≠ 0 := fun h => hy (by rw [h, norm_zero]; exact hε)
          rw [norm_smul, Real.norm_eq_abs]
          refine (mul_le_of_le_one_left (norm_nonneg _) (abs_one_sub_cut_scale_le hu hε y)).trans
            ((hu.norm_le' hy0).trans ?_)
          gcongr
          exact not_lt.mp hy
      have hφd : ∀ y, ‖fderiv ℝ φ y‖ ≤ B * ε⁻¹ := norm_fderiv_cut_scale_le hε hB
      have hfr1 : ∀ y, ‖fderiv ℝ fr y‖ ≤ C * ε ^ (-(1 + 1 : ℝ)) + B * ε⁻¹ * (C * ε⁻¹) := by
        intro y
        by_cases hy : ‖y‖ < ε
        · rw [(scaleFar_eventually_zero hu hε hy).fderiv_eq, fderiv_const_apply, norm_zero]
          positivity
        · have hy' : ε ≤ ‖y‖ := not_lt.mp hy
          have hy0 : y ≠ 0 := fun h => hy (by rw [h, norm_zero]; exact hε)
          rw [(hasFDerivAt_scaleFar hu hε hy0).fderiv]
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_smul, Real.norm_eq_abs]
            refine (mul_le_of_le_one_left (norm_nonneg _) (abs_one_sub_cut_scale_le hu hε y)).trans ?_
            have h1 := hu.bound 1 le_rfl y hy0
            rw [norm_iteratedFDeriv_one, Nat.cast_one] at h1
            exact h1.trans (mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_nonpos (z := -(1 + 1 : ℝ)) hε hy' (by norm_num)) hC)
          · rw [ContinuousLinearMap.norm_smulRight_apply, norm_neg]
            refine mul_le_mul (hφd y) ((hu.norm_le' hy0).trans ?_) (norm_nonneg _)
              (by positivity)
            gcongr
      set Mf := C * ε⁻¹ + (C * ε ^ (-(1 + 1 : ℝ)) + B * ε⁻¹ * (C * ε⁻¹))
      have hMf0 : 0 ≤ C * ε ^ (-(1 + 1 : ℝ)) + B * ε⁻¹ * (C * ε⁻¹) := by positivity
      have hb0 : ∀ y, ‖fr y‖ ≤ Mf := fun y => (hfr0 y).trans (le_add_of_nonneg_right hMf0)
      have hb1 : ∀ y, ‖fderiv ℝ fr y‖ ≤ Mf := fun y =>
        (hfr1 y).trans (le_add_of_nonneg_left (by positivity))
      rw [spaceDiv_average ht hfc hb0 hb1 x]
      -- the divergence of the far part
      set b : Space → ℝ := (closedBall (0 : Space) (2 * ε)).indicator
        (fun _ => 3 * B * C * ε⁻¹ ^ 2)
      have hdivb : ∀ z, |spaceDiv fr z| ≤ b z := by
        intro z
        have hb0' : 0 ≤ b z := by
          simp only [b]; exact indicator_nonneg (fun _ _ => by positivity) _
        by_cases hz : ‖z‖ < ε
        · have : fderiv ℝ fr z = 0 := by
            rw [(scaleFar_eventually_zero hu hε hz).fderiv_eq, fderiv_const_apply]
          simp only [spaceDiv, this, ContinuousLinearMap.zero_apply, PiLp.zero_apply,
            Finset.sum_const_zero, abs_zero]
          exact hb0'
        have hz' : ε ≤ ‖z‖ := not_lt.mp hz
        have hz0 : z ≠ 0 := fun h => hz (by rw [h, norm_zero]; exact hε)
        have hform : spaceDiv fr z = (1 - φ z) * spaceDiv u z +
            ∑ i : Fin 3, (-(fderiv ℝ φ z (coordinateVector i))) * (u z) i := by
          unfold spaceDiv
          rw [show fderiv ℝ fr z = _ from (hasFDerivAt_scaleFar hu hε hz0).fderiv]
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.neg_apply, PiLp.add_apply,
            PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum]
          rfl
        rw [hform, hdiv z hz0, mul_zero, zero_add]
        have hterm : ∀ i : Fin 3, |(-(fderiv ℝ φ z (coordinateVector i))) * (u z) i| ≤
            ‖fderiv ℝ φ z‖ * ‖u z‖ := by
          intro i
          rw [abs_mul, abs_neg]
          refine mul_le_mul ?_ ?_ (abs_nonneg _) (norm_nonneg _)
          · rw [← Real.norm_eq_abs]
            refine ((fderiv ℝ φ z).le_opNorm _).trans ?_
            rw [norm_coordinateVector, mul_one]
          · rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le _ i
        refine (Finset.abs_sum_le_sum_abs _ _).trans
          ((Finset.sum_le_sum fun i _ => hterm i).trans ?_)
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        by_cases hz2 : 2 * ε < ‖z‖
        · rw [show fderiv ℝ φ z = 0 from fderiv_cut_scale_eq_zero hε (Or.inr hz2), norm_zero,
            zero_mul, mul_zero]
          exact hb0'
        · have hzb : z ∈ closedBall (0 : Space) (2 * ε) := by
            rw [mem_closedBall, dist_zero_right]; exact not_lt.mp hz2
          simp only [b, indicator_of_mem hzb]
          have hu1 : ‖u z‖ ≤ C * ε⁻¹ :=
            (hu.norm_le' hz0).trans (by gcongr)
          calc (3 : ℕ) * (‖fderiv ℝ φ z‖ * ‖u z‖) ≤ 3 * (B * ε⁻¹ * (C * ε⁻¹)) := by
                push_cast
                gcongr
                exact hφd z
            _ = 3 * B * C * ε⁻¹ ^ 2 := by ring
      have hbi : Integrable b := by
        refine (integrableOn_const ?_).integrable_indicator measurableSet_closedBall
        exact (measure_closedBall_lt_top).ne
      have hbint : ∫ z, b z = 3 * B * C * ε⁻¹ ^ 2 * (8 * ε ^ 3 * V1) := by
        rw [integral_indicator measurableSet_closedBall, setIntegral_const, smul_eq_mul,
          Measure.real, hvol (2 * ε) (by positivity)]
        ring
      rw [← Real.norm_eq_abs, average]
      calc ‖∫ y : Space, kernel t y • spaceDiv fr (x - y)‖
          ≤ ∫ y : Space, K0 * b (x - y) := by
            refine norm_integral_le_of_norm_le ((hbi.comp_sub_left x).const_mul K0)
              (Eventually.of_forall fun y => ?_)
            rw [norm_smul, Real.norm_of_nonneg (kernel_nonneg ht y), Real.norm_eq_abs]
            exact mul_le_mul (hK0 y) (hdivb _) (abs_nonneg _) hK00
        _ = K0 * (3 * B * C * ε⁻¹ ^ 2 * (8 * ε ^ 3 * V1)) := by
            rw [integral_const_mul, integral_sub_left_eq_self (fun z => b z) volume x, hbint]
  -- letting `ε → 0`
  set ε : ℕ → ℝ := fun n => 1 / (2 * ((n : ℝ) + 1))
  have hεpos : ∀ n, 0 < ε n := fun n => by positivity
  have hε1 : ∀ n, 2 * ε n ≤ 1 := fun n => by
    simp only [ε]
    rw [mul_one_div, div_le_one (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h2ε : ∀ n, 2 * ε n = 1 / ((n : ℝ) + 1) := fun n => by
    simp only [ε]; field_simp
  -- the near term tends to zero
  have hI : Tendsto (fun n : ℕ => I (2 * ε n)) atTop (𝓝 0) := by
    have hanti : Antitone fun n : ℕ => closedBall (0 : Space) (1 / ((n : ℝ) + 1)) := by
      intro m n hmn
      apply closedBall_subset_closedBall
      apply one_div_le_one_div_of_le (by positivity)
      have : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
      linarith
    have h := tendsto_setIntegral_of_antitone (μ := (volume : Measure Space))
      (f := fun y : Space => ‖y‖ ^ (-(1 : ℝ))) (fun n => measurableSet_closedBall) hanti
      ⟨0, by simpa using integrableOn_inv_norm_closedBall⟩
    have hnull : volume (⋂ n : ℕ, closedBall (0 : Space) (1 / ((n : ℝ) + 1))) = 0 := by
      refine measure_mono_null (fun y hy => ?_) (measure_singleton (0 : Space))
      rw [mem_iInter] at hy
      rw [mem_singleton_iff, ← norm_eq_zero]
      by_contra hne
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr (norm_ne_zero_iff.mp hne))
      have := hy n
      rw [mem_closedBall, dist_zero_right] at this
      linarith
    rw [setIntegral_measure_zero _ hnull] at h
    simp only [I, h2ε]
    exact h
  -- the far term tends to zero
  have hfar : Tendsto (fun n : ℕ => K0 * (3 * B * C * (ε n)⁻¹ ^ 2 * (8 * ε n ^ 3 * V1)))
      atTop (𝓝 0) := by
    have he : ∀ n, K0 * (3 * B * C * (ε n)⁻¹ ^ 2 * (8 * ε n ^ 3 * V1)) =
        (24 * K0 * B * C * V1) * ε n := fun n => by
      have := (hεpos n).ne'
      field_simp
      ring
    simp_rw [he]
    have hε0 : Tendsto ε atTop (𝓝 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (1 / 2 : ℝ)
      rw [mul_zero] at h
      refine h.congr fun n => ?_
      simp only [ε]; field_simp
    simpa using hε0.const_mul (24 * K0 * B * C * V1)
  have hlim := ((hI.const_mul C).const_mul M1 |>.const_mul 3).add hfar
  simp only [mul_zero, add_zero] at hlim
  have hle : |spaceDiv (average t u) x| ≤ 0 :=
    ge_of_tendsto' hlim fun n => key (ε n) (hεpos n) (hε1 n)
  exact abs_nonpos_iff.mp hle

/-- **INF04 T10 `simHeat_solenoidal`** (B0697, tex 5923–5934: "`H_a` is solenoidal"). For
`h > 0` and `u ∈ 𝒦₁(C)` with `div u = 0` off the origin, the profile `H_h[u](τ)` is divergence
free at every phase and every point. -/
theorem simHeat_solenoidal {h : ℝ} (hh : 0 < h) {C : ℝ} {u : SpatialField}
    (hu : InvDistClass 1 C u) (hdiv : ∀ x : Space, x ≠ 0 → spaceDiv u x = 0) (τ : ℝ)
    (y : Space) : spaceDiv (simHeat h u τ) y = 0 := by
  have hT : 0 < h * Real.exp τ := mul_pos hh (Real.exp_pos τ)
  have hfun : simHeat h u τ = fun z => Real.exp (τ / 2) • average (h * Real.exp τ) u
      (Real.exp (τ / 2) • z) := rfl
  have hd : DifferentiableAt ℝ (average (h * Real.exp τ) u) (Real.exp (τ / 2) • y) :=
    ((contDiff_average hu.heatAdmissible hT).differentiable (by simp)) _
  rw [hfun, spaceDiv_rescale hd, spaceDiv_average_eq_zero hu hdiv hT, mul_zero]

end UnforcedLeray.Heat
