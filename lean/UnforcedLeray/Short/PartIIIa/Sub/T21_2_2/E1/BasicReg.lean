import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.HigherReg.Transfer
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.Cont.Age

/-!
# `PartIII-a:T21/2/2/3/3`: low-order regularity of the moving adjoint (SP 3036-3047, 3060)

The moving slice `Φ = movingPhi ν φ r` (`a = clockA ν r`, `d = c/√a`) is smooth and `d`-periodic
(`IsAdjointFlow.periodic` with `√a d = c`), and its `L²` integrability against `p_d⁻¹` on the cell
follows from `memX` and `memH1` by the scaling `x = √a y` (`transfer_weight_int`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff
open Real

namespace UnforcedLeray.Short.IIIa.AdjE1

theorem movAdjBasicReg (m : ℝ) (hm : 8 < m) : MovAdjBasicReg m := by
  intro ν tr t s φ ζ hF
  obtain ⟨hν, ht, hts, ⟨G, _hG, hflow⟩, hζ⟩ := hF
  have hr : revAge ν s ζ ∈ Ico t s := (adjAgeMap ν t s hν ht hts).2.2 (Ioo_subset_Ioc_self hζ)
  have hm0 : 0 ≤ m := by linarith
  have hc : 0 < ν ^ (-2 : ℝ) := by positivity
  have ha : 0 < clockA ν (revAge ν s ζ) := by
    have h0 : 0 ≤ revAge ν s ζ := ht.trans hr.1
    unfold clockA
    nlinarith [mul_nonneg hν.le h0]
  have hR : 0 < Real.sqrt (clockA ν (revAge ν s ζ)) := Real.sqrt_pos.2 ha
  have hφ : ContDiff ℝ ∞ (φ (revAge ν s ζ)) := hflow.smooth _ hr
  unfold mvPhi mvLen cellLen
  set r := revAge ν s ζ with hr_def
  have hnorm : ∀ y : ℝ × ℝ,
      ‖movingPhi ν φ r y‖ ^ 2 = ((clockA ν r)⁻¹) ^ 2 * ‖φ r (Real.sqrt (clockA ν r) • y)‖ ^ 2 := by
    intro y
    unfold movingPhi
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    rfl
  have hnorm1 : ∀ (k : Fin 2) (y : ℝ × ℝ),
      ‖pdCx k (movingPhi ν φ r) y‖ ^ 2 =
        ((clockA ν r)⁻¹ * Real.sqrt (clockA ν r)) ^ 2 *
          ‖pdCx k (φ r) (Real.sqrt (clockA ν r) • y)‖ ^ 2 := by
    intro k y
    rw [pdCx_movingPhi ν φ r hφ k y]
    have e : (((clockA ν r)⁻¹ : ℝ) : ℂ) * ((Real.sqrt (clockA ν r) : ℝ) : ℂ) *
        pdCx k (φ r) (Real.sqrt (clockA ν r) • y) =
        ((((clockA ν r)⁻¹ * Real.sqrt (clockA ν r)) : ℝ) : ℂ) *
          pdCx k (φ r) (Real.sqrt (clockA ν r) • y) := by
      push_cast
      ring
    rw [e, norm_sq_real_const_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [movingPhi_eq_comp]
    exact contDiff_const.mul (hφ.comp (contDiff_const_smul _))
  · intro y
    unfold movingPhi
    have hsq : Real.sqrt (clockA ν r) * (ν ^ (-2 : ℝ) / Real.sqrt (clockA ν r)) = ν ^ (-2 : ℝ) := by
      field_simp
    rw [mul_add, hsq]
    congr 1
    exact hflow.periodic r hr (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)
  · have h0 := (transfer_weight_int m (ν ^ (-2 : ℝ)) (Real.sqrt (clockA ν r)) hm0 hc hR
      (φ r) (hflow.memX r (Ico_subset_Icc_self hr))).const_mul (((clockA ν r)⁻¹) ^ 2)
    refine IntegrableOn.congr_fun h0 (fun y _ => ?_) (B0579.measurableSet_cell _)
    rw [hnorm y]
    ring
  · intro k
    have hH : MemLp (pdCx k (φ r)) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
      hflow.memH1 r hr k
    have h1 := (transfer_weight_int m (ν ^ (-2 : ℝ)) (Real.sqrt (clockA ν r)) hm0 hc hR
      (pdCx k (φ r)) hH).const_mul (((clockA ν r)⁻¹ * Real.sqrt (clockA ν r)) ^ 2)
    refine IntegrableOn.congr_fun h1 (fun y _ => ?_) (B0579.measurableSet_cell _)
    rw [hnorm1 k y]
    ring

end UnforcedLeray.Short.IIIa.AdjE1
