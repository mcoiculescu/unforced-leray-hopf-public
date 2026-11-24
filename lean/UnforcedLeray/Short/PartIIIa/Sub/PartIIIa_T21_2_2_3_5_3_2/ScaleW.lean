import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_5_3_2

/-!
# `PartIII-a:T21/2/2/3/5/3/2` leaf `E1ScaleW`: change of variables in the weight-derivative term

Source of record: `the November 2 reference manuscript` (SP) lines 2860-2864,
3036-3037. With `x = √a y`: `∂_r physW(r, √a y) = -a⁻²(dtW + (β/2) y·∇w)(y)` (`PhysWDeriv`),
`|∂_kφ(r, √a y)|² = a |∂_kΦ(y)|²` (`norm_pdCx_movingPhi_sq`), and `∫_{C_c} = a ∫_{C_d}` of the
rescaled integrand (`integral_cell_scale`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

open UnforcedLeray.Short.IIIa

theorem e1ScaleW (m : ℝ) : E1ScaleW m := by
  unfold E1ScaleW
  intro hD ν tr t s φ ζ hζ k
  obtain ⟨hr, ha⟩ := adjFlowAt_age hζ
  have ht0 : 0 ≤ t := hζ.2.1
  have hν : 0 < ν := hζ.1
  obtain ⟨_, _, _, ⟨G, _, hF⟩, _⟩ := hζ
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hr0 : 0 ≤ revAge ν s ζ := le_trans ht0 hr.1.le
  have hφ : ContDiff ℝ ∞ (φ (revAge ν s ζ)) := hF.smooth _ (Ioo_subset_Ico_self hr)
  have hs : 0 < Real.sqrt (clockA ν (revAge ν s ζ)) := Real.sqrt_pos.mpr ha
  have hs' : Real.sqrt (clockA ν (revAge ν s ζ)) ≠ 0 := hs.ne'
  have ha' : clockA ν (revAge ν s ζ) ≠ 0 := ha.ne'
  have hmi : clockA ν (revAge ν s ζ) * (clockA ν (revAge ν s ζ))⁻¹ = 1 := mul_inv_cancel₀ ha'
  have hinv : (clockA ν (revAge ν s ζ))⁻¹ * clockA ν (revAge ν s ζ) = 1 := inv_mul_cancel₀ ha'
  simp only [mvLen, mvBeta, mvPhi]
  have key : ∀ y : ℝ × ℝ,
      deriv (fun r' => physW ν (ν ^ (-2 : ℝ)) m r'
          (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2))
          (revAge ν s ζ) *
        ‖pdCx k (φ (revAge ν s ζ))
          (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)‖ ^ 2
      = -((clockA ν (revAge ν s ζ))⁻¹) *
          ((dtW m (cellLen (ν ^ (-2 : ℝ)) (clockA ν (revAge ν s ζ))) (ν * clockA ν (revAge ν s ζ)) y +
              ν * clockA ν (revAge ν s ζ) / 2 *
                (y.1 * B0579.pd 0 (periodicWeight (-m) (cellLen (ν ^ (-2 : ℝ)) (clockA ν (revAge ν s ζ)))) y +
                  y.2 * B0579.pd 1 (periodicWeight (-m) (cellLen (ν ^ (-2 : ℝ)) (clockA ν (revAge ν s ζ)))) y)) *
            ‖pdCx k (movingPhi ν φ (revAge ν s ζ)) y‖ ^ 2) := by
    intro y
    have hx : ((Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
        Real.sqrt (clockA ν (revAge ν s ζ)) * y.2) : ℝ × ℝ) =
        Real.sqrt (clockA ν (revAge ν s ζ)) • y := by
      ext <;> simp [smul_eq_mul]
    have h := norm_pdCx_movingPhi_sq hν hr0 hφ k y
    rw [hx] at h
    have hn : ‖pdCx k (φ (revAge ν s ζ)) (Real.sqrt (clockA ν (revAge ν s ζ)) • y)‖ ^ 2 =
        clockA ν (revAge ν s ζ) * ‖pdCx k (movingPhi ν φ (revAge ν s ζ)) y‖ ^ 2 := by
      linear_combination (-(clockA ν (revAge ν s ζ))) * h -
        (‖pdCx k (φ (revAge ν s ζ)) (Real.sqrt (clockA ν (revAge ν s ζ)) • y)‖ ^ 2) * hmi
    rw [hx, hD ν (ν ^ (-2 : ℝ)) (revAge ν s ζ) y hc ha, hn]
    field_simp
  have hcs : ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (revAge ν s ζ))),
      deriv (fun r' => physW ν (ν ^ (-2 : ℝ)) m r'
          (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2))
          (revAge ν s ζ) *
        ‖pdCx k (φ (revAge ν s ζ))
          (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)‖ ^ 2
      = (clockA ν (revAge ν s ζ))⁻¹ * ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          deriv (fun r' => physW ν (ν ^ (-2 : ℝ)) m r' x) (revAge ν s ζ) *
            ‖pdCx k (φ (revAge ν s ζ)) x‖ ^ 2 :=
    UnforcedLeray.Short.IIIa.integral_cell_scale (ν ^ (-2 : ℝ)) (clockA ν (revAge ν s ζ)) ha
      (fun x => deriv (fun r' => physW ν (ν ^ (-2 : ℝ)) m r' x) (revAge ν s ζ) *
        ‖pdCx k (φ (revAge ν s ζ)) x‖ ^ 2)
  have h2 : ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (revAge ν s ζ))),
      deriv (fun r' => physW ν (ν ^ (-2 : ℝ)) m r'
          (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2))
          (revAge ν s ζ) *
        ‖pdCx k (φ (revAge ν s ζ))
          (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)‖ ^ 2
      = ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (revAge ν s ζ))),
          -((clockA ν (revAge ν s ζ))⁻¹) *
          ((dtW m (cellLen (ν ^ (-2 : ℝ)) (clockA ν (revAge ν s ζ))) (ν * clockA ν (revAge ν s ζ)) y +
              ν * clockA ν (revAge ν s ζ) / 2 *
                (y.1 * B0579.pd 0 (periodicWeight (-m) (cellLen (ν ^ (-2 : ℝ)) (clockA ν (revAge ν s ζ)))) y +
                  y.2 * B0579.pd 1 (periodicWeight (-m) (cellLen (ν ^ (-2 : ℝ)) (clockA ν (revAge ν s ζ)))) y)) *
            ‖pdCx k (movingPhi ν φ (revAge ν s ζ)) y‖ ^ 2) := by
    congr 1
    funext y
    exact key y
  rw [integral_const_mul] at h2
  rw [h2] at hcs
  apply mul_left_cancel₀ (inv_ne_zero ha')
  linear_combination hcs

end UnforcedLeray.Short.IIIa.AdjE1
