import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_5_3_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_9
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.WeightLogBounds

/-!
# `PartIII-a:T21/2/2/3/5/3/2`: the integral algebra on the moving cell (SP 3062)

Source of record: `the November 2 reference manuscript` (SP) lines 3044-3051 and
3062. With `ψ_k = xiRed_k - (β/2)∂_kΦ` and `w = p_d⁻¹`, the per-direction sum
`2β∫w|∂_kΦ|² + ∫(dtW + (β/2)y·∇w)|∂_kΦ|² + 2∫w Re(conj ∂_kΦ ψ_k)` equals the `k`-th summand of
`e1Rate`: `Re(conj ∂_kΦ · ψ_k) = Re(conj ∂_kΦ · xiRed_k) - (β/2)|∂_kΦ|²` pointwise.
Integrability: `dtW|∂_kΦ|²` and `(y·∇w)|∂_kΦ|²` are dominated by `C w|∂_kΦ|²`
(`WB m d 1 CW`, `dtW m d β = β dtW m d 1`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

/-- One direction `k` of the integral algebra on the cell of length `d`. -/
theorem rateAlg_k (m d β CW : ℝ) (V : ℝ × ℝ → Fin 2 → ℝ) (Φ χ : ℝ × ℝ → ℂ)
    (ψ : Fin 2 → ℝ × ℝ → ℂ) (k : Fin 2) (hd : 0 < d) (hreg : MovRegLow m d Φ)
    (hWB : WB m d 1 CW)
    (hint : IntegrableOn (fun y => periodicWeight (-m) d y *
      ((starRingEnd ℂ) (pdCx k Φ y) * ψ k y).re) (B0579.cell d))
    (hψ : ∀ y : ℝ × ℝ, ψ k y = xiRed β V Φ χ k y - (β : ℂ) / 2 * pdCx k Φ y) :
    (2 * β * (∫ y in B0579.cell d, periodicWeight (-m) d y * ‖pdCx k Φ y‖ ^ 2) +
      (∫ y in B0579.cell d,
        (dtW m d β y + β / 2 * (y.1 * B0579.pd 0 (periodicWeight (-m) d) y +
          y.2 * B0579.pd 1 (periodicWeight (-m) d) y)) * ‖pdCx k Φ y‖ ^ 2) +
      2 * ∫ y in B0579.cell d, periodicWeight (-m) d y *
        ((starRingEnd ℂ) (pdCx k Φ y) * ψ k y).re) =
      ((∫ y in B0579.cell d, dtW m d β y * ‖pdCx k Φ y‖ ^ 2) +
        2 * (∫ y in B0579.cell d,
          periodicWeight (-m) d y * ((starRingEnd ℂ) (pdCx k Φ y) * xiRed β V Φ χ k y).re) +
        β / 2 * ∫ y in B0579.cell d,
          (2 * periodicWeight (-m) d y + (y.1 * B0579.pd 0 (periodicWeight (-m) d) y +
            y.2 * B0579.pd 1 (periodicWeight (-m) d) y)) * ‖pdCx k Φ y‖ ^ 2) := by
  have hw1 : ContDiff ℝ 1 (periodicWeight (-m) d) := (pw_contDiff (-m) d).of_le (by simp)
  have hR_cont : Continuous (fun y : ℝ × ℝ => y.1 * B0579.pd 0 (periodicWeight (-m) d) y +
      y.2 * B0579.pd 1 (periodicWeight (-m) d) y) :=
    (continuous_fst.mul (pdContinuous hw1 0)).add (continuous_snd.mul (pdContinuous hw1 1))
  have hU : Continuous (fun y => ‖pdCx k Φ y‖ ^ 2) :=
    ((pdCx_cont hreg.smooth k).norm).pow 2
  have hA : IntegrableOn (fun y => periodicWeight (-m) d y * ‖pdCx k Φ y‖ ^ 2)
      (B0579.cell d) := hreg.int1 k
  have hS : MeasurableSet (B0579.cell d) := B0579.measurableSet_cell d
  -- `dtW|∂_kΦ|²` is integrable: `|dtW m d β| ≤ |β| (CW/2) w`
  have hdt : IntegrableOn (fun y => dtW m d β y * ‖pdCx k Φ y‖ ^ 2) (B0579.cell d) := by
    have hc : Continuous (fun y => dtW m d β y * ‖pdCx k Φ y‖ ^ 2) :=
      (dtW_cont m d β hd.ne').mul hU
    refine (bd (c := |β| * (CW / 2)) hS hA hc ?_).1
    intro y hy
    have hdb : dtW m d β y = β * dtW m d 1 y := by unfold dtW; ring
    have h1 := hWB.dt y hy
    have hn : 0 ≤ ‖pdCx k Φ y‖ ^ 2 := by positivity
    rw [abs_mul, abs_of_nonneg hn, hdb, abs_mul]
    have key : |β| * |dtW m d 1 y| ≤ |β| * (CW / 2 * periodicWeight (-m) d y) :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg β)
    calc |β| * |dtW m d 1 y| * ‖pdCx k Φ y‖ ^ 2
        ≤ |β| * (CW / 2 * periodicWeight (-m) d y) * ‖pdCx k Φ y‖ ^ 2 :=
          mul_le_mul_of_nonneg_right key hn
      _ = |β| * (CW / 2) * (periodicWeight (-m) d y * ‖pdCx k Φ y‖ ^ 2) := by ring
  -- `(y·∇w)|∂_kΦ|²` is integrable: `|y·∇w| ≤ CW w`
  have hRint : IntegrableOn (fun y => (y.1 * B0579.pd 0 (periodicWeight (-m) d) y +
      y.2 * B0579.pd 1 (periodicWeight (-m) d) y) * ‖pdCx k Φ y‖ ^ 2) (B0579.cell d) := by
    have hc : Continuous (fun y => (y.1 * B0579.pd 0 (periodicWeight (-m) d) y +
        y.2 * B0579.pd 1 (periodicWeight (-m) d) y) * ‖pdCx k Φ y‖ ^ 2) :=
      hR_cont.mul hU
    refine (bd (c := CW) hS hA hc ?_).1
    intro y hy
    have hn : 0 ≤ ‖pdCx k Φ y‖ ^ 2 := by positivity
    rw [abs_mul, abs_of_nonneg hn]
    calc |y.1 * B0579.pd 0 (periodicWeight (-m) d) y +
          y.2 * B0579.pd 1 (periodicWeight (-m) d) y| * ‖pdCx k Φ y‖ ^ 2
        ≤ CW * periodicWeight (-m) d y * ‖pdCx k Φ y‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hWB.dil y hy) hn
      _ = CW * (periodicWeight (-m) d y * ‖pdCx k Φ y‖ ^ 2) := by ring
  -- pointwise splits
  have hsp1 : (fun y : ℝ × ℝ => (dtW m d β y + β / 2 * (y.1 * B0579.pd 0 (periodicWeight (-m) d) y +
      y.2 * B0579.pd 1 (periodicWeight (-m) d) y)) * ‖pdCx k Φ y‖ ^ 2) =
      fun y => dtW m d β y * ‖pdCx k Φ y‖ ^ 2 + β / 2 * ((y.1 * B0579.pd 0 (periodicWeight (-m) d) y +
        y.2 * B0579.pd 1 (periodicWeight (-m) d) y) * ‖pdCx k Φ y‖ ^ 2) :=
    funext fun y => by ring
  have hsp2 : (fun y : ℝ × ℝ => (2 * periodicWeight (-m) d y + (y.1 * B0579.pd 0
      (periodicWeight (-m) d) y + y.2 * B0579.pd 1 (periodicWeight (-m) d) y)) *
      ‖pdCx k Φ y‖ ^ 2) =
      fun y => 2 * (periodicWeight (-m) d y * ‖pdCx k Φ y‖ ^ 2) +
        (y.1 * B0579.pd 0 (periodicWeight (-m) d) y +
          y.2 * B0579.pd 1 (periodicWeight (-m) d) y) * ‖pdCx k Φ y‖ ^ 2 :=
    funext fun y => by ring
  have hxi : (fun y => periodicWeight (-m) d y *
      ((starRingEnd ℂ) (pdCx k Φ y) * xiRed β V Φ χ k y).re) =
      fun y => periodicWeight (-m) d y * ((starRingEnd ℂ) (pdCx k Φ y) * ψ k y).re +
        β / 2 * (periodicWeight (-m) d y * ‖pdCx k Φ y‖ ^ 2) := by
    funext y
    have hx : xiRed β V Φ χ k y = ψ k y + (β : ℂ) / 2 * pdCx k Φ y := by
      rw [hψ y]; ring
    have e : (starRingEnd ℂ) (pdCx k Φ y) * (ψ k y + (β : ℂ) / 2 * pdCx k Φ y) =
        (starRingEnd ℂ) (pdCx k Φ y) * ψ k y +
          (((β / 2 : ℝ)) : ℂ) * ((starRingEnd ℂ) (pdCx k Φ y) * pdCx k Φ y) := by
      push_cast; ring
    rw [hx, e, Complex.add_re, Complex.re_ofReal_mul, re_conj_self]
    ring
  -- the integrals
  have hJ : (∫ y in B0579.cell d,
      (dtW m d β y + β / 2 * (y.1 * B0579.pd 0 (periodicWeight (-m) d) y +
        y.2 * B0579.pd 1 (periodicWeight (-m) d) y)) * ‖pdCx k Φ y‖ ^ 2) =
      (∫ y in B0579.cell d, dtW m d β y * ‖pdCx k Φ y‖ ^ 2) +
        β / 2 * ∫ y in B0579.cell d, (y.1 * B0579.pd 0 (periodicWeight (-m) d) y +
          y.2 * B0579.pd 1 (periodicWeight (-m) d) y) * ‖pdCx k Φ y‖ ^ 2 := by
    rw [hsp1, integral_add hdt (hRint.const_mul _), integral_const_mul]
  have hL : (∫ y in B0579.cell d, (2 * periodicWeight (-m) d y + (y.1 * B0579.pd 0
      (periodicWeight (-m) d) y + y.2 * B0579.pd 1 (periodicWeight (-m) d) y)) *
      ‖pdCx k Φ y‖ ^ 2) =
      2 * (∫ y in B0579.cell d, periodicWeight (-m) d y * ‖pdCx k Φ y‖ ^ 2) +
        ∫ y in B0579.cell d, (y.1 * B0579.pd 0 (periodicWeight (-m) d) y +
          y.2 * B0579.pd 1 (periodicWeight (-m) d) y) * ‖pdCx k Φ y‖ ^ 2 := by
    rw [hsp2, integral_add (hA.const_mul 2) hRint, integral_const_mul]
  have hD : (∫ y in B0579.cell d, periodicWeight (-m) d y *
      ((starRingEnd ℂ) (pdCx k Φ y) * xiRed β V Φ χ k y).re) =
      (∫ y in B0579.cell d, periodicWeight (-m) d y *
        ((starRingEnd ℂ) (pdCx k Φ y) * ψ k y).re) +
        β / 2 * ∫ y in B0579.cell d, periodicWeight (-m) d y * ‖pdCx k Φ y‖ ^ 2 := by
    rw [hxi, integral_add hint (hA.const_mul _), integral_const_mul]
  rw [hJ, hL]
  linear_combination (-2 : ℝ) * hD

/-- **Leaf (integral algebra on the moving cell)** (SP 3062): see `E1RateAlg`. -/
theorem e1RateAlg (m : ℝ) : UnforcedLeray.Short.IIIa.AdjE1.E1RateAlg m := by
  intro d β V Φ χ ψ hd hreg hint hψ
  obtain ⟨CW, -, hW⟩ := wb_of_hW periodicWeightLogBounds m
  have hWB : WB m d 1 CW := hW d 1 hd one_pos le_rfl
  unfold e1Rate
  exact Finset.sum_congr rfl fun k _ =>
    rateAlg_k m d β CW V Φ χ ψ k hd hreg hWB (hint k) (hψ k)

end UnforcedLeray.Short.IIIa.AdjE1
